"""
cegis.py — the learner-verifier-falsifier loop for neural certificates.

round: train NN  →  sound-verify (reuse interval/dReal on the to_sympy expr)
  - proved  → done (sound neural certificate)
  - refuted → the verifier's counterexample goes back into the training set
  - unknown → run a PGD falsifier on the trained net; a found violation is added
              and we retrain; if the falsifier is clean too, the blocker is verifier
              tightness (not the learner) → stop as 'unknown-verifier-limited'.
"""
from __future__ import annotations

import time

import torch

from verif_agent.backend_base import get_backend
from verif_agent.neural.train import train, lambdify_f, _sample


def falsify(system, cert, n_starts=300, steps=60, lr=0.05, tol=1e-4, seed=1, topk=3):
    """PGD ascent to maximise V̇ over the box; return worst violating points."""
    state_vars = system["state_vars"]
    bounds = [tuple(map(float, b)) for b in
              (system.get("X_bounds") or [(-3, 3)] * len(state_vars))]
    f = lambdify_f(system["f_expr"], state_vars)
    lo = torch.tensor([b[0] for b in bounds], dtype=torch.float64)
    hi = torch.tensor([b[1] for b in bounds], dtype=torch.float64)
    x = _sample(bounds, n_starts, seed).clone()
    for _ in range(steps):
        x = x.detach().requires_grad_(True)
        V = cert(x)
        gradV = torch.autograd.grad(V.sum(), x, create_graph=True)[0]
        Vdot = (gradV * f(x)).sum(dim=-1)
        g = torch.autograd.grad(Vdot.sum(), x)[0]
        with torch.no_grad():
            x = torch.clamp(x + lr * g, lo, hi)
    # final Vdot
    x = x.detach().requires_grad_(True)
    V = cert(x)
    gradV = torch.autograd.grad(V.sum(), x, create_graph=True)[0]
    Vdot = (gradV * f(x)).sum(dim=-1).detach()
    viol = (Vdot > tol).nonzero().squeeze(-1)
    if viol.numel() == 0:
        return []
    order = Vdot[viol].argsort(descending=True)
    return [x[viol[i]].detach().tolist() for i in order[:topk]]


def cegis(system, cfg, max_rounds=6, verifier="interval", seed=0, verbose=False):
    state_vars = system["state_vars"]
    extra = []
    t0 = time.time()
    last = None
    for rnd in range(max_rounds):
        cert, info = train(system, cfg, extra_points=extra or None, seed=seed + rnd)
        expr = cert.to_sympy(state_vars)
        sysd = dict(system)
        sysd["cert_gt"] = expr
        backend = get_backend(verifier)
        ok, reason = backend.applicable(sysd, expr)
        if not ok:
            return {"solved": False, "rounds": rnd, "blocker": f"verifier n/a: {reason}",
                    "time": time.time() - t0, "verifier": verifier}
        r = backend.verify(sysd, expr)
        last = r
        if verbose:
            print(f"    round {rnd+1}: loss={info['final_loss']:.1e} "
                  f"{verifier}->{r.status} ({r.elapsed_s:.1f}s)")
        if r.status == "proved" and r.sound:
            return {"solved": True, "rounds": rnd + 1, "cert": expr, "verifier": verifier,
                    "final_loss": info["final_loss"], "width": cfg["width"],
                    "cert_size": expr.count("tanh"), "time": time.time() - t0}
        # get a counterexample: verifier's, else PGD falsifier
        ce_pts = []
        if r.counterexample:
            ce_pts = [[r.counterexample[v] for v in state_vars]]
        else:
            ce_pts = falsify(system, cert, seed=seed + 100 + rnd)
        if not ce_pts:
            return {"solved": False, "rounds": rnd + 1, "verifier": verifier,
                    "blocker": "verifier-limited (falsifier found no violation)",
                    "final_loss": info["final_loss"], "time": time.time() - t0,
                    "conditions": (last.detail or {}).get("conditions")}
        extra.extend(ce_pts)
    return {"solved": False, "rounds": max_rounds, "verifier": verifier,
            "blocker": "max rounds", "time": time.time() - t0,
            "conditions": (last.detail or {}).get("conditions") if last else None}
