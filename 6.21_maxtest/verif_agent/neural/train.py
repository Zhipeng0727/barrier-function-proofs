"""
train.py — gradient training of a neural Lyapunov certificate. The learner side:
minimise a hinge surrogate of the decrease condition (and positivity for the plain
net) over sampled points + accumulated CEGIS counterexamples. f is lambdified to
torch so ∇V·f flows through autograd.
"""
from __future__ import annotations

import math

import sympy as sp
import torch

from verif_agent.neural.cert import make_cert

_TMOD = {
    "sin": torch.sin, "cos": torch.cos, "tan": torch.tan, "exp": torch.exp,
    "log": torch.log, "sqrt": torch.sqrt, "tanh": torch.tanh, "sinh": torch.sinh,
    "cosh": torch.cosh, "atan": torch.atan, "asin": torch.asin, "acos": torch.acos,
    "asinh": torch.asinh, "acosh": torch.acosh, "atanh": torch.atanh, "Abs": torch.abs,
    "pi": math.pi,
}


def lambdify_f(f_expr, state_vars):
    xs = [sp.Symbol(v, real=True) for v in state_vars]
    loc = {v: s for v, s in zip(state_vars, xs)}
    lams = []
    for fe in f_expr:
        e = sp.sympify(str(fe).replace("^", "**"), locals=loc)
        lams.append(sp.lambdify(xs, e, modules=[_TMOD]))

    def f(x):  # x: (N, dim) -> (N, dim)
        cols = [x[:, i] for i in range(len(state_vars))]
        out = []
        for lam in lams:
            v = lam(*cols)
            if not torch.is_tensor(v):
                v = torch.full_like(x[:, 0], float(v))
            out.append(v)
        return torch.stack(out, dim=-1)
    return f


def _sample(bounds, n, seed):
    g = torch.Generator().manual_seed(seed)
    lo = torch.tensor([b[0] for b in bounds], dtype=torch.float64)
    hi = torch.tensor([b[1] for b in bounds], dtype=torch.float64)
    u = torch.rand(n, len(bounds), generator=g, dtype=torch.float64)
    return lo + (hi - lo) * u


def train(system, cfg, extra_points=None, seed=0):
    """Train a Lyapunov net. Returns (cert, info). cfg keys: kind,width,alpha,
    margin,lr,iters,n_samples,pos_weight."""
    state_vars = system["state_vars"]
    dim = len(state_vars)
    x_star = system.get("equilibrium") or [0.0] * dim
    bounds = [tuple(map(float, b)) for b in
              (system.get("X_bounds") or [(-3, 3)] * dim)]
    f = lambdify_f(system["f_expr"], state_vars)
    cert = make_cert(cfg["kind"], dim, cfg["width"], x_star, cfg["alpha"], seed=seed)

    pts = _sample(bounds, cfg["n_samples"], seed)
    if extra_points is not None and len(extra_points):
        ex = torch.tensor(extra_points, dtype=torch.float64)
        pts = torch.cat([pts, ex.repeat(cfg.get("cex_repeat", 20), 1)], dim=0)

    opt = torch.optim.Adam(cert.parameters(), lr=cfg["lr"])
    xstar_t = torch.tensor(x_star, dtype=torch.float64)
    margin, pos_w = cfg["margin"], cfg.get("pos_weight", 1.0)
    hist = []
    for it in range(cfg["iters"]):
        x = pts.clone().requires_grad_(True)
        V = cert(x)
        gradV = torch.autograd.grad(V.sum(), x, create_graph=True)[0]
        Vdot = (gradV * f(x)).sum(dim=-1)
        dist2 = ((x - xstar_t) ** 2).sum(dim=-1)
        loss = torch.relu(Vdot + margin * dist2).mean()
        if cfg["kind"] == "plain":          # positivity must be learned too
            loss = loss + pos_w * torch.relu(-V + 1e-2 * dist2).mean()
        opt.zero_grad()
        loss.backward()
        opt.step()
        if it % max(1, cfg["iters"] // 5) == 0 or it == cfg["iters"] - 1:
            hist.append((it, float(loss)))
    return cert, {"loss_hist": hist, "final_loss": hist[-1][1] if hist else None}
