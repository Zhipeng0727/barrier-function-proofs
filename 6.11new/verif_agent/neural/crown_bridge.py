#!/usr/bin/env python3
"""
crown_bridge.py — base-env side of the CROWN verifier. Trains a structural neural
Lyapunov on a system, exports (net weights + polynomial f as monomials + domain)
to JSON, and runs crown_verify.py in the prover-mps py3.11 env (which has
auto_LiRPA). Returns the CROWN decrease verdict. Polynomial dynamics only.
"""
from __future__ import annotations

import json
import os
import subprocess
import sys

import sympy as sp

_PARENT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
if _PARENT not in sys.path:
    sys.path.insert(0, _PARENT)

from verif_agent.neural.train import train          # noqa: E402
from verif_agent.features import _parse             # noqa: E402

PROVER_PY = "/Users/zhipeng/.conda/envs/prover-mps/bin/python"
CROWN_SCRIPT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "crown_verify.py")


def f_to_monomials(f_expr, state_vars):
    xs = [sp.Symbol(v, real=True) for v in state_vars]
    mono = []
    for fe in f_expr:
        e = _parse(fe, state_vars)
        p = sp.Poly(sp.expand(e), *xs)        # raises if not polynomial
        terms = [[float(c), [int(d) for d in exps]] for exps, c in p.terms()]
        mono.append(terms)
    return mono


def crown_verify_system(system, cfg, seed=0, inner_radius=None, max_boxes=4000):
    sv = system["state_vars"]
    try:
        fmono = f_to_monomials(system["f_expr"], sv)
    except Exception as e:
        return {"status": "unsupported", "reason": f"non-polynomial f: {e}"}
    cert, info = train(system, cfg, seed=seed)
    W1 = cert.lin.weight.detach().cpu().numpy().tolist()
    b1 = cert.lin.bias.detach().cpu().numpy().tolist()
    xstar = [float(c) for c in (system.get("equilibrium") or [0.0] * len(sv))]
    spec = {
        "W1": W1, "b1": b1, "xstar": xstar, "alpha": float(cert.alpha),
        "fmono": fmono,
        "bounds": [list(map(float, b)) for b in system["X_bounds"]],
        "inner_radius": float(inner_radius if inner_radius is not None
                              else system.get("inner_radius", 0.0)),
        "max_boxes": max_boxes,
    }
    path = "/tmp/crown_spec.json"
    with open(path, "w") as f:
        json.dump(spec, f)
    out = subprocess.run([PROVER_PY, CROWN_SCRIPT, path],
                         capture_output=True, text=True, timeout=600)
    line = [l for l in out.stdout.strip().splitlines() if l.startswith("{")]
    res = json.loads(line[-1]) if line else {"status": "error",
                                             "err": out.stderr[-500:]}
    res["final_loss"] = info.get("final_loss")
    return res


if __name__ == "__main__":
    from verif_agent.neural.benchmarks_real import REAL_SYSTEMS
    cfg = {"kind": "structural", "width": 6, "alpha": 0.1, "margin": 0.1,
           "lr": 0.02, "iters": 700, "n_samples": 1500}
    keys = sys.argv[1:] or ["fossil_poly3", "fossil_poly4", "fossil_nonpoly1"]
    for k in keys:
        s = dict(REAL_SYSTEMS[k])
        r = crown_verify_system(s, cfg, seed=0, inner_radius=0.5, max_boxes=6000)
        print(f"{k:18} dom{s['X_bounds'][0]}  CROWN decrease -> {r.get('status')}  "
              f"({r.get('reason') or r.get('worst_ub')}, boxes={r.get('processed')})")
