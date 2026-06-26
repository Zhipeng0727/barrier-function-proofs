#!/usr/bin/env python3
"""
run_real2.py — IMPROVED agent flow on the 10 real systems. Controlled variables vs
run_real.py:
  (1) ball-exclusion in the Lyapunov decrease (annulus): V̇≤0 verified on domain
      minus an inner ball (FOSSIL itself uses a Torus inner radius) — kills the
      near-origin straddle that caused 'verifier-limited'.
  (2) fair A0: identity-seeded quadratic (the natural V=‖z‖² is always a candidate).
  (3) controlled outer radius (default 3): both arms on the SAME domain, since z3
      (A0) is exact at any radius but interval (A1) needs a moderate box.
A0 = quadratic (z3 exact, or interval if dynamics transcendental); A1 = neural tanh.
"""
from __future__ import annotations

import argparse
import json
import os
import sys

_PARENT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
if _PARENT not in sys.path:
    sys.path.insert(0, _PARENT)

from verif_agent.neural.benchmarks_real import REAL_SYSTEMS    # noqa: E402
from verif_agent.neural.cegis import cegis                     # noqa: E402
from verif_agent.features import extract_features              # noqa: E402

CFG_QUAD = {"kind": "quad", "width": 0, "alpha": 1e-3, "margin": 1e-3,
            "lr": 0.05, "iters": 600, "n_samples": 1200}
CFG_NEURAL = {"kind": "structural", "width": 6, "alpha": 0.1, "margin": 0.1,
              "lr": 0.02, "iters": 700, "n_samples": 1200}


def with_domain(system, outer, inner):
    s = dict(system)
    orthant = system["X_bounds"][0][0] > 0   # positive-orthant systems keep lo>0
    s["X_bounds"] = [((0.01, outer) if orthant else (-outer, outer))
                     for _ in system["state_vars"]]
    s["inner_radius"] = inner
    return s


def a0_verifier(system):
    return "z3" if extract_features(system, cert=None)["decidable_real"] else "interval"


def best(system, cfg, verifier, seeds, max_rounds):
    acc = 0.0
    for sd in seeds:
        r = cegis(system, cfg, max_rounds=max_rounds, verifier=verifier, seed=sd)
        acc += r.get("time", 0.0)
        if r.get("solved"):
            r["time"] = acc
            return r
        last = r
    last["time"] = acc
    return last


def run(keys, outer, inner, seeds, out_path):
    rows = []
    for k in keys:
        s = with_domain(REAL_SYSTEMS[k], outer, inner)
        dim = len(s["state_vars"])
        a0 = best(s, CFG_QUAD, a0_verifier(s), seeds, 4)
        a1 = best(s, CFG_NEURAL, "interval", seeds, 5)
        rows.append({"id": k, "dim": dim, "A0": bool(a0.get("solved")),
                     "A0_blk": a0.get("blocker"), "A1": bool(a1.get("solved")),
                     "A1_blk": a1.get("blocker"), "A1_cert": (a1.get("cert") or "")[:70]})
        print(f"{k:20} dim{dim}  A0(quad)={str(a0.get('solved')):5} "
              f"A1(neural)={str(a1.get('solved')):5}  A1blk={a1.get('blocker') or 'ok'}")
    a0n = sum(r["A0"] for r in rows)
    a1n = sum(r["A1"] for r in rows)
    excl = [r["id"] for r in rows if r["A1"] and not r["A0"]]
    rev = [r["id"] for r in rows if r["A0"] and not r["A1"]]
    print("\n" + "=" * 64)
    print(f"IMPROVED flow on REAL systems  (outer={outer}, inner_ball={inner}), n={len(rows)}")
    print(f"  A0 quadratic : {a0n}/{len(rows)}")
    print(f"  A1 neural    : {a1n}/{len(rows)}")
    print(f"  EXCLUSIVE neural wins : {len(excl)} -> {excl}")
    print(f"  reverse (quad only)   : {len(rev)} -> {rev}")
    with open(out_path, "w") as f:
        json.dump({"outer": outer, "inner": inner, "rows": rows,
                   "A0": a0n, "A1": a1n, "exclusive": excl, "reverse": rev}, f, indent=1)
    print(f"  -> {out_path}")


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--keys", nargs="*", default=None)
    ap.add_argument("--outer", type=float, default=3.0)
    ap.add_argument("--inner", type=float, default=0.5)
    ap.add_argument("--seeds", nargs="*", type=int, default=[0, 1, 2])
    ap.add_argument("--out", default=os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                                  "real_improved_result.json"))
    a = ap.parse_args()
    keys = a.keys or list(REAL_SYSTEMS.keys())
    run(keys, a.outer, a.inner, a.seeds, a.out)
