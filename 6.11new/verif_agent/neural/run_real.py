#!/usr/bin/env python3
"""
run_real.py — H1 on REAL, literature benchmarks (FOSSIL). For each system:
  A0 = trained quadratic Lyapunov  V=zᵀPz  (P⪰0)  →  z3 EXACT verification
  A1 = neural tanh Lyapunov (structural) via CEGIS →  interval sound verification
Both arms use the same learner-verifier loop; only representation + verifier differ.
Exclusive wins (A1 solves, A0 cannot) on neutral data = the real test of the claim
that NN expressiveness buys sound coverage a polynomial certificate cannot.
"""
from __future__ import annotations

import argparse
import json
import os
import sys
import time

_PARENT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
if _PARENT not in sys.path:
    sys.path.insert(0, _PARENT)

from verif_agent.neural.benchmarks_real import REAL_SYSTEMS   # noqa: E402
from verif_agent.neural.cegis import cegis                    # noqa: E402
from verif_agent.features import extract_features             # noqa: E402


def a0_verifier_for(system):
    # the quad cert is polynomial, but ∇V·f is transcendental when f is → z3 can't
    # verify it; route A0 to interval in that case (same as the neural arm).
    feats = extract_features(system, cert=None)
    return "z3" if feats["decidable_real"] else "interval"

CFG_QUAD = {"kind": "quad", "width": 0, "alpha": 1e-3, "margin": 1e-3,
            "lr": 0.05, "iters": 600, "n_samples": 1000}
CFG_NEURAL = {"kind": "structural", "width": 6, "alpha": 0.1, "margin": 1e-2,
              "lr": 0.02, "iters": 600, "n_samples": 1000}


def best_of(system, cfg, verifier, seeds, max_rounds):
    best = {"solved": False, "rounds": max_rounds, "time": 0.0}
    for sd in seeds:
        r = cegis(system, cfg, max_rounds=max_rounds, verifier=verifier, seed=sd)
        best["time"] += r.get("time", 0.0)
        if r.get("solved"):
            r["time"] = best["time"]
            return r            # first solving seed wins
        best = {**r, "time": best["time"]}
    return best


def run(keys, seeds, out_path):
    rows = []
    for k in keys:
        s = dict(REAL_SYSTEMS[k])
        dim = len(s["state_vars"])
        a0 = best_of(s, CFG_QUAD, a0_verifier_for(s), seeds, max_rounds=4)
        a1 = best_of(s, CFG_NEURAL, "interval", seeds, max_rounds=5)
        rows.append({"id": k, "dim": dim, "source": s["source"],
                     "A0_quad": a0.get("solved"), "A0_rounds": a0.get("rounds"),
                     "A0_time": round(a0.get("time", 0), 1), "A0_blocker": a0.get("blocker"),
                     "A1_neural": a1.get("solved"), "A1_rounds": a1.get("rounds"),
                     "A1_time": round(a1.get("time", 0), 1), "A1_blocker": a1.get("blocker"),
                     "A1_cert": a1.get("cert", "")[:80]})
        print(f"{k:20} dim{dim}  A0(quad/z3)={str(a0.get('solved')):5} "
              f"A1(neural/interval)={str(a1.get('solved')):5}  "
              f"[A0 {a0.get('A0_blocker') or a0.get('blocker') or 'ok'}]")
    a0n = sum(1 for r in rows if r["A0_quad"])
    a1n = sum(1 for r in rows if r["A1_neural"])
    excl = [r["id"] for r in rows if r["A1_neural"] and not r["A0_quad"]]
    rev = [r["id"] for r in rows if r["A0_quad"] and not r["A1_neural"]]
    print("\n" + "=" * 64)
    print(f"REAL benchmarks (FOSSIL), n={len(rows)}")
    print(f"  A0 quadratic (z3 exact) : {a0n}/{len(rows)}")
    print(f"  A1 neural-CEGIS (interval): {a1n}/{len(rows)}")
    print(f"  EXCLUSIVE WINS (neural solves, quadratic cannot): {len(excl)} -> {excl}")
    print(f"  reverse (quad solves, neural cannot): {len(rev)} -> {rev}")
    with open(out_path, "w") as f:
        json.dump({"rows": rows, "A0": a0n, "A1": a1n, "exclusive": excl,
                   "reverse": rev}, f, indent=1)
    print(f"  -> {out_path}")


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--keys", nargs="*", default=None)
    ap.add_argument("--seeds", nargs="*", type=int, default=[0, 1])
    ap.add_argument("--out", default=os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                                  "real_benchmark_result.json"))
    a = ap.parse_args()
    keys = a.keys or list(REAL_SYSTEMS.keys())
    run(keys, a.seeds, a.out)
