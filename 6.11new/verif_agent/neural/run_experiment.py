#!/usr/bin/env python3
"""
run_experiment.py — the neural-certificate experiment.

  A0 (symbolic baseline): the simplest symbolic ansatz V=‖x-x*‖² (a degree-2
      polynomial) verified by the sound stack — the "no neural needed" control.
  A1 (neural-CEGIS):      trained tanh-net certificate, sound-verified.
  H1 (make-or-break):     EXCLUSIVE WINS = systems A1 certifies that A0 cannot.

Then a CONTROLLED sweep over agent-structure knobs, and GLM-in-the-loop tuning,
to find the best structure. Usage:
  python3 -m verif_agent.neural.run_experiment --n 8 --tune 3
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

from dataset_loader import load_dataset                       # noqa: E402
from verif_agent import verify                                # noqa: E402
import verif_agent.backends                                    # noqa: E402,F401
from verif_agent.neural.cegis import cegis                     # noqa: E402
from verif_agent.neural.sweep import controlled_variants, run_sweep, run_config, score  # noqa: E402
from verif_agent.neural.glm_tuner import glm_tune              # noqa: E402

MANIFEST = "/Users/zhipeng/Desktop/paper4/data/lean4_core200_diverse_manifest_v5.json"


def hard_slice(n):
    entries, _ = load_dataset(MANIFEST, call_fn=None, limit=200)
    hard = [(e, s) for e, s in entries
            if s.get("task_type") == "lyapunov" and not s.get("discrete")
            and len(s["state_vars"]) <= 3 and s.get("equilibrium") is not None
            and s.get("cert_gt") and s.get("meta", {}).get("verif_cond_class") == "transcendental"]
    return hard[:n]


def symbolic_baseline(systems):
    """A0: try the simplest polynomial ansatz V = ||x - x*||^2, sound-verify."""
    solved = set()
    for eid, s in systems:
        xstar = s.get("equilibrium") or [0.0] * len(s["state_vars"])
        cert = " + ".join(f"({v} - ({c}))**2" for v, c in zip(s["state_vars"], xstar))
        sysd = dict(s)
        sysd["psd_ok"] = False
        res = verify(sysd, cert)
        if res.status == "proved" and res.sound:
            solved.add(eid)
    return solved


def neural_arm(systems, cfg):
    vr = cfg.get("verifier", "interval")
    mr = cfg.get("max_rounds", 4)
    cc = {k: cfg[k] for k in ("kind", "width", "alpha", "margin", "lr", "iters", "n_samples")}
    solved, detail = set(), []
    for eid, s in systems:
        r = cegis(s, cc, max_rounds=mr, verifier=vr)
        if r["solved"]:
            solved.add(eid)
        detail.append({"id": eid, "solved": r["solved"], "rounds": r.get("rounds"),
                       "time": round(r.get("time", 0), 2)})
    return solved, detail


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=8)
    ap.add_argument("--tune", type=int, default=3)
    ap.add_argument("--out", default=os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                                  "neural_experiment.json"))
    a = ap.parse_args()
    systems = hard_slice(a.n)
    ids = [e for e, _ in systems]
    print(f"HARD slice (transcendental lyapunov, dim<=3): {len(systems)} systems")
    print(f"  {ids}\n")

    t0 = time.time()
    print("A0 symbolic baseline  V=||x-x*||^2 (sound):")
    a0 = symbolic_baseline(systems)
    print(f"  solved {len(a0)}/{len(systems)}: {sorted(a0)}\n")

    print("Controlled sweep (one knob changed per variant):")
    variants = controlled_variants()
    sweep = run_sweep(systems, variants,
                      log_path=a.out.replace(".json", "_sweep.json"))
    best_variant = max(sweep.items(), key=lambda kv: score(kv[1]))
    print(f"  best variant: {best_variant[0]}  ({best_variant[1]['solved']}/{len(systems)})\n")

    print(f"GLM-in-the-loop tuning ({a.tune} rounds):")
    history, best = glm_tune(systems, rounds=a.tune,
                             log_path=a.out.replace(".json", "_tune.json"))
    best_cfg = best["cfg"]
    print(f"  best tuned config: {best['name']}  "
          f"({best['result']['solved']}/{len(systems)})\n")

    print("A1 neural-CEGIS with best config:")
    a1, a1_detail = neural_arm(systems, best_cfg)
    print(f"  solved {len(a1)}/{len(systems)}: {sorted(a1)}")

    exclusive = a1 - a0
    print(f"\n==== H1: EXCLUSIVE WINS (neural solves, symbolic-poly cannot) ====")
    print(f"  A0 symbolic-poly : {len(a0)}/{len(systems)}")
    print(f"  A1 neural-CEGIS  : {len(a1)}/{len(systems)}")
    print(f"  exclusive wins   : {len(exclusive)}  -> {sorted(exclusive)}")
    print(f"  total wall       : {time.time()-t0:.1f}s")

    payload = {"slice": ids, "A0_solved": sorted(a0), "A1_solved": sorted(a1),
               "exclusive_wins": sorted(exclusive), "best_cfg": best_cfg,
               "sweep": {k: {"solved": v["solved"], "avg_rounds": v["avg_rounds"],
                             "time": v["time"], "cfg": v["cfg"]} for k, v in sweep.items()},
               "tune_history": [{"name": h["name"], "cfg": h["cfg"],
                                 "solved": h["result"]["solved"],
                                 "rationale": h.get("rationale")} for h in history],
               "a1_detail": a1_detail}
    with open(a.out, "w", encoding="utf-8") as f:
        json.dump(payload, f, ensure_ascii=False, indent=1)
    print(f"\nreport -> {a.out}")


if __name__ == "__main__":
    main()
