"""
sweep.py — controlled-variable comparison of neural-CEGIS agent variants. Start
from one BASE config and change EXACTLY ONE structural knob per variant, so any
delta in solved-count / rounds / time is attributable to that knob. This is the
"control variables, optimize the agent structure" engine; the GLM tuner
(glm_tuner.py) drives it.

Knobs (the structural variables):
  kind     : 'structural' (PD by construction) vs 'plain' (PD learned)
  width    : hidden units — expressiveness vs verifiability
  margin   : decrease margin trained for (V̇ ≤ -margin·‖x-x*‖²)
  iters    : training iterations
  lr       : learning rate
  verifier : 'interval' vs 'dreal'
  max_rounds: CEGIS budget
"""
from __future__ import annotations

import json

from verif_agent.neural.cegis import cegis

BASE = {"kind": "structural", "width": 5, "alpha": 0.1, "margin": 1e-3,
        "lr": 0.02, "iters": 400, "n_samples": 500,
        "verifier": "interval", "max_rounds": 4}


def controlled_variants(base=BASE):
    """BASE + one-knob perturbations (the controlled set)."""
    V = {"base": dict(base)}
    V["plain_positivity"] = {**base, "kind": "plain"}
    V["width3"] = {**base, "width": 3}
    V["width8"] = {**base, "width": 8}
    V["margin0"] = {**base, "margin": 0.0}
    V["margin1e-2"] = {**base, "margin": 1e-2}
    V["verifier_dreal"] = {**base, "verifier": "dreal", "max_rounds": 2}
    V["iters800"] = {**base, "iters": 800}
    return V


def run_config(systems, cfg, seed=0):
    vr = cfg.get("verifier", "interval")
    mr = cfg.get("max_rounds", 4)
    cegis_cfg = {k: cfg[k] for k in
                 ("kind", "width", "alpha", "margin", "lr", "iters", "n_samples")}
    per = []
    for eid, s in systems:
        r = cegis(s, cegis_cfg, max_rounds=mr, verifier=vr, seed=seed)
        per.append({"id": eid, "solved": r["solved"], "rounds": r.get("rounds"),
                    "time": round(r.get("time", 0), 2), "blocker": r.get("blocker")})
    solved = sum(p["solved"] for p in per)
    tot_time = round(sum(p["time"] for p in per), 1)
    avg_rounds = round(sum(p["rounds"] or 0 for p in per) / max(1, len(per)), 2)
    return {"solved": solved, "n": len(per), "time": tot_time,
            "avg_rounds": avg_rounds, "per": per}


def run_sweep(systems, configs, seed=0, log_path=None):
    results = {}
    for name, cfg in configs.items():
        res = run_config(systems, cfg, seed=seed)
        results[name] = {"cfg": cfg, **res}
        print(f"  [{name:16}] solved {res['solved']}/{res['n']}  "
              f"avg_rounds {res['avg_rounds']}  time {res['time']}s")
        if log_path:
            with open(log_path, "w", encoding="utf-8") as f:
                json.dump(results, f, ensure_ascii=False, indent=1)
    return results


def score(res):
    """Rank: more solved first, then fewer rounds, then less time."""
    return (res["solved"], -res["avg_rounds"], -res["time"])
