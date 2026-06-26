"""
glm_tuner.py — GLM-in-the-loop tuning of the neural-CEGIS agent structure. After
each evaluated config, the structured results are handed to GLM (the user's own
API via runtime_state), which proposes the next config to try under a controlled
protocol (change one or two knobs, don't repeat, maximise solved then minimise
rounds/time). This is the "use GLM for feedback to tune parameters / try several
agents" loop.
"""
from __future__ import annotations

import json
import os
import re
import sys

_PARENT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
if _PARENT not in sys.path:
    sys.path.insert(0, _PARENT)

from runtime_state import call_api, select_provider  # noqa: E402
from verif_agent.neural.sweep import run_config, BASE, score  # noqa: E402

KNOBS = {
    "kind": ["structural", "plain"],
    "width": [3, 4, 5, 6, 8, 12],
    "margin": [0.0, 1e-3, 1e-2, 5e-2],
    "lr": [0.005, 0.01, 0.02, 0.05],
    "iters": [300, 400, 800, 1500],
    "n_samples": [500],
    "alpha": [0.05, 0.1, 0.2],
    "verifier": ["interval", "dreal"],
    "max_rounds": [3, 4, 6],
}

_SYS = ("You tune a neural-Lyapunov CEGIS agent. Goal: maximise the number of "
        "systems that get a SOUND certificate, then minimise CEGIS rounds and wall "
        "time. You change the agent's structure via a small set of knobs. Reply with "
        "ONLY a JSON object, no prose.")


def _clamp(cfg):
    out = dict(BASE)
    for k, v in (cfg or {}).items():
        if k in KNOBS:
            out[k] = v
    # snap numeric knobs to the nearest allowed value
    for k in ("width", "iters", "max_rounds"):
        out[k] = min(KNOBS[k], key=lambda a: abs(a - out[k]))
    if out["kind"] not in KNOBS["kind"]:
        out["kind"] = "structural"
    if out["verifier"] not in KNOBS["verifier"]:
        out["verifier"] = "interval"
    return out


def _history_brief(history):
    rows = []
    for h in history:
        c = h["cfg"]
        rows.append({"name": h["name"],
                     "knobs": {k: c[k] for k in ("kind", "width", "margin", "lr",
                                                 "iters", "verifier", "max_rounds")},
                     "solved": f'{h["result"]["solved"]}/{h["result"]["n"]}',
                     "avg_rounds": h["result"]["avg_rounds"],
                     "time": h["result"]["time"]})
    return rows


def propose(history):
    prompt = (
        "Knob space (allowed values):\n" + json.dumps(KNOBS) + "\n\n"
        "Results so far (controlled — each row is one config):\n"
        + json.dumps(_history_brief(history), indent=1) + "\n\n"
        "Propose the NEXT config to try. Change one or two knobs versus the best "
        "row so far; do not repeat a config already tried. Output strictly:\n"
        '{"name": "<short>", "cfg": {<full knob dict>}, "rationale": "<one line>"}')
    txt, _ = call_api(_SYS, [{"role": "user", "content": prompt}],
                      label="neural-tuner", provider="glm")
    m = re.search(r"\{.*\}", txt, re.S)
    obj = json.loads(m.group(0) if m else txt)
    return obj.get("name", "glm")[:24], _clamp(obj.get("cfg")), obj.get("rationale", "")


def glm_tune(systems, rounds=4, seed=0, log_path=None):
    select_provider("glm")
    history = []
    base_res = run_config(systems, BASE, seed=seed)
    history.append({"name": "base", "cfg": dict(BASE), "result": base_res, "rationale": "seed"})
    print(f"  [base            ] solved {base_res['solved']}/{base_res['n']} "
          f"avg_rounds {base_res['avg_rounds']} time {base_res['time']}s")
    for i in range(rounds):
        try:
            name, cfg, why = propose(history)
        except Exception as e:
            print(f"  GLM propose failed ({type(e).__name__}); stopping tune")
            break
        res = run_config(systems, cfg, seed=seed)
        history.append({"name": name, "cfg": cfg, "result": res, "rationale": why})
        print(f"  [{name:16}] solved {res['solved']}/{res['n']} "
              f"avg_rounds {res['avg_rounds']} time {res['time']}s  ← {why[:50]}")
        if log_path:
            with open(log_path, "w", encoding="utf-8") as f:
                json.dump(history, f, ensure_ascii=False, indent=1)
    best = max(history, key=lambda h: score(h["result"]))
    return history, best
