#!/usr/bin/env python3
"""
eval_on_core200.py — the benchmark harness. For every cert-bearing entry it runs:
  (a) the ROUTED agent (selection, stops at first conclusive sound verdict), and
  (b) each backend STANDALONE (sampling / z3 / dreal),
then reports, per backend and for the agent:
  - sound-proved coverage, refutations, unknowns
  - wall time, and the ORACLE (any sound backend proves) coverage
  - acceleration: routed wall-time vs run-the-whole-pool wall-time

This is the figure that answers "does method selection help here". Run:
  python3 -m verif_agent.eval_on_core200 --limit 200
  python3 -m verif_agent.eval_on_core200 --limit 200 --use-glm   # fuller coverage
"""
from __future__ import annotations

import argparse
import json
import os
import sys
import time

_PARENT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if _PARENT not in sys.path:
    sys.path.insert(0, _PARENT)

from dataset_loader import load_dataset                       # noqa: E402
from verif_agent import verify, route_system                  # noqa: E402
from verif_agent.backend_base import get_backend              # noqa: E402

DEFAULT_MANIFEST = "/Users/zhipeng/Desktop/paper4/data/lean4_core200_diverse_manifest_v5.json"
STANDALONE = ["sampling", "z3", "interval", "dreal"]


def _glm_call_fn():
    from runtime_state import call_api, select_provider
    select_provider("glm")

    def call(system_prompt, messages):
        return call_api(system_prompt, messages, label="dataset-convert")
    return call


def _run_standalone(system, cert, timeout_ms):
    out = {}
    for name in STANDALONE:
        b = get_backend(name)
        kw = {"timeout_ms": timeout_ms} if name == "z3" else {}
        r = b.verify(system, cert, **kw)
        out[name] = {"status": r.status, "sound": r.sound,
                     "elapsed_s": round(r.elapsed_s, 3)}
    return out


def run(manifest, limit, timeout_ms, with_lean, use_glm, out_path):
    call_fn = _glm_call_fn() if use_glm else None
    entries, skipped = load_dataset(manifest, call_fn=call_fn, limit=limit)
    cert_entries = [(e, s) for e, s in entries if s.get("cert_gt")]
    print(f"loaded {len(entries)} systems ({len(cert_entries)} with a certificate); "
          f"{len(skipped)} unparsed\n")

    rows = []
    t_all = time.time()
    for eid, system in cert_entries:
        cert = system["cert_gt"]
        routing = route_system(system, cert)
        agent_res = verify(system, cert, with_lean=with_lean, timeout_ms=timeout_ms)
        standalone = _run_standalone(system, cert, timeout_ms)
        oracle_sound = any(v["sound"] and v["status"] == "proved" for v in standalone.values())
        rows.append({
            "id": eid,
            "class": routing["features"],
            "task": system.get("task_type"),
            "ladder": agent_res.ladder,
            "agent_status": agent_res.status,
            "agent_sound": agent_res.sound,
            "agent_backend": agent_res.chosen_backend,
            "agent_time": round(agent_res.elapsed_s, 3),
            "standalone": standalone,
            "oracle_sound": oracle_sound,
        })
    total_wall = time.time() - t_all

    _report(rows, total_wall, out_path, manifest, limit)
    return rows


def _report(rows, total_wall, out_path, manifest, limit):
    n = len(rows)
    # per-backend standalone tallies
    bk = {name: {"proved_sound": 0, "refuted": 0, "unknown": 0,
                 "unsupported": 0, "unavailable": 0, "error": 0, "time": 0.0}
          for name in STANDALONE}
    for r in rows:
        for name, v in r["standalone"].items():
            st = v["status"]
            key = "proved_sound" if (st == "proved" and v["sound"]) else st
            bk[name][key] = bk[name].get(key, 0) + 1
            bk[name]["time"] += v["elapsed_s"]

    agent_sound = sum(1 for r in rows if r["agent_sound"] and r["agent_status"] == "proved")
    agent_refuted = sum(1 for r in rows if r["agent_status"] == "refuted")
    agent_unsound_pass = sum(1 for r in rows
                             if r["agent_status"] == "proved" and not r["agent_sound"])
    agent_unknown = sum(1 for r in rows if r["agent_status"] == "unknown")
    oracle = sum(1 for r in rows if r["oracle_sound"])
    agent_time = sum(r["agent_time"] for r in rows)
    runall_time = sum(v["elapsed_s"] for r in rows for v in r["standalone"].values())

    print("=" * 72)
    print(f"BENCHMARK  ({n} cert-bearing systems)")
    print("=" * 72)
    print("\nStandalone backends (sound proofs only count as 'proved'):")
    print(f"  {'backend':9} {'proved':>7} {'refut':>6} {'unkn':>5} {'unsup':>6} "
          f"{'unavl':>6} {'err':>4} {'time(s)':>8}")
    for name in STANDALONE:
        b = bk[name]
        print(f"  {name:9} {b['proved_sound']:>7} {b['refuted']:>6} {b['unknown']:>5} "
              f"{b.get('unsupported',0):>6} {b.get('unavailable',0):>6} {b.get('error',0):>4} "
              f"{b['time']:>8.2f}")

    print(f"\nROUTED AGENT:")
    print(f"  sound proofs : {agent_sound}/{n}")
    print(f"  refutations  : {agent_refuted}/{n}")
    print(f"  unsound pass : {agent_unsound_pass}/{n}  (no sound backend available — "
          f"these are the cases waiting on dReal)")
    print(f"  unknown      : {agent_unknown}/{n}")
    print(f"  ORACLE (any sound backend proves) : {oracle}/{n}")
    print(f"  agent matches oracle coverage     : {agent_sound}/{oracle} "
          f"of oracle-provable solved soundly by routing")

    print(f"\nACCELERATION (selection = stop at first conclusive):")
    print(f"  routed wall-time      : {agent_time:8.2f}s")
    print(f"  run-whole-pool time   : {runall_time:8.2f}s")
    if runall_time > 0:
        print(f"  speedup               : {runall_time / max(agent_time,1e-6):8.2f}x")
    print(f"  harness total wall    : {total_wall:8.2f}s")

    # class breakdown of where sound coverage stands
    from collections import Counter
    by_class = Counter()
    sound_by_class = Counter()
    for r in rows:
        c = r["class"].split()[-1]
        by_class[c] += 1
        if r["agent_sound"]:
            sound_by_class[c] += 1
    print("\nSound coverage by expression class:")
    for c, tot in by_class.most_common():
        print(f"  {c:14} {sound_by_class[c]:>3}/{tot:<3} sound")

    payload = {"manifest": manifest, "limit": limit, "n": n,
               "standalone": bk, "agent": {
                   "sound": agent_sound, "refuted": agent_refuted,
                   "unsound_pass": agent_unsound_pass, "unknown": agent_unknown,
                   "oracle": oracle, "routed_time": agent_time,
                   "runall_time": runall_time},
               "rows": rows}
    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(payload, f, ensure_ascii=False, indent=1)
    print(f"\nper-instance results -> {out_path}")


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--manifest", default=DEFAULT_MANIFEST)
    ap.add_argument("--limit", type=int, default=200)
    ap.add_argument("--timeout-ms", type=int, default=6000)
    ap.add_argument("--with-lean", action="store_true")
    ap.add_argument("--use-glm", action="store_true",
                    help="use GLM to convert manifest entries local parsing can't (fuller coverage)")
    ap.add_argument("--out", default=os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                                  "benchmark_result.json"))
    a = ap.parse_args()
    run(a.manifest, a.limit, a.timeout_ms, a.with_lean, a.use_glm, a.out)
