"""
validate_escalation.py — run the real (GLM + Lean) escalation orchestrator on
ground-truth certificates from the core200 manifest, to validate the tool flow and
collect failure data for iterative improvement.

Usage: python3 validate_escalation.py L4-014 B2-007 L1-001
"""
import json
import sys
import time

from dataset_loader import convert_manifest_record
from lean_escalation import formalize_certificate
from runtime_state import TOKENS, reset_tokens, API_CONFIG, PROVIDER

MANIFEST = "/Users/zhipeng/Desktop/paper4/data/lean4_core200_diverse_manifest_v5.json"
BUDGET = {"inner": 2, "barriers": 2, "max_calls": 4, "repeat_l3": 2}


def load_systems(ids):
    d = json.load(open(MANIFEST, encoding="utf-8"))
    by_id = {rec["id"]: rec for rec in d["core200"]}
    out = []
    for i in ids:
        s, _ = convert_manifest_record(by_id[i], None, {})
        if s and s.get("cert_gt"):
            out.append((i, s))
        else:
            print(f"  [skip] {i}: not locally parseable / no cert_gt")
    return out


def main(ids):
    print(f"provider={PROVIDER} model={API_CONFIG['model']} budget={BUDGET}\n")
    systems = load_systems(ids)
    summary = []
    for eid, s in systems:
        print(f"\n{'='*64}\n{eid}: {s['name']}  | cert: {s['cert_gt']}\n{'='*64}")
        reset_tokens()
        t0 = time.time()
        try:
            res = formalize_certificate(s, s["cert_gt"], budget=BUDGET)
            ok, level = res["solved"], res["final_level"]
        except Exception as e:
            res, ok, level = {"calls": 0}, False, f"EXC:{type(e).__name__}:{e}"
        dt = time.time() - t0
        toks = TOKENS["output"]
        routes = "→".join(l["route"] for l in res.get("levels", []))
        summary.append((eid, ok, level, res.get("calls", 0), toks, round(dt), routes))
        print(f"\n  RESULT {eid}: solved={ok} level={level} calls={res.get('calls',0)} "
              f"out_tokens={toks} {dt:.0f}s  routes={routes}")
        if not ok and res.get("diag"):
            print(f"  last diag: {res['diag'][:300].replace(chr(10),' | ')}")

    print(f"\n\n{'#'*64}\nSUMMARY\n{'#'*64}")
    print(f"{'id':10s} {'solved':7s} {'level':12s} {'calls':6s} {'out_tok':8s} {'sec':5s} routes")
    for eid, ok, level, calls, toks, dt, routes in summary:
        print(f"{eid:10s} {str(ok):7s} {str(level):12s} {calls:<6d} {toks:<8d} {dt:<5d} {routes}")
    solved = sum(1 for r in summary if r[1])
    print(f"\nSOLVED {solved}/{len(summary)}")
    return summary


if __name__ == "__main__":
    main(sys.argv[1:] or ["L4-014"])
