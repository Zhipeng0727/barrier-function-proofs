#!/usr/bin/env python3
"""smoke_v5.py — local (zero-token) end-to-end check of the v5 pipeline:
load every locally-parseable manifest entry and verify its ground-truth
certificate with the task-appropriate verifier. Per-entry wall time printed."""
import json
import sys
import time
import collections

from dataset_loader import convert_manifest_record
from barrier_core import local_verify

MANIFEST = "/Users/zhipeng/Desktop/paper4/data/lean4_core200_diverse_manifest_v5.json"


def main():
    d = json.load(open(MANIFEST, encoding="utf-8"))
    ok = []
    for rec in d["core200"]:
        s, _ = convert_manifest_record(rec, None, {})
        if s:
            ok.append((rec["id"], s))
    print(f"loaded {len(ok)} entries locally; verifying ground-truth certificates...",
          flush=True)
    res = {"pass": [], "fail": [], "nocert": []}
    for eid, s in ok:
        if not s["cert_gt"]:
            res["nocert"].append(eid)
            continue
        t0 = time.time()
        try:
            lv = local_verify(s, s["cert_gt"], {"xu_points": [], "escape_points": []})
            tag = "PASS" if lv["passed"] else "FAIL"
            (res["pass"] if lv["passed"] else res["fail"]).append((eid, lv))
        except Exception as e:
            tag, lv = "EXC ", {"feedback": f"{type(e).__name__}: {e}"}
            res["fail"].append((eid, lv))
        print(f"  {tag} {eid:<8} {s['task_type'][:4]}/{'disc' if s['discrete'] else 'cont'}"
              f"  {time.time()-t0:6.1f}s", flush=True)
    print(f"\nPASS: {len(res['pass'])}  FAIL: {len(res['fail'])}  NO-CERT: {len(res['nocert'])}")
    for eid, lv in res["fail"]:
        fb = (lv.get("feedback") or "")[:160].replace("\n", " | ")
        print(f"  FAIL {eid}: {fb}")
    print("no-cert:", res["nocert"])
    bytask = collections.Counter()
    for eid, s in ok:
        bytask[(s["task_type"], "disc" if s["discrete"] else "cont")] += 1
    print("loaded by task:", dict(bytask))
    return 0 if not res["fail"] else 1


if __name__ == "__main__":
    sys.exit(main())
