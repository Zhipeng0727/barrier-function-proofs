#!/usr/bin/env python3
"""
run_lean_gaps.py — Run the Lean formalization pipeline on the 12 cases where
NO automated numerical backend (z3/interval/dReal) can produce a sound proof.
These are the LEAN-NECESSARY cases — the paper's core claim.

Uses lean_escalation.formalize_certificate with the full reinforced pipeline
(recipe injection + three-level L1/L2/L3 escalation).
"""
import json
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from dataset_loader import load_dataset
from lean_escalation import formalize_certificate
from runtime_state import reset_tokens, TOKENS

MANIFEST = "/Users/zhipeng/Desktop/paper4/data/lean4_core200_diverse_manifest_v5.json"
OUT = os.path.join(HERE, "lean_gap_results.json")

GAP_IDS = [
    "L1-006", "L4-014", "L4-015", "B1-006", "B1-017", "B2-002",
    "B3-001", "B3-003", "B6-001", "B4-018", "L7-001", "L7-003",
]

LEAN_BUDGET = {"inner": 5, "barriers": 2, "max_calls": 8, "repeat_l3": 3}


def _build_system(entry, parsed_system):
    """Merge manifest metadata + parsed system dict into lean_escalation's format."""
    s = dict(parsed_system)
    s.setdefault("ode", entry.get("dynamics", ""))
    s.setdefault("X_domain", str(s.get("X_bounds", "")))
    s.setdefault("task", s.get("task_type", entry.get("task", "lyapunov")))
    s.setdefault("name", entry.get("id", ""))
    return s


def main():
    from runtime_state import call_api, select_provider
    select_provider("glm")

    def call_fn(system_prompt, messages):
        return call_api(system_prompt, messages, label="dataset-convert")

    entries_raw, skipped = load_dataset(MANIFEST, call_fn=call_fn, limit=200)
    entries_by_id = {}
    manifest = json.load(open(MANIFEST))
    manifest_by_id = {e["id"]: e for e in manifest["core200"]}
    for eid, system in entries_raw:
        entries_by_id[eid] = system

    results = []
    total_t0 = time.time()

    print(f"{'='*70}")
    print(f"LEAN GAP RUNNER — {len(GAP_IDS)} cases, budget={LEAN_BUDGET}")
    print(f"{'='*70}\n")

    for gid in GAP_IDS:
        system = entries_by_id.get(gid)
        entry = manifest_by_id.get(gid, {})
        cert = entry.get("certificate", "")

        if not system:
            print(f"[{gid}] SKIP — not parseable locally (needs GLM conversion)")
            if system is None:
                print(f"  trying GLM conversion...")
                continue
            results.append({"id": gid, "status": "skip", "reason": "not_parsed"})
            continue

        cert_gt = system.get("cert_gt", cert)
        if not cert_gt:
            print(f"[{gid}] SKIP — no certificate")
            results.append({"id": gid, "status": "skip", "reason": "no_cert"})
            continue

        sysd = _build_system(entry, system)
        print(f"\n[{gid}] {entry.get('title', '?')}")
        print(f"  cert: {cert_gt[:70]}")
        print(f"  dynamics: {entry.get('dynamics', '?')[:70]}")

        reset_tokens()
        t0 = time.time()
        events = []

        def on_event(e):
            events.append(e)
            ev = e.get("event", "")
            if ev == "attempt":
                mark = "✅" if e.get("compile_ok") else f"L{e.get('route','?')[0]}"
                print(f"    attempt b{e['barrier']}.{e['inner']}: "
                      f"{e['strategy']} → {mark} ({e.get('err','')})")
            elif ev == "escalate":
                print(f"    ↑ escalate to {e['to']} ({e.get('reason','')})")
            elif ev == "regenerate_barrier":
                print(f"    ⟳ regenerate barrier (was: {e['after_cert'][:40]}...)")

        try:
            res = formalize_certificate(sysd, cert_gt, budget=LEAN_BUDGET,
                                        strict_sorry=True, on_event=on_event)
            dt = round(time.time() - t0, 1)
            solved = res.get("solved", False)
            mark = "✅ PROVED" if solved else "❌ partial"
            print(f"  → {mark} | level={res.get('final_level')} | "
                  f"calls={res.get('calls')} | {dt}s | {TOKENS['output']} tok")

            results.append({
                "id": gid,
                "title": entry.get("title", ""),
                "status": "proved" if solved else "partial",
                "solved": solved,
                "final_level": res.get("final_level"),
                "calls": res.get("calls"),
                "time_s": dt,
                "tokens": TOKENS["output"],
                "code": res.get("code", "")[:2000] if solved else None,
                "verif_cond_class": entry.get("verif_cond_class"),
            })
        except Exception as e:
            dt = round(time.time() - t0, 1)
            print(f"  → ERROR: {type(e).__name__}: {e}")
            results.append({
                "id": gid, "status": "error",
                "error": f"{type(e).__name__}: {e}", "time_s": dt,
            })

    total_dt = round(time.time() - total_t0)
    solved_count = sum(1 for r in results if r.get("solved"))
    print(f"\n{'='*70}")
    print(f"LEAN GAP RESULTS: {solved_count}/{len(results)} proved | {total_dt}s total")
    print(f"{'='*70}")
    for r in results:
        mark = "✅" if r.get("solved") else ("⏭" if r["status"] == "skip" else "❌")
        print(f"  {mark} {r['id']:10} {r['status']:8} "
              f"{r.get('final_level',''):8} {r.get('time_s',0):>5.0f}s")

    json.dump(results, open(OUT, "w"), indent=2, ensure_ascii=False)
    print(f"\nSaved → {OUT}")
    return results


if __name__ == "__main__":
    main()
