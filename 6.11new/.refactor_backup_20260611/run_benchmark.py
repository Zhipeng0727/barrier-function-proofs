#!/usr/bin/env python3
"""
run_benchmark.py — batch-evaluate the v4 pipeline over a dataset.

Per entry it records: solved, turns used, refuter calls, tokens in/out, wall time.
Outputs a CSV + JSON summary under benchmark_results/<run-name>/ so different
pipeline variants (v3 vs v4, KB on/off, effort ladders) can be A/B compared.

Examples:
  python3 run_benchmark.py --dataset /Users/zhipeng/lean/data/invariant_dataset.jsonl --limit 10
  python3 run_benchmark.py --dataset /Users/zhipeng/lean/data/koopman_nopoly_extension.json --limit 5 --lean
"""
import argparse
import csv
import datetime
import json
import os
import re
import sys
import traceback

import dual_agent_debate_4 as v4  # unified pipeline; pick backend via --provider
from dataset_loader import load_dataset


class _Tee:
    """Fan stdout/stderr to the terminal AND a log file at the same time."""
    def __init__(self, *streams):
        self.streams = streams

    def write(self, data):
        for s in self.streams:
            s.write(data)
            s.flush()

    def flush(self):
        for s in self.streams:
            s.flush()


def main():
    parser = argparse.ArgumentParser(description="Batch benchmark for barrier pipeline v4")
    parser.add_argument("--dataset", required=True)
    parser.add_argument("--limit", type=int, default=None, help="Max entries to run")
    parser.add_argument("--start", type=int, default=0, help="Skip the first N entries")
    parser.add_argument("--turns", type=int, default=5)
    parser.add_argument("--provider", default="openai", choices=list(v4.PROVIDERS),
                        help="Backend: 'openai' (codex/GPT, default) or 'anthropic' (Claude)")
    parser.add_argument("--model", default=None)
    parser.add_argument("--no-kb", action="store_true")
    parser.add_argument("--lean", action="store_true", help="Enable Lean4 phase (off by default in batch)")
    parser.add_argument("--name", default=None, help="Run name (default: timestamp)")
    args = parser.parse_args()

    v4.select_provider(args.provider)
    if args.model:
        v4.API_CONFIG["model"] = args.model  # explicit override wins over provider default

    run_name = args.name or datetime.datetime.now().strftime("%m%d_%H%M%S")
    out_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                           "benchmark_results", run_name)
    os.makedirs(out_dir, exist_ok=True)

    # tee all console output into the run's own folder — no shell redirect needed
    _log_fh = open(os.path.join(out_dir, "run.log"), "w", encoding="utf-8")
    sys.stdout = _Tee(sys.__stdout__, _log_fh)
    sys.stderr = _Tee(sys.__stderr__, _log_fh)
    print(f"[Log] tee -> {os.path.join(out_dir, 'run.log')}")

    entries, skipped = load_dataset(
        args.dataset,
        call_fn=lambda s, m: v4.call_api(s, m, effort="medium", label="dataset-convert"),
        limit=(args.start + args.limit) if args.limit else None,
    )
    print(f"[Dataset] {len(entries)} usable entries, {len(skipped)} skipped")
    for eid, reason in skipped[:10]:
        print(f"  skipped {eid}: {reason}")

    selected = entries[args.start: args.start + args.limit if args.limit else None]
    rows = []
    for i, (eid, system) in enumerate(selected, 1):
        key = re.sub(r"\W+", "_", str(eid))[:50]
        print(f"\n######## [{i}/{len(selected)}] {eid} ########")
        row = {"id": eid, "solved": False, "turns": None, "refuter_calls": None,
               "tokens_in": None, "tokens_out": None, "elapsed_s": None,
               "h": None, "lean_compile_ok": None, "error": None}
        try:
            result = v4.run_barrier_synthesis_v4(
                key, turns=args.turns, system=system,
                output_dir=os.path.join(out_dir, key),
                use_kb=not args.no_kb, do_plot=False, do_lean=args.lean,
            )
            row.update({
                "solved": result["solved"],
                "turns": len(result["rounds"]),
                "refuter_calls": result["refuter_calls"],
                "tokens_in": result["tokens"]["input"],
                "tokens_out": result["tokens"]["output"],
                "elapsed_s": result["timing"]["total_elapsed_s"],
                "h": (result.get("final_barrier") or {}).get("h"),
                "lean_compile_ok": (result.get("lean4") or {}).get("compile_ok"),
            })
        except KeyboardInterrupt:
            print("Interrupted — writing partial summary.")
            row["error"] = "interrupted"
            rows.append(row)
            break
        except Exception as e:
            traceback.print_exc()
            row["error"] = f"{type(e).__name__}: {e}"
        rows.append(row)

        # write incrementally so a crash never loses progress
        _write_summary(out_dir, args, rows, skipped)

    _write_summary(out_dir, args, rows, skipped)
    solved = [r for r in rows if r["solved"]]
    tok_out = sum(r["tokens_out"] or 0 for r in rows)
    tok_in = sum(r["tokens_in"] or 0 for r in rows)
    print(f"\n{'='*60}\nRun: {run_name}")
    print(f"Solved {len(solved)}/{len(rows)}; "
          f"avg turns (solved): {sum(r['turns'] for r in solved)/len(solved):.2f}" if solved
          else f"Solved 0/{len(rows)}")
    print(f"Total tokens in/out: {tok_in}/{tok_out}")
    print(f"Summary: {os.path.join(out_dir, 'summary.csv')}")


def _write_summary(out_dir, args, rows, skipped):
    with open(os.path.join(out_dir, "summary.json"), "w", encoding="utf-8") as f:
        json.dump({"config": vars(args), "model": v4.API_CONFIG["model"],
                   "rows": rows, "skipped": skipped}, f, ensure_ascii=False, indent=2)
    if rows:
        with open(os.path.join(out_dir, "summary.csv"), "w", newline="", encoding="utf-8") as f:
            writer = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
            writer.writeheader()
            writer.writerows(rows)


if __name__ == "__main__":
    main()
