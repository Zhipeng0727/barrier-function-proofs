"""
diagnose_formalize.py — run the real escalation on one example and DUMP every
generated Lean program + its full compiler diagnostic to artifacts/, so failures
can be read and the tool flow improved from ground truth (not guesses).

Usage: python3 diagnose_formalize.py L4-014
"""
import json
import os
import sys

from dataset_loader import convert_manifest_record
from lean_escalation import (run_lean_escalation, make_real_writer,
                             make_real_proposer, _base_lean_prompt)
from lean_proof import lean_compile_check
from runtime_state import reset_tokens, TOKENS, API_CONFIG, PROVIDER

MANIFEST = "/Users/zhipeng/Desktop/paper4/data/lean4_core200_diverse_manifest_v5.json"
ART = os.path.join(os.path.dirname(os.path.abspath(__file__)), "artifacts")


def load(eid):
    d = json.load(open(MANIFEST, encoding="utf-8"))
    rec = {r["id"]: r for r in d["core200"]}[eid]
    s, _ = convert_manifest_record(rec, None, {})
    return s


def main(eid):
    os.makedirs(ART, exist_ok=True)
    s = load(eid)
    cert = s["cert_gt"]
    print(f"provider={PROVIDER} model={API_CONFIG['model']}  {eid}  cert={cert}\n")
    reset_tokens()

    # capturing writer/compiler: wrap the real ones, persist every artifact
    real_writer = make_real_writer(effort="high")
    seq = {"n": 0}
    log = []

    def writer(ctx):
        code = real_writer(ctx)
        seq["n"] += 1
        path = os.path.join(ART, f"{eid}_{seq['n']:02d}_{ctx['strategy']}.lean")
        with open(path, "w", encoding="utf-8") as f:
            f.write(f"-- strategy={ctx['strategy']} cert={ctx['cert']}\n{code}\n")
        log.append({"n": seq["n"], "strategy": ctx["strategy"], "path": path,
                    "code_len": len(code)})
        return code

    def compiler(code):
        ok, diag = lean_compile_check(code, f"diag_{eid}_{seq['n']}", strict_sorry=True)
        log[-1]["compile_ok"] = ok
        log[-1]["diag"] = diag
        # full diagnostic to a sidecar file
        with open(log[-1]["path"] + ".diag.txt", "w", encoding="utf-8") as f:
            f.write(f"compile_ok={ok}\n\n{diag}")
        tag = "OK ✅" if ok else "FAIL"
        print(f"  attempt {seq['n']} [{log[-1]['strategy']}] {tag}")
        if not ok:
            head = diag.split("\n")[0][:140]
            print(f"     → {head}")
        return ok, diag

    res = run_lean_escalation(
        s, cert, write_fn=writer, compile_fn=compiler,
        propose_fn=make_real_proposer(effort="high"),
        budget={"inner": 4, "barriers": 2, "max_calls": 7, "repeat_l3": 3},
        on_event=None,
    )
    print(f"\nsolved={res['solved']} level={res['final_level']} "
          f"calls={res['calls']} out_tokens={TOKENS['output']}")
    print(f"artifacts in {ART}/  ({len(log)} programs dumped)")
    summary = os.path.join(ART, f"{eid}_summary.json")
    json.dump({"id": eid, "cert": cert, "result": res,
               "attempts": [{k: v for k, v in a.items() if k != "diag"} for a in log]},
              open(summary, "w"), indent=2, default=str)
    return res


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else "L4-014")
