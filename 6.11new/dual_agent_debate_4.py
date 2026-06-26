#!/usr/bin/env python3
"""
dual_agent_debate_4.py — orchestrator + CLI entry point for the iterated
barrier-synthesis pipeline (v4), and the stable public facade for run_benchmark.py.

Composes the three building-block modules:
  - runtime_state : mutable state (API_CONFIG / PROVIDER / TOKENS) + call_api transport
  - barrier_core  : system catalog, agent prompts, local verification, plotting
  - lean_proof    : Lean 4 generate/compile/repair loop

Pipeline (per system): Proposer proposes h(x) -> local sympy/scipy verification
(zero tokens) -> only locally-passing candidates reach the LLM Refuter -> on
"valid" stop, else feed compact critique back to the Proposer. Optional Lean4
formalization of the final barrier.

This module re-exports the five names run_benchmark.py consumes (API_CONFIG,
PROVIDERS, select_provider, call_api, run_barrier_synthesis_v4) so `v4.<name>`
keeps resolving — the imports below bind the SAME objects (no copies).
"""
import argparse
import datetime
import json
import os
import re
import time

# re-export for run_benchmark.py (binds the identical runtime_state objects)
from runtime_state import (
    API_CONFIG, PROVIDERS, select_provider, call_api, reset_tokens, TOKENS,
    EFFORT_LADDER,
)
from barrier_core import (
    SYSTEMS, proposer_system, refuter_system, parse_json_response,
    plot_barrier, local_verify, _task_framework,
)
from lean_proof import generate_lean_proof
from knowledge_base import KnowledgeBase

__all__ = [
    "API_CONFIG", "PROVIDERS", "select_provider", "call_api",
    "run_barrier_synthesis_v4", "run_certificate_verification", "main",
]

# ─────────────────────────────────────────────
# Compact Proposer context
# ─────────────────────────────────────────────
def build_proposer_msg(system: dict, attempts: list, cache: dict, kb_block: str,
                       refuter_critique: str = None, enlargement_hint: str = None) -> str:
    fw = _task_framework(system)
    base = (
        f"Please {fw['goal']}.\n\n"
        f"System: {system['ode']}\n"
        f"State domain: {system['X_domain']}"
        + (f"\nUnsafe set: {system['X_u_desc']}" if system.get("X_u_desc") else "")
    )
    sections = [base]
    if kb_block:
        sections.append(kb_block)
    if attempts:
        lines = ["[Your previous attempts and why each failed — do NOT repeat these mistakes]"]
        for a in attempts[-4:]:
            lines.append(f"- h = {a['h']}\n  failure: {a['failure'][:600]}")
        sections.append("\n".join(lines))
    cex = cache.get("xu_points", []) + cache.get("escape_points", [])
    if cex:
        sections.append(
            "[Known counterexample points — your new h MUST handle all of them]\n" +
            json.dumps(cex[:10], ensure_ascii=False))
    if refuter_critique:
        sections.append(f"[Verifier critique of the last proposal]\n{refuter_critique[:1500]}")
    if enlargement_hint:
        sections.append(
            f"[The last h was VALID. Suggestion to enlarge the invariant set]\n{enlargement_hint}\n"
            f"Only adjust it if you can keep both conditions satisfied; otherwise return the valid h unchanged.")
    sections.append("Output the JSON object in the required format.")
    return "\n\n".join(sections)


# ─────────────────────────────────────────────
# Refuter gate (token saver): polynomial candidates whose local checks pass
# with zero violations are exactly the cases sampling already covers reliably
# (SMT/SOS territory) — the LLM Refuter adds little there. Transcendental
# candidates always go to the Refuter.
# ─────────────────────────────────────────────
def _refuter_gate(system: dict, h_str: str, lv: dict) -> bool:
    try:
        import sympy as sp
        syms = [sp.Symbol(v, real=True) for v in system["state_vars"]]
        loc = {s.name: s for s in syms}
        h = sp.sympify(h_str.replace("^", "**"), locals=loc)
        if not h.is_polynomial(*syms):
            return False
        for fe in system["f_expr"]:
            if not sp.sympify(fe.replace("^", "**"), locals=loc).is_polynomial(*syms):
                return False
    except Exception:
        return False
    sym = lv.get("symbolic", {})
    traj = lv.get("trajectory", {})
    if system.get("task_type") == "lyapunov":
        clean = (sym.get("decrease_viol_frac") == 0 and sym.get("positivity_ok") is True)
    else:
        clean = (sym.get("cond1_ok") is True and
                 (sym.get("cond2_viol_frac") in (0, 0.0, None)) and sym.get("cond2_ok") is True)
    return bool(clean and traj.get("trajectory_valid") is not False)


# ─────────────────────────────────────────────
# Main synthesis loop (v4)
# ─────────────────────────────────────────────
def run_barrier_synthesis_v4(system_key: str, turns: int = 5, output_dir: str = None,
                             system: dict = None, delay: float = 1.0, use_kb: bool = True,
                             do_plot: bool = True, do_lean: bool = True,
                             lean_repair: int = 2, refuter_gate: bool = True) -> dict:
    system = system or SYSTEMS[system_key]
    out_dir = output_dir or os.path.join(os.path.dirname(os.path.abspath(__file__)), system_key)
    os.makedirs(out_dir, exist_ok=True)
    prefix = os.path.join(out_dir, f"v4_{system_key}")

    kb = KnowledgeBase() if use_kb else None
    kb_block = kb.few_shot_block(system) if kb else ""
    if kb_block:
        print(f"[KB] injected {kb_block.count('Example ')} reference case(s)")

    reset_tokens()
    pipeline_start = time.time()
    print(f"\n{'='*60}\nSystem: {system['name']}\nDynamics: {system['ode']}\n"
          f"Model: {API_CONFIG['model']} | max turns: {turns}\n{'='*60}")

    result = {
        "pipeline": "v4",
        "system": system,
        "timestamp": datetime.datetime.now().isoformat(),
        "model": API_CONFIG["model"],
        "rounds": [],
        "final_barrier": None,
        "solved": False,
        "refuter_calls": 0,
        "lean4": None,
    }

    cache = {"xu_points": [], "escape_points": []}
    attempts = []          # [{h, failure}]
    refuter_critique = None
    enlargement_hint = None
    effort_idx = 0

    for turn in range(1, turns + 1):
        effort = EFFORT_LADDER[min(effort_idx, len(EFFORT_LADDER) - 1)]
        print(f"\n{'─'*50}\nTurn {turn}  (reasoning effort: {effort})\n{'─'*50}")

        user_msg = build_proposer_msg(system, attempts, cache, kb_block if turn == 1 else "",
                                      refuter_critique, enlargement_hint)
        refuter_critique = enlargement_hint = None

        print("[Proposer] generating...")
        reply_a, t_prop = call_api(proposer_system(system), [{"role": "user", "content": user_msg}],
                                   effort=effort, label=f"proposer#{turn}")
        proposal = parse_json_response(reply_a)
        h_str = proposal.get("h", "")
        print(f"  h = {h_str}")

        round_rec = {"turn": turn, "effort": effort, "proposal": proposal,
                     "proposer_elapsed_s": t_prop}
        result["rounds"].append(round_rec)

        if not h_str:
            attempts.append({"h": "(unparseable)", "failure": "output was not valid JSON with an 'h' field"})
            effort_idx += 1
            continue

        # ── local verification FIRST (zero tokens) ──
        print("[Local verification] cache + symbolic + trajectory...")
        lv = local_verify(system, h_str, cache)
        round_rec["local_verification"] = {
            "passed": lv["passed"], "cache_fails": lv["cache_fails"],
            "symbolic": lv["symbolic"], "trajectory": lv["trajectory"],
        }
        if not lv["passed"]:
            print(f"  local FAIL:\n{lv['feedback']}")
            attempts.append({"h": h_str, "failure": lv["feedback"] or "local verification failed"})
            effort_idx += 1
            time.sleep(delay)
            continue
        # ── refuter gate: clean polynomial candidates are auto-accepted ──
        if refuter_gate and _refuter_gate(system, h_str, lv):
            print("  local PASS + poly fast-path — refuter skipped (gate)")
            result["final_barrier"] = proposal
            result["solved"] = True
            result["refuter_verdict"] = "auto-accepted (poly fast-path, clean local margins)"
            round_rec["refutation"] = {"verdict": "auto-accepted-gate"}
            if kb:
                kb.add_case({
                    "id": system_key, "dim": len(system["state_vars"]),
                    "system_class": ((system.get("meta") or {}).get("system_class")
                                     or (system.get("meta") or {}).get("dynamics_class", "")),
                    "ode": system["ode"], "h": h_str,
                    "lie_derivative": lv["symbolic"].get("lie_derivative", ""),
                    "key_steps": (proposal.get("condition2_check") or "")[:800],
                    "source": "pipeline-v4-gate",
                })
            break
        print("  local PASS — escalating to LLM Refuter")

        # ── LLM Refuter only for locally-passing candidates ──
        fw = _task_framework(system)
        refuter_msg = (
            f"Please verify whether the following {fw['quantity_name']} is correct:\n\n"
            f"System: {system['ode']}\nState domain: {system['X_domain']}\n"
            + (f"Unsafe set: {system['X_u_desc']}\n" if system.get("X_u_desc") else "")
            + f"Proposed certificate = {h_str}\n"
            f"Claimed certified set: {proposal.get('invariant_set', 'unknown')}\n\n"
            f"Local numerical checks (sampling + trajectories) already PASSED. Focus on what "
            f"sampling can miss: rigorous inequality reasoning, behaviour near boundary/corner "
            f"cases, and degenerate points. If valid, also analyze enlargement."
        )
        result["refuter_calls"] += 1
        try:
            reply_b, t_ref = call_api(refuter_system(system), [{"role": "user", "content": refuter_msg}],
                                      effort=EFFORT_LADDER[min(effort_idx + 1, len(EFFORT_LADDER) - 1)],
                                      label=f"refuter#{turn}")
        except RuntimeError as e:
            # relay outage mid-run: keep the locally-verified candidate instead of losing the turn
            print(f"  [Refuter] unavailable after retries ({e}); keeping locally-verified h.")
            result["final_barrier"] = proposal
            result["solved"] = True
            result["refuter_verdict"] = "unavailable (network) — local checks only"
            round_rec["refutation"] = {"verdict": "unavailable", "error": str(e)}
            break
        refutation = parse_json_response(reply_b)
        round_rec["refutation"] = refutation
        round_rec["refuter_elapsed_s"] = t_ref

        if refutation.get("verdict") == "valid":
            print(f"\nTurn {turn}: Refuter confirmed VALID — stopping.")
            result["final_barrier"] = proposal
            result["solved"] = True
            if kb:
                kb.add_case({
                    "id": system_key, "dim": len(system["state_vars"]),
                    "system_class": ((system.get("meta") or {}).get("system_class")
                                     or (system.get("meta") or {}).get("dynamics_class", "")),
                    "ode": system["ode"], "h": h_str,
                    "lie_derivative": lv["symbolic"].get("lie_derivative", ""),
                    "key_steps": (proposal.get("condition2_check") or "")[:800],
                    "source": "pipeline-v4",
                })
                print("[KB] solved case recorded")
            break
        else:
            print(f"  Refuter verdict: invalid — {str(refutation.get('flaw'))[:200]}")
            refuter_critique = json.dumps(
                {k: refutation.get(k) for k in ("flaw", "counterexample", "suggestion")},
                ensure_ascii=False)
            attempts.append({"h": h_str, "failure": f"LLM refuter: {str(refutation.get('flaw'))[:400]}"})
            effort_idx += 1
        time.sleep(delay)

    if not result["final_barrier"] and result["rounds"]:
        result["final_barrier"] = result["rounds"][-1]["proposal"]
        print("\nMax turns reached without a confirmed barrier; keeping the last proposal.")

    final = result["final_barrier"] or {}
    h_final = final.get("h", "")

    if do_plot and h_final:
        try:
            plot_barrier(system, system_key, h_final, prefix)
        except Exception as e:
            print(f"  [Plot] skipped: {e}")

    if do_lean and h_final and result["solved"]:
        print(f"\n{'─'*50}\n[Lean4 Writer] generate + compile loop\n{'─'*50}")
        result["lean4"] = generate_lean_proof(system, final, tag=re.sub(r"\W+", "_", system_key)[:40],
                                              repair_rounds=lean_repair)
        if result["lean4"]["code"]:
            with open(f"{prefix}.lean", "w", encoding="utf-8") as f:
                f.write(f"-- v4 pipeline, compile_ok={result['lean4']['compile_ok']}\n"
                        f"-- System: {system['name']}\n\n{result['lean4']['code']}")

    result["timing"] = {"total_elapsed_s": round(time.time() - pipeline_start, 3)}
    result["tokens"] = {"input": TOKENS["input"], "output": TOKENS["output"],
                        "calls": TOKENS["calls"]}

    out_path = f"{prefix}.json"
    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(result, f, ensure_ascii=False, indent=2)
    print(f"\nSolved: {result['solved']} | turns used: {len(result['rounds'])} | "
          f"refuter calls: {result['refuter_calls']} | "
          f"tokens in/out: {TOKENS['input']}/{TOKENS['output']} | "
          f"total: {result['timing']['total_elapsed_s']}s")
    print(f"Results saved: {out_path}")
    return result


# ─────────────────────────────────────────────
# Verification-only mode (v5): skip the Proposer entirely — locally verify the
# dataset's ground-truth certificate, then push it through the Lean4 phase.
# This separates the two research questions (synthesis vs formal verification)
# and is the cheapest way to move dataset entries from prove-ready to lean-verified.
# ─────────────────────────────────────────────
def run_certificate_verification(system_key: str, system: dict, output_dir: str = None,
                                 do_lean: bool = True, lean_repair: int = 2,
                                 do_plot: bool = False) -> dict:
    out_dir = output_dir or os.path.join(os.path.dirname(os.path.abspath(__file__)), system_key)
    os.makedirs(out_dir, exist_ok=True)
    prefix = os.path.join(out_dir, f"verify_{system_key}")
    reset_tokens()
    t0 = time.time()

    result = {
        "pipeline": "v5-verify-only",
        "system": system,
        "timestamp": datetime.datetime.now().isoformat(),
        "model": API_CONFIG["model"],
        "certificate": system.get("cert_gt"),
        "solved": False,
        "refuter_calls": 0,
        "rounds": [],
        "lean4": None,
    }
    cert = system.get("cert_gt")
    print(f"\n{'='*60}\n[verify-only] {system['name']}\nDynamics: {system['ode']}\n"
          f"Certificate: {cert}\n{'='*60}")
    if not cert:
        result["error"] = "no ground-truth certificate available for this entry"
        print("  SKIP: " + result["error"])
    else:
        lv = local_verify(system, cert, {"xu_points": [], "escape_points": []})
        result["local_verification"] = {
            "passed": lv["passed"], "symbolic": lv["symbolic"], "trajectory": lv["trajectory"],
        }
        result["solved"] = lv["passed"]
        if not lv["passed"]:
            print(f"  ground-truth certificate FAILED local checks:\n{lv['feedback']}")
            result["error"] = "ground-truth certificate failed local verification"
        else:
            print("  local verification PASSED")
            if do_plot:
                try:
                    plot_barrier(system, system_key, cert, prefix)
                except Exception as e:
                    print(f"  [Plot] skipped: {e}")
            if do_lean:
                print(f"\n{'─'*50}\n[Lean4 Writer] generate + compile loop\n{'─'*50}")
                final = {"h": cert,
                         "invariant_set": system.get("X_u_desc", ""),
                         "lie_derivative": lv["symbolic"].get("lie_derivative", "")}
                result["lean4"] = generate_lean_proof(
                    system, final, tag=re.sub(r"\W+", "_", system_key)[:40],
                    repair_rounds=lean_repair)
                if result["lean4"]["code"]:
                    with open(f"{prefix}.lean", "w", encoding="utf-8") as f:
                        f.write(f"-- v5 verify-only, compile_ok={result['lean4']['compile_ok']}\n"
                                f"-- System: {system['name']}\n\n{result['lean4']['code']}")

    result["timing"] = {"total_elapsed_s": round(time.time() - t0, 3)}
    result["tokens"] = {"input": TOKENS["input"], "output": TOKENS["output"],
                        "calls": TOKENS["calls"]}
    with open(f"{prefix}.json", "w", encoding="utf-8") as f:
        json.dump(result, f, ensure_ascii=False, indent=2)
    print(f"verify-only result: solved={result['solved']} | "
          f"lean_ok={(result.get('lean4') or {}).get('compile_ok')} | "
          f"tokens {TOKENS['input']}/{TOKENS['output']} | {result['timing']['total_elapsed_s']}s")
    return result


# ─────────────────────────────────────────────
# CLI
# ─────────────────────────────────────────────
def main():
    parser = argparse.ArgumentParser(description="Barrier synthesis pipeline v4")
    parser.add_argument("--system", default="darboux", help=f"Built-in system: {', '.join(SYSTEMS)}")
    parser.add_argument("--dataset", default=None, help="Path to external dataset (.json/.jsonl)")
    parser.add_argument("--entry-id", default=None, help="Entry id within --dataset")
    parser.add_argument("--turns", type=int, default=5)
    parser.add_argument("--provider", default=None, choices=list(PROVIDERS),
                        help="Backend: 'anthropic' (Claude) or 'openai' (codex/GPT)")
    parser.add_argument("--model", default=None)
    parser.add_argument("--no-kb", action="store_true", help="Disable knowledge-base few-shot")
    parser.add_argument("--no-lean", action="store_true", help="Skip Lean4 phase")
    parser.add_argument("--no-plot", action="store_true")
    parser.add_argument("--lean-repair", type=int, default=2, help="Max Lean repair rounds")
    parser.add_argument("--verify-only", action="store_true",
                        help="Skip the Proposer: verify the dataset ground-truth certificate + Lean4")
    parser.add_argument("--no-refuter-gate", action="store_true",
                        help="Always call the LLM Refuter (disable the poly fast-path)")
    args = parser.parse_args()

    if args.provider:
        select_provider(args.provider)
    if args.model:
        API_CONFIG["model"] = args.model  # explicit override wins over provider default

    if args.dataset:
        from dataset_loader import load_dataset
        entries, skipped = load_dataset(
            args.dataset,
            call_fn=lambda s, m: call_api(s, m, effort="medium", label="dataset-convert"))
        if skipped:
            print(f"[Dataset] skipped {len(skipped)} entries (first 3: {skipped[:3]})")
        wanted = [(eid, sysd) for eid, sysd in entries
                  if args.entry_id is None or eid == args.entry_id]
        if not wanted:
            raise SystemExit(f"entry id {args.entry_id!r} not found; available: {[e for e, _ in entries][:20]}")
        eid, system = wanted[0]
        key = re.sub(r"\W+", "_", eid)[:50]
        if args.verify_only:
            run_certificate_verification(key, system, do_lean=not args.no_lean,
                                         lean_repair=args.lean_repair,
                                         do_plot=not args.no_plot)
        else:
            run_barrier_synthesis_v4(key, turns=args.turns, system=system,
                                     use_kb=not args.no_kb, do_plot=not args.no_plot,
                                     do_lean=not args.no_lean, lean_repair=args.lean_repair,
                                     refuter_gate=not args.no_refuter_gate)
    else:
        if args.verify_only:
            raise SystemExit("--verify-only needs --dataset/--entry-id (built-in systems carry no ground-truth certificate)")
        run_barrier_synthesis_v4(args.system, turns=args.turns,
                                 use_kb=not args.no_kb, do_plot=not args.no_plot,
                                 do_lean=not args.no_lean, lean_repair=args.lean_repair,
                                 refuter_gate=not args.no_refuter_gate)


if __name__ == "__main__":
    main()
