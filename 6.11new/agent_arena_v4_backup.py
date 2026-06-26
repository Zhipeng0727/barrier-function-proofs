#!/usr/bin/env python3
"""
agent_arena_v4.py — Framework improvement iteration targeting:
  - Fewer API calls (M_multi champion: 8 calls for 7/7)
  - Fewer tokens (M_multi: 854)
  - Less wall-time (M_multi: 95s sequential)
  - Maintained 7/7 correctness

New architectures:

  N_parallel_multi    M_multi but problems run in ThreadPoolExecutor.
                      Same calls/tokens, dramatically less wall-time.

  O_lean_prompt       Compressed prompt: minimal system msg, single best
                      recipe only, no SOS hints boilerplate. Targets token
                      reduction while preserving retrieval benefit.

  P_hybrid_kb_multi   M + L combined: multi-recipe on first attempt,
                      KB-guided structured repair hints on retry (not raw
                      error paste). Best of both worlds for hard cases.

  Q_speculative2      For hard problems: fire 2 independent proposals in
                      parallel, take first success. Sequential for easy.
                      Trades +1 call for -1 round latency on hard problems.

Controlled: same 7-problem testset, same oracle (strict_sorry), same recipes.
"""
import json
import os
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from runtime_state import call_api, reset_tokens, TOKENS, API_CONFIG, PROVIDER
from lean_proof import extract_lean_code, lean_compile_check
from self_evolve import (_MINER_SYS, _miner_prompt, _FAMILY_IMPORTS, _SOS_HINTS,
                         load_store)
from lean_error_kb import route_for, repair_hint

HERE = os.path.dirname(os.path.abspath(__file__))
ARENA_OUT = os.path.join(HERE, "agent_arena_v4_results.json")

TESTSET = [
    ("exp", "exp_pos", "0 < Real.exp x", "easy"),
    ("trig", "sin_cos_sq", "Real.sin t ^ 2 + Real.cos t ^ 2 = 1", "easy"),
    ("log", "log_sub_one", "0 < x → Real.log x ≤ x - 1", "medium"),
    ("exp", "exp_add_one", "1 + x ≤ Real.exp x", "medium"),
    ("tanh", "tanh_sign", "0 ≤ y * Real.tanh y", "hard"),
    ("log", "log_self_lower", "0 < x → 1 - 1 / x ≤ Real.log x", "hard"),
    ("poly", "logistic_inv",
     "∀ x : ℝ, x ∈ Set.Icc (0:ℝ) 1 → 0 ≤ (38/10)*x*(1-x) ∧ (38/10)*x*(1-x) ≤ 1",
     "hard"),
]


# ── Shared utilities ──
import re

def _normalize_goal(s):
    s = re.sub(r'\s+', ' ', s.strip())
    for op in ['/', '*', '+', '-', '^', '≤', '≥', '→', '=', '<', '>']:
        s = s.replace(f' {op} ', op).replace(f' {op}', op).replace(f'{op} ', op)
    return s

def _jaccard(a, b):
    na, nb = _normalize_goal(a), _normalize_goal(b)
    if na == nb:
        return 1.0
    sa, sb = set(na.lower().split()), set(nb.lower().split())
    if not sa or not sb:
        return 0.0
    return len(sa & sb) / len(sa | sb)

def _find_closest(family, goal, top_k=1):
    store = load_store()
    recipes = store.get("recipes", {})
    scored = []
    for key, r in recipes.items():
        if not r.get("verified"):
            continue
        sim = _jaccard(goal, r.get("goal", ""))
        bonus = 0.1 if r.get("family") == family else 0.0
        scored.append((sim + bonus, r))
    scored.sort(key=lambda x: -x[0])
    return scored[:top_k]

def _format_multi(recipes, goal):
    if not recipes:
        return ""
    parts = []
    for i, (sim, r) in enumerate(recipes):
        parts.append(
            f"\n--- RECIPE {i+1} (sim={sim:.2f}) ---\n"
            f"Goal: {r['goal']}\n```lean\n{r['lean']}\n```"
        )
    return ("\nVERIFIED proofs for similar goals — adapt the most relevant:\n"
            + "\n".join(parts)
            + f"\n\nProve: {goal}")

def _format_single(recipe, goal):
    r = recipe
    return (f"\nVERIFIED proof ('{r['family']}' family) — adapt:\n"
            f"Goal: {r['goal']}\n```lean\n{r['lean']}\n```\n"
            f"Prove: {goal}")


# ══════════════════════════════════════════════════
# N: Parallel-problems M_multi (same logic, concurrent execution)
# ══════════════════════════════════════════════════

def _propose_multi(ob, prior, variant, tag, effort="high"):
    fam, oid, goal, _ = ob
    imports = _FAMILY_IMPORTS.get(fam, "")
    sos = _SOS_HINTS.get(fam, "")
    top = _find_closest(fam, goal, top_k=2)
    retrieval = _format_multi(top, goal) if top else ""
    angle = ["", "\nTry the most ELEMENTARY route.",
             "\nTry a DIFFERENT lemma than obvious.",
             "\nKeep it SHORT."][variant % 4]
    base = (
        f"Prove this Lean 4 lemma:\n\n"
        f"  GOAL ({oid}):\n  example (x y t : ℝ) : {goal} := by ...\n\n"
        f"Use these imports:\n{imports}\nimport Mathlib.Tactic\nopen Real\n\n"
        f"{sos}\n{retrieval}\n{angle}\n"
        f"Write a COMPLETE `example` that compiles. No `sorry`."
    )
    if prior:
        base += (f"\n\nPREVIOUS ATTEMPT FAILED:\n```lean\n{prior['code']}\n```\n"
                 f"Error:\n{prior['diag'][:900]}\nFix it.")
    try:
        reply, _ = call_api(_MINER_SYS, [{"role": "user", "content": base}],
                            effort=effort, label=f"arena4-{tag}")
    except Exception as e:
        return False, "", f"API {type(e).__name__}"
    code = extract_lean_code(reply)
    ok, diag = lean_compile_check(code, f"arena4_{oid}_{tag}", strict_sorry=True)
    return ok, code, diag

def _solve_multi(ob, B=4):
    prior = None
    for i in range(B):
        ok, code, diag = _propose_multi(ob, prior, i, f"{ob[1]}_N_{i}")
        if ok:
            return {"solved": True, "rounds": i + 1, "proposer_calls": i + 1, "critic_calls": 0}
        prior = {"code": code, "diag": diag}
    return {"solved": False, "rounds": B, "proposer_calls": B, "critic_calls": 0}

def arch_parallel_multi(problems, B=4, width=1):
    """N: Run each problem in a thread, M_multi strategy per problem."""
    results = {}
    with ThreadPoolExecutor(max_workers=min(len(problems), 4)) as pool:
        futures = {pool.submit(_solve_multi, ob, B): ob for ob in problems}
        for f in as_completed(futures):
            ob = futures[f]
            results[ob[1]] = f.result()
    return results


# ══════════════════════════════════════════════════
# O: Lean prompt (compressed — fewer tokens per call)
# ══════════════════════════════════════════════════

_LEAN_SYS = "You are a Lean 4 proof writer. Output ONLY a complete, compiling `example` block. No sorry."

def _propose_lean(ob, prior, variant, tag, effort="high"):
    fam, oid, goal, _ = ob
    imports = _FAMILY_IMPORTS.get(fam, "")
    top = _find_closest(fam, goal, top_k=1)
    retrieval = _format_single(top[0][1], goal) if top else f"\nProve: {goal}"
    base = (
        f"```lean\nimport Mathlib.Analysis.SpecialFunctions.Log.Basic\n"
        f"import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic\n"
        f"import Mathlib.Analysis.SpecialFunctions.ExpDeriv\n"
        f"{imports}\nimport Mathlib.Tactic\nopen Real\n\n"
        f"example (x y t : ℝ) : {goal} := by\n  sorry\n```\n"
        f"Replace `sorry` with a real proof."
        f"{retrieval}"
    )
    if prior:
        base += f"\n\nFailed attempt:\n```lean\n{prior['code']}\n```\nError: {prior['diag'][:600]}"
    try:
        reply, _ = call_api(_LEAN_SYS, [{"role": "user", "content": base}],
                            effort=effort, label=f"arena4-{tag}")
    except Exception as e:
        return False, "", f"API {type(e).__name__}"
    code = extract_lean_code(reply)
    ok, diag = lean_compile_check(code, f"arena4_{oid}_{tag}", strict_sorry=True)
    return ok, code, diag

def arch_lean_prompt(problems, B=4, width=1):
    """O: Compressed prompt, single recipe, minimal system msg."""
    results = {}
    for ob in problems:
        prior = None
        for i in range(B):
            ok, code, diag = _propose_lean(ob, prior, i, f"{ob[1]}_O_{i}")
            if ok:
                results[ob[1]] = {"solved": True, "rounds": i + 1,
                                  "proposer_calls": i + 1, "critic_calls": 0}
                break
            prior = {"code": code, "diag": diag}
        else:
            results[ob[1]] = {"solved": False, "rounds": B,
                              "proposer_calls": B, "critic_calls": 0}
    return results


# ══════════════════════════════════════════════════
# P: Hybrid KB + Multi-recipe (M + L combined)
# ══════════════════════════════════════════════════

def _propose_hybrid_kb(ob, prior, variant, tag, effort="high"):
    fam, oid, goal, _ = ob
    imports = _FAMILY_IMPORTS.get(fam, "")
    sos = _SOS_HINTS.get(fam, "")
    top = _find_closest(fam, goal, top_k=2)
    retrieval = _format_multi(top, goal) if top else ""
    angle = ["", "\nElementary route.", "\nDifferent lemma.", "\nShort proof."][variant % 4]
    base = (
        f"Prove this Lean 4 lemma:\n\n"
        f"  GOAL ({oid}):\n  example (x y t : ℝ) : {goal} := by ...\n\n"
        f"Imports:\n{imports}\nimport Mathlib.Tactic\nopen Real\n\n"
        f"{sos}\n{retrieval}\n{angle}\nNo `sorry`."
    )
    if prior:
        diag = prior["diag"]
        route = route_for(diag)
        hint = repair_hint(diag)
        route_level = route.get("route", "L1")
        if route_level == "L2":
            base += (f"\n\nSTRUCTURAL FAILURE — take a COMPLETELY DIFFERENT approach:\n"
                     f"Previous:\n```lean\n{prior['code']}\n```\n"
                     f"Error class: {route.get('id', '?')} ({route.get('title', '')})\n"
                     f"Hint: {hint}\n"
                     f"DO NOT repeat the same tactic family.")
        else:
            base += (f"\n\nFailed (fixable in-place):\n"
                     f"```lean\n{prior['code']}\n```\n"
                     f"Error: {diag[:500]}\n"
                     f"Repair: {hint}")
    try:
        reply, _ = call_api(_MINER_SYS, [{"role": "user", "content": base}],
                            effort=effort, label=f"arena4-{tag}")
    except Exception as e:
        return False, "", f"API {type(e).__name__}"
    code = extract_lean_code(reply)
    ok, diag = lean_compile_check(code, f"arena4_{oid}_{tag}", strict_sorry=True)
    return ok, code, diag

def arch_hybrid_kb_multi(problems, B=4, width=1):
    """P: Multi-recipe first attempt, KB-guided repair on retries."""
    results = {}
    for ob in problems:
        prior = None
        for i in range(B):
            ok, code, diag = _propose_hybrid_kb(ob, prior, i, f"{ob[1]}_P_{i}")
            if ok:
                results[ob[1]] = {"solved": True, "rounds": i + 1,
                                  "proposer_calls": i + 1, "critic_calls": 0}
                break
            prior = {"code": code, "diag": diag}
        else:
            results[ob[1]] = {"solved": False, "rounds": B,
                              "proposer_calls": B, "critic_calls": 0}
    return results


# ══════════════════════════════════════════════════
# Q: Speculative parallel + hybrid (full combination)
# ══════════════════════════════════════════════════

def _solve_speculative(ob, B=4):
    """Per-problem: first attempt fires 2 proposals in parallel.
    If both fail, use the one with shorter error for retry with KB."""
    fam, oid, goal, diff = ob

    # Round 1: speculative 2-way parallel
    with ThreadPoolExecutor(max_workers=2) as pool:
        f1 = pool.submit(_propose_hybrid_kb, ob, None, 0, f"{oid}_Q_0a")
        f2 = pool.submit(_propose_hybrid_kb, ob, None, 1, f"{oid}_Q_0b")
        r1 = f1.result()
        r2 = f2.result()

    calls = 2
    if r1[0]:
        return {"solved": True, "rounds": 1, "proposer_calls": calls, "critic_calls": 0}
    if r2[0]:
        return {"solved": True, "rounds": 1, "proposer_calls": calls, "critic_calls": 0}

    # Pick better failure (shorter diag = simpler error = better retry signal)
    prior = {"code": r1[1], "diag": r1[2]}
    if len(r2[2]) < len(r1[2]) and r2[1]:
        prior = {"code": r2[1], "diag": r2[2]}

    # Rounds 2+: sequential with KB-guided repair
    for i in range(1, B):
        calls += 1
        ok, code, diag = _propose_hybrid_kb(ob, prior, i + 1, f"{oid}_Q_{i}")
        if ok:
            return {"solved": True, "rounds": i + 1, "proposer_calls": calls, "critic_calls": 0}
        prior = {"code": code, "diag": diag}
    return {"solved": False, "rounds": B, "proposer_calls": calls, "critic_calls": 0}

def arch_speculative_hybrid(problems, B=4, width=1):
    """Q: Parallel problems + speculative first round + KB repair."""
    results = {}
    with ThreadPoolExecutor(max_workers=min(len(problems), 4)) as pool:
        futures = {pool.submit(_solve_speculative, ob, B): ob for ob in problems}
        for f in as_completed(futures):
            ob = futures[f]
            results[ob[1]] = f.result()
    return results


# ══════════════════════════════════════════════════
# R: Adaptive difficulty-aware (minimal prompt for easy, full for hard)
# ══════════════════════════════════════════════════

_MINIMAL_SYS = "You write Lean 4 proofs. Output ONLY a compiling `example` block. No sorry."

def _propose_adaptive(ob, prior, variant, tag, effort="high"):
    fam, oid, goal, diff = ob
    imports = _FAMILY_IMPORTS.get(fam, "")

    if diff == "easy" and prior is None:
        # Minimal prompt: just goal + single best recipe
        top = _find_closest(fam, goal, top_k=1)
        retrieval = _format_single(top[0][1], goal) if top else ""
        base = (
            f"import Mathlib.Analysis.SpecialFunctions.Log.Basic\n"
            f"import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic\n"
            f"import Mathlib.Analysis.SpecialFunctions.ExpDeriv\n"
            f"{imports}\nimport Mathlib.Tactic\nopen Real\n\n"
            f"example (x y t : ℝ) : {goal} := by\n  sorry\n\n"
            f"Replace sorry with real proof.{retrieval}"
        )
        sys_msg = _MINIMAL_SYS
    else:
        # Full prompt with multi-recipe + SOS + KB repair
        sos = _SOS_HINTS.get(fam, "")
        top_k = 2 if diff == "hard" else 1
        top = _find_closest(fam, goal, top_k=top_k)
        if top_k == 2:
            retrieval = _format_multi(top, goal) if top else ""
        else:
            retrieval = _format_single(top[0][1], goal) if top else ""
        angle = ["", "\nElementary route.", "\nDifferent lemma.", "\nShort proof."][variant % 4]
        base = (
            f"Prove this Lean 4 lemma:\n\n"
            f"  GOAL ({oid}):\n  example (x y t : ℝ) : {goal} := by ...\n\n"
            f"Imports:\n{imports}\nimport Mathlib.Tactic\nopen Real\n\n"
            f"{sos}\n{retrieval}\n{angle}\nNo `sorry`."
        )
        sys_msg = _MINER_SYS
        if prior:
            diag = prior["diag"]
            route = route_for(diag)
            hint = repair_hint(diag)
            if route.get("route") == "L2":
                base += (f"\n\nSTRUCTURAL FAILURE — different approach:\n"
                         f"```lean\n{prior['code']}\n```\n"
                         f"Error: {route.get('id', '?')}\nHint: {hint}\n"
                         f"Use a DIFFERENT tactic family.")
            else:
                base += (f"\n\nFailed:\n```lean\n{prior['code']}\n```\n"
                         f"Error: {diag[:500]}\nRepair: {hint}")
    try:
        reply, _ = call_api(sys_msg, [{"role": "user", "content": base}],
                            effort=effort, label=f"arena4-{tag}")
    except Exception as e:
        return False, "", f"API {type(e).__name__}"
    code = extract_lean_code(reply)
    ok, diag = lean_compile_check(code, f"arena4_{oid}_{tag}", strict_sorry=True)
    return ok, code, diag

def _solve_adaptive(ob):
    _, _, _, diff = ob
    B = {"easy": 2, "medium": 3, "hard": 5}[diff]
    prior = None
    for i in range(B):
        ok, code, diag = _propose_adaptive(ob, prior, i, f"{ob[1]}_R_{i}")
        if ok:
            return {"solved": True, "rounds": i + 1, "proposer_calls": i + 1, "critic_calls": 0}
        prior = {"code": code, "diag": diag}
    return {"solved": False, "rounds": B, "proposer_calls": B, "critic_calls": 0}

def arch_adaptive(problems, B=4, width=1):
    """R: Adaptive per-difficulty, parallel execution, KB repair on retry."""
    results = {}
    with ThreadPoolExecutor(max_workers=min(len(problems), 4)) as pool:
        futures = {pool.submit(_solve_adaptive, ob): ob for ob in problems}
        for f in as_completed(futures):
            ob = futures[f]
            results[ob[1]] = f.result()
    return results


# ══════════════════════════════════════════════════
# Runner
# ══════════════════════════════════════════════════

ARCHITECTURES = {
    "N_parallel_multi":     arch_parallel_multi,
    "O_lean_prompt":        arch_lean_prompt,
    "P_hybrid_kb_multi":    arch_hybrid_kb_multi,
    "Q_speculative_hybrid": arch_speculative_hybrid,
    "R_adaptive":           arch_adaptive,
}

def run_arena(arch_names=None, B=4):
    arch_names = arch_names or list(ARCHITECTURES.keys())
    all_results = {}

    for name in arch_names:
        fn = ARCHITECTURES[name]
        print(f"\n{'='*60}")
        print(f"  Running: {name}  (B={B}, {len(TESTSET)} problems)")
        print(f"{'='*60}")
        reset_tokens()
        t0 = time.time()

        row = fn(TESTSET, B=B)

        wall = time.time() - t0
        solved = sum(1 for v in row.values() if v["solved"])
        calls = sum(v["proposer_calls"] for v in row.values())
        out_tok = TOKENS["output"]

        all_results[name] = {
            "solved": solved,
            "n": len(TESTSET),
            "proposer_calls": calls,
            "out_tokens": out_tok,
            "wall_s": round(wall, 1),
            "row": row,
        }
        print(f"  → {solved}/{len(TESTSET)}  calls={calls}  tok={out_tok}  wall={wall:.1f}s")
        for prob, pd in row.items():
            status = "✓" if pd["solved"] else "✗"
            print(f"    {prob:20s} {status}  rounds={pd['rounds']}")

    with open(ARENA_OUT, "w") as f:
        json.dump(all_results, f, indent=2, ensure_ascii=False)
    print(f"\nResults saved → {ARENA_OUT}")
    return all_results


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("--arch", nargs="*", help="architectures to run")
    parser.add_argument("--budget", type=int, default=4)
    args = parser.parse_args()
    run_arena(args.arch, B=args.budget)
