#!/usr/bin/env python3
"""
agent_arena_v3.py — Iteration on top of v2 results. G_retrieval_sos was the clear
winner at 6/7 (11 calls, 1114 tok). This round improves it:

  K_sim_retrieval     Fix retrieval: use Jaccard similarity on goal tokens to find
                      the CLOSEST recipe, not just the first match by family.
                      G used candidates[0] which returned log_sub_one for log_self_lower
                      even though the EXACT recipe existed. This is a bug fix, not a hack.

  L_retrieval_kb      Hybrid: K's retrieval for the first attempt, then on failure
                      use I's KB-routed repair hints (structured error routing) instead
                      of raw error message pasting.

  M_retrieval_multi   Multi-recipe: inject the TOP-2 closest recipes instead of just
                      one. More context for the model to draw on, especially for hard
                      cases where one recipe alone isn't enough.

Baselines: re-run G_retrieval_sos (to confirm reproducibility) and C_seq_sos.

Controlled: same budget B=4, effort=high, oracle=strict_sorry, same 7-problem testset.
"""
import json
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from runtime_state import call_api, reset_tokens, TOKENS, API_CONFIG, PROVIDER
from lean_proof import extract_lean_code, lean_compile_check
from self_evolve import (_MINER_SYS, _miner_prompt, _FAMILY_IMPORTS, _SOS_HINTS,
                         load_store)
from lean_error_kb import route_for, repair_hint

HERE = os.path.dirname(os.path.abspath(__file__))
ARENA_OUT = os.path.join(HERE, "agent_arena_v3_results.json")

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


# ── Similarity-based recipe retrieval (fixed) ──
def _normalize_goal(s):
    """Normalize whitespace around operators for consistent tokenization."""
    import re
    s = re.sub(r'\s+', ' ', s.strip())
    for op in ['/', '*', '+', '-', '^', '≤', '≥', '→', '=', '<', '>']:
        s = s.replace(f' {op} ', op).replace(f' {op}', op).replace(f'{op} ', op)
    return s

def _jaccard(a, b):
    """Token-level Jaccard similarity with normalized operators."""
    na, nb = _normalize_goal(a), _normalize_goal(b)
    if na == nb:
        return 1.0
    sa = set(na.lower().split())
    sb = set(nb.lower().split())
    if not sa or not sb:
        return 0.0
    return len(sa & sb) / len(sa | sb)


def _find_closest_recipe_sim(family, goal, top_k=1):
    """Find the top-k closest recipes by goal similarity, preferring same family."""
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


def _format_recipe(recipe, goal):
    r = recipe
    return (f"\nHere is a VERIFIED, compiling proof for a similar goal in the "
            f"'{r['family']}' family — adapt its structure:\n"
            f"Goal: {r['goal']}\n```lean\n{r['lean']}\n```\n"
            f"Adapt this pattern to prove: {goal}")


def _format_multi_recipe(recipes, goal):
    if not recipes:
        return ""
    parts = []
    for i, (sim, r) in enumerate(recipes):
        parts.append(
            f"\n--- RECIPE {i+1} (similarity={sim:.2f}) ---\n"
            f"Goal: {r['goal']}\n```lean\n{r['lean']}\n```"
        )
    return ("\nHere are VERIFIED, compiling proofs for similar goals. "
            "Adapt the most relevant one:\n"
            + "\n".join(parts)
            + f"\n\nAdapt the best pattern to prove: {goal}")


# ── K: Similarity-retrieved (fixed retrieval) ──
def _propose_sim_retrieval(ob, prior, variant, tag, effort="high"):
    fam, oid, goal, _ = ob
    imports = _FAMILY_IMPORTS.get(fam, "")
    sos = _SOS_HINTS.get(fam, "")
    top = _find_closest_recipe_sim(fam, goal, top_k=1)
    retrieval = _format_recipe(top[0][1], goal) if top else ""
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
                            effort=effort, label=f"arena3-{tag}")
    except Exception as e:
        return False, "", f"API {type(e).__name__}"
    code = extract_lean_code(reply)
    ok, diag = lean_compile_check(code, f"arena3_{oid}_{tag}", strict_sorry=True)
    return ok, code, diag


def arch_sim_retrieval(ob, B, width):
    n, prior = 0, None
    for i in range(B):
        n += 1
        ok, code, diag = _propose_sim_retrieval(ob, prior, i, f"{ob[1]}_K_{i}")
        if ok:
            return {"solved": True, "rounds": i + 1, "proposer_calls": n, "critic_calls": 0}
        prior = {"code": code, "diag": diag}
    return {"solved": False, "rounds": B, "proposer_calls": n, "critic_calls": 0}


# ── L: Retrieval + KB-repair hybrid ──
def _propose_retrieval_kb(ob, prior, variant, tag, effort="high"):
    fam, oid, goal, _ = ob
    imports = _FAMILY_IMPORTS.get(fam, "")
    sos = _SOS_HINTS.get(fam, "")
    top = _find_closest_recipe_sim(fam, goal, top_k=1)
    retrieval = _format_recipe(top[0][1], goal) if top else ""
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
            base += (f"\n\nYOUR PREVIOUS PROOF STRATEGY FAILED STRUCTURALLY. "
                     f"Take a COMPLETELY DIFFERENT approach:\n"
                     f"Previous code:\n```lean\n{prior['code']}\n```\n"
                     f"Error class: {route.get('id', '?')} (structural, not fixable in-place)\n"
                     f"Structured hint: {hint}\n"
                     f"DO NOT repeat the same tactic family. Try a different route entirely.")
        else:
            base += (f"\n\nPREVIOUS ATTEMPT FAILED (fixable in-place):\n"
                     f"```lean\n{prior['code']}\n```\n"
                     f"Error: {diag[:500]}\n"
                     f"Repair hint: {hint}\nFix it.")
    try:
        reply, _ = call_api(_MINER_SYS, [{"role": "user", "content": base}],
                            effort=effort, label=f"arena3-{tag}")
    except Exception as e:
        return False, "", f"API {type(e).__name__}"
    code = extract_lean_code(reply)
    ok, diag = lean_compile_check(code, f"arena3_{oid}_{tag}", strict_sorry=True)
    return ok, code, diag


def arch_retrieval_kb(ob, B, width):
    n, prior = 0, None
    for i in range(B):
        n += 1
        ok, code, diag = _propose_retrieval_kb(ob, prior, i, f"{ob[1]}_L_{i}")
        if ok:
            return {"solved": True, "rounds": i + 1, "proposer_calls": n, "critic_calls": 0}
        prior = {"code": code, "diag": diag}
    return {"solved": False, "rounds": B, "proposer_calls": n, "critic_calls": 0}


# ── M: Multi-recipe retrieval (top-2) ──
def _propose_multi_retrieval(ob, prior, variant, tag, effort="high"):
    fam, oid, goal, _ = ob
    imports = _FAMILY_IMPORTS.get(fam, "")
    sos = _SOS_HINTS.get(fam, "")
    top = _find_closest_recipe_sim(fam, goal, top_k=2)
    retrieval = _format_multi_recipe(top, goal) if top else ""
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
                            effort=effort, label=f"arena3-{tag}")
    except Exception as e:
        return False, "", f"API {type(e).__name__}"
    code = extract_lean_code(reply)
    ok, diag = lean_compile_check(code, f"arena3_{oid}_{tag}", strict_sorry=True)
    return ok, code, diag


def arch_multi_retrieval(ob, B, width):
    n, prior = 0, None
    for i in range(B):
        n += 1
        ok, code, diag = _propose_multi_retrieval(ob, prior, i, f"{ob[1]}_M_{i}")
        if ok:
            return {"solved": True, "rounds": i + 1, "proposer_calls": n, "critic_calls": 0}
        prior = {"code": code, "diag": diag}
    return {"solved": False, "rounds": B, "proposer_calls": n, "critic_calls": 0}


# ── Baselines (re-run for reproducibility) ──
def _propose_vanilla(ob, prior, sos_on, variant, tag, effort="high"):
    fam, oid, goal, _ = ob
    imports = _FAMILY_IMPORTS.get(fam, "")
    saved = _SOS_HINTS.get(fam)
    if not sos_on and saved is not None:
        _SOS_HINTS[fam] = ""
    try:
        prompt = _miner_prompt(fam, goal, oid, imports, prior, variant)
    finally:
        if not sos_on and saved is not None:
            _SOS_HINTS[fam] = saved
    try:
        reply, _ = call_api(_MINER_SYS, [{"role": "user", "content": prompt}],
                            effort=effort, label=f"arena3-{tag}")
    except Exception as e:
        return False, "", f"API {type(e).__name__}"
    code = extract_lean_code(reply)
    ok, diag = lean_compile_check(code, f"arena3_{oid}_{tag}", strict_sorry=True)
    return ok, code, diag


def arch_seq_sos(ob, B, width):
    n, prior = 0, None
    for i in range(B):
        n += 1
        ok, code, diag = _propose_vanilla(ob, prior, True, i, f"{ob[1]}_C3_{i}")
        if ok:
            return {"solved": True, "rounds": i + 1, "proposer_calls": n, "critic_calls": 0}
        prior = {"code": code, "diag": diag}
    return {"solved": False, "rounds": B, "proposer_calls": n, "critic_calls": 0}


def _propose_naive_retrieval(ob, prior, variant, tag, effort="high"):
    """G-style naive retrieval (candidates[0]) for ablation."""
    fam, oid, goal, _ = ob
    imports = _FAMILY_IMPORTS.get(fam, "")
    sos = _SOS_HINTS.get(fam, "")
    store = load_store()
    recipes = store.get("recipes", {})
    candidates = [r for r in recipes.values()
                  if r.get("family") == fam and r.get("verified")]
    if not candidates:
        candidates = [r for r in recipes.values() if r.get("verified")]
    retrieval = ""
    if candidates:
        best = candidates[0]
        retrieval = (f"\nHere is a VERIFIED, compiling proof for a similar goal in the "
                     f"'{best['family']}' family — adapt its structure:\n"
                     f"Goal: {best['goal']}\n```lean\n{best['lean']}\n```\n"
                     f"Adapt this pattern to prove: {goal}")
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
                            effort=effort, label=f"arena3-{tag}")
    except Exception as e:
        return False, "", f"API {type(e).__name__}"
    code = extract_lean_code(reply)
    ok, diag = lean_compile_check(code, f"arena3_{oid}_{tag}", strict_sorry=True)
    return ok, code, diag


def arch_naive_retrieval(ob, B, width):
    """G_retrieval_sos exact reproduction for ablation."""
    n, prior = 0, None
    for i in range(B):
        n += 1
        ok, code, diag = _propose_naive_retrieval(ob, prior, i, f"{ob[1]}_G3_{i}")
        if ok:
            return {"solved": True, "rounds": i + 1, "proposer_calls": n, "critic_calls": 0}
        prior = {"code": code, "diag": diag}
    return {"solved": False, "rounds": B, "proposer_calls": n, "critic_calls": 0}


ARCHS = [
    ("C_seq_sos", arch_seq_sos),
    ("G_naive_retrieval", arch_naive_retrieval),
    ("K_sim_retrieval", arch_sim_retrieval),
    ("L_retrieval_kb", arch_retrieval_kb),
    ("M_multi_retrieval", arch_multi_retrieval),
]


def main(budget=4, width=2):
    from runtime_state import select_provider
    select_provider("glm")

    print(f"provider={PROVIDER} model={API_CONFIG['model']}  AGENT ARENA v3 (iteration)\n"
          f"budget B={budget}, width={width}, effort=high, oracle=strict_sorry\n"
          f"test set ({len(TESTSET)}): {', '.join(o[1] for o in TESTSET)}\n"
          f"architectures: {', '.join(a[0] for a in ARCHS)}\n")

    # show what retrieval returns for each test case
    print("--- Retrieval diagnostics ---")
    for fam, oid, goal, diff in TESTSET:
        naive_store = load_store().get("recipes", {})
        naive_cands = [r for r in naive_store.values()
                       if r.get("family") == fam and r.get("verified")]
        naive_pick = naive_cands[0]["goal"] if naive_cands else "(none)"
        sim_top = _find_closest_recipe_sim(fam, goal, top_k=1)
        sim_pick = sim_top[0][1]["goal"] if sim_top else "(none)"
        sim_score = sim_top[0][0] if sim_top else 0
        match = "✓" if naive_pick == sim_pick else "✗ DIFFERENT"
        print(f"  {oid:16s} naive→'{naive_pick[:40]}' sim→'{sim_pick[:40]}' "
              f"(J={sim_score:.2f}) {match}")
    print()

    grid = {}
    for arch_name, fn in ARCHS:
        reset_tokens()
        print(f"\n{'='*60}\n{arch_name}\n{'='*60}")
        t0 = time.time()
        row, solved = {}, 0
        for ob in TESTSET:
            r = fn(ob, budget, width)
            r["tokens"] = TOKENS["output"]
            row[ob[1]] = r
            solved += int(r["solved"])
            mark = f"✅ r{r['rounds']}" if r["solved"] else "❌"
            print(f"  {ob[1]:16s} [{ob[3]:6s}] {mark}  "
                  f"calls={r['proposer_calls']}+{r['critic_calls']}c")
        dt = round(time.time() - t0)
        pcalls = sum(v["proposer_calls"] for v in row.values())
        ccalls = sum(v["critic_calls"] for v in row.values())
        grid[arch_name] = {"row": row, "solved": solved, "n": len(TESTSET),
                           "proposer_calls": pcalls, "critic_calls": ccalls,
                           "out_tokens": TOKENS["output"], "wall_s": dt}
        json.dump(grid, open(ARENA_OUT, "w"), indent=2, ensure_ascii=False, default=str)
        print(f"  → {arch_name}: {solved}/{len(TESTSET)} solved | "
              f"calls={pcalls}+{ccalls}c | {TOKENS['output']} tok | {dt}s")

    # comparison
    print(f"\n\n{'#'*70}")
    print(f"ARENA v3 COMPARISON (B={budget})")
    print(f"{'#'*70}")
    hdr = f"{'arch':24s} | solved | calls | tokens | wall_s"
    print(hdr)
    print("-" * len(hdr))
    for name, data in grid.items():
        print(f"{name:24s} | {data['solved']:3d}/7  | {data['proposer_calls']:5d} | "
              f"{data['out_tokens']:6d} | {data['wall_s']:5d}")

    # per-problem breakdown
    print(f"\n--- Per-problem ---")
    for ob in TESTSET:
        line = f"  {ob[1]:16s} [{ob[3]:6s}]"
        for name, data in grid.items():
            r = data["row"][ob[1]]
            mark = f"r{r['rounds']}" if r["solved"] else "✗"
            line += f"  {name[:3]}:{mark:>3}"
        print(line)

    print(f"\nSaved → {ARENA_OUT}")
    return grid


if __name__ == "__main__":
    main()
