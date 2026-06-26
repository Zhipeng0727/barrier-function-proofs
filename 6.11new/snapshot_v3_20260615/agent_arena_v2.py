#!/usr/bin/env python3
"""
agent_arena_v2.py — EXTENDED controlled comparison with 4 new architectures on top
of the original 6 (A–F). Each new architecture targets a specific weakness found
in the v1 arena:

  G_retrieval_sos     Recipe-retrieval augmented: inject the CLOSEST verified recipe
                      (from recipe_store.json) as a template, not just the family hint.
                      Hypothesis: a concrete working proof is a stronger anchor than
                      abstract lemma names.

  H_cot_sos           Chain-of-thought: first call asks GLM to PLAN the proof strategy
                      (which lemma, which tactic family, why), second call writes code
                      given the plan. Hypothesis: reasoning-first reduces hallucination.

  I_kb_repair_sos     Error-KB-routed repair: instead of feeding raw diagnostics back,
                      route through lean_error_kb to get a structured repair hint with
                      the correct fix category (L1 in-place / L2 new strategy).
                      Hypothesis: structured repair > raw error pasting.

  J_progressive_sos   Progressive disclosure: round 1 attempts WITHOUT hints (forces
                      the model to think); only rounds 2+ get hints. If round 1 fails,
                      the hint explains what was tried AND what to use instead.
                      Hypothesis: teaching > telling (avoid hint-dependence).

Controlled variables: same as v1 (budget, effort, oracle, testset).
Run: python3 agent_arena_v2.py --budget 4 --width 2
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
ARENA_OUT = os.path.join(HERE, "agent_arena_v2_results.json")

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


# ── shared propose primitive (same as v1 for fair comparison) ──
def _propose(ob, prior, sos_on, variant, tag, effort="high"):
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
                            effort=effort, label=f"arena2-{tag}")
    except Exception as e:
        return False, "", f"API {type(e).__name__}"
    code = extract_lean_code(reply)
    ok, diag = lean_compile_check(code, f"arena2_{oid}_{tag}", strict_sorry=True)
    return ok, code, diag


def _carry(results):
    fails = [r for r in results if r and r[1]]
    if not fails:
        return None
    best = max(fails, key=lambda r: len(r[2] or ""))
    return {"code": best[1], "diag": best[2] or ""}


# ── G: Retrieval-augmented (inject closest verified recipe as template) ──
def _find_closest_recipe(family, goal):
    store = load_store()
    recipes = store.get("recipes", {})
    candidates = []
    for key, r in recipes.items():
        if r.get("family") == family and r.get("verified"):
            candidates.append(r)
    if not candidates:
        for key, r in recipes.items():
            if r.get("verified"):
                candidates.append(r)
    if not candidates:
        return ""
    best = candidates[0]
    return (f"\nHere is a VERIFIED, compiling proof for a similar goal in the "
            f"'{best['family']}' family — adapt its structure:\n"
            f"Goal: {best['goal']}\n```lean\n{best['lean']}\n```\n"
            f"Adapt this pattern to prove: {goal}")


def _propose_retrieval(ob, prior, variant, tag, effort="high"):
    fam, oid, goal, _ = ob
    imports = _FAMILY_IMPORTS.get(fam, "")
    sos = _SOS_HINTS.get(fam, "")
    retrieval = _find_closest_recipe(fam, goal)
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
                            effort=effort, label=f"arena2-{tag}")
    except Exception as e:
        return False, "", f"API {type(e).__name__}"
    code = extract_lean_code(reply)
    ok, diag = lean_compile_check(code, f"arena2_{oid}_{tag}", strict_sorry=True)
    return ok, code, diag


def arch_retrieval_sos(ob, B, width):
    n, prior = 0, None
    for i in range(B):
        n += 1
        ok, code, diag = _propose_retrieval(ob, prior, i, f"{ob[1]}_G_{i}")
        if ok:
            return {"solved": True, "rounds": i + 1, "proposer_calls": n, "critic_calls": 0}
        prior = {"code": code, "diag": diag}
    return {"solved": False, "rounds": B, "proposer_calls": n, "critic_calls": 0}


# ── H: Chain-of-thought (plan then code) ──
_COT_PLANNER_SYS = (
    "You are a Lean 4 proof STRATEGIST. Given a goal, you output a 3-step PLAN: "
    "(1) which Mathlib lemma or tactic is the key step, (2) what intermediate goals "
    "appear after applying it, (3) how to close each subgoal. "
    "Do NOT write Lean code — just the strategy in plain text, 3-5 sentences max."
)

_COT_CODER_SYS = (
    "You are a Lean 4 coder. Given a goal AND a proof strategy, write the COMPLETE "
    "Lean 4 proof that implements the strategy. Output ONLY one ```lean code block. "
    "No `sorry`. Use exact Mathlib lemma names from the strategy."
)


def _propose_cot(ob, prior, variant, tag, effort="high"):
    fam, oid, goal, _ = ob
    imports = _FAMILY_IMPORTS.get(fam, "")
    sos = _SOS_HINTS.get(fam, "")
    plan_prompt = (
        f"Goal: example (x y t : ℝ) : {goal} := by ...\n"
        f"Family: {fam}\n{sos}\n\nWhat is the proof strategy? 3-5 sentences."
    )
    if prior:
        plan_prompt += (f"\n\nA previous attempt FAILED:\n```lean\n{prior['code']}\n```\n"
                        f"Error: {prior['diag'][:600]}\nAvoid this mistake in your plan.")
    try:
        plan, _ = call_api(_COT_PLANNER_SYS,
                           [{"role": "user", "content": plan_prompt}],
                           effort=effort, label=f"arena2-plan-{tag}")
    except Exception:
        return False, "", "plan API error"

    code_prompt = (
        f"Implement this proof in Lean 4:\n\n"
        f"GOAL: example (x y t : ℝ) : {goal} := by ...\n\n"
        f"IMPORTS:\n{imports}\nimport Mathlib.Tactic\nopen Real\n\n"
        f"PROOF STRATEGY:\n{plan}\n\n"
        f"Write the COMPLETE `example` that compiles. Follow the strategy exactly."
    )
    try:
        reply, _ = call_api(_COT_CODER_SYS,
                            [{"role": "user", "content": code_prompt}],
                            effort=effort, label=f"arena2-code-{tag}")
    except Exception as e:
        return False, "", f"API {type(e).__name__}"
    code = extract_lean_code(reply)
    ok, diag = lean_compile_check(code, f"arena2_{oid}_{tag}", strict_sorry=True)
    return ok, code, diag


def arch_cot_sos(ob, B, width):
    n, prior = 0, None
    rounds = B // 2  # each round uses 2 calls (plan + code)
    for i in range(max(1, rounds)):
        n += 2
        ok, code, diag = _propose_cot(ob, prior, i, f"{ob[1]}_H_{i}")
        if ok:
            return {"solved": True, "rounds": i + 1, "proposer_calls": n, "critic_calls": 0}
        prior = {"code": code, "diag": diag}
    return {"solved": False, "rounds": max(1, rounds), "proposer_calls": n, "critic_calls": 0}


# ── I: KB-routed repair (structured repair hints from lean_error_kb) ──
def _propose_kb_repair(ob, prior, sos_on, variant, tag, effort="high"):
    fam, oid, goal, _ = ob
    imports = _FAMILY_IMPORTS.get(fam, "")
    sos = _SOS_HINTS.get(fam, "") if sos_on else ""
    angle = ["", "\nElementary route.", "\nDifferent lemma.", "\nShort proof."][variant % 4]
    base = (
        f"Prove this Lean 4 lemma:\n\n"
        f"  GOAL ({oid}):\n  example (x y t : ℝ) : {goal} := by ...\n\n"
        f"Imports:\n{imports}\nimport Mathlib.Tactic\nopen Real\n\n"
        f"{sos}{angle}\nNo `sorry`."
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
                     f"Repair hint: {hint}\n"
                     f"Fix the specific error. Keep the overall proof structure.")
    try:
        reply, _ = call_api(_MINER_SYS, [{"role": "user", "content": base}],
                            effort=effort, label=f"arena2-{tag}")
    except Exception as e:
        return False, "", f"API {type(e).__name__}"
    code = extract_lean_code(reply)
    ok, diag = lean_compile_check(code, f"arena2_{oid}_{tag}", strict_sorry=True)
    return ok, code, diag


def arch_kb_repair_sos(ob, B, width):
    n, prior = 0, None
    for i in range(B):
        n += 1
        ok, code, diag = _propose_kb_repair(ob, prior, True, i, f"{ob[1]}_I_{i}")
        if ok:
            return {"solved": True, "rounds": i + 1, "proposer_calls": n, "critic_calls": 0}
        prior = {"code": code, "diag": diag}
    return {"solved": False, "rounds": B, "proposer_calls": n, "critic_calls": 0}


# ── J: Progressive disclosure (no hints round 1, hints from round 2) ──
def arch_progressive_sos(ob, B, width):
    n, prior = 0, None
    for i in range(B):
        n += 1
        sos_on = (i >= 1)  # round 0: no hints; round 1+: hints
        ok, code, diag = _propose(ob, prior, sos_on, i, f"{ob[1]}_J_{i}")
        if ok:
            return {"solved": True, "rounds": i + 1, "proposer_calls": n, "critic_calls": 0}
        if i == 0 and not ok:
            prior = {"code": code,
                     "diag": (diag or "") + "\n\nNow use the VERIFIED hints below to fix it."}
        else:
            prior = {"code": code, "diag": diag}
    return {"solved": False, "rounds": B, "proposer_calls": n, "critic_calls": 0}


# ── Also re-run the best v1 architectures for fair comparison ──
def _sequential(ob, B, sos_on, tagc):
    n, prior = 0, None
    for i in range(B):
        n += 1
        ok, code, diag = _propose(ob, prior, sos_on, i, f"{ob[1]}_{tagc}_{i}")
        if ok:
            return {"solved": True, "rounds": i + 1, "proposer_calls": n, "critic_calls": 0}
        prior = {"code": code, "diag": diag}
    return {"solved": False, "rounds": B, "proposer_calls": n, "critic_calls": 0}


def arch_seq_sos(ob, B, width):
    return _sequential(ob, B, True, "C2")


def _parallel(ob, B, width, sos_on, tagc):
    n, prior = 0, None
    rounds = max(1, B // width)
    for rnd in range(rounds):
        results = [None] * width
        with ThreadPoolExecutor(max_workers=width) as ex:
            futs = {ex.submit(_propose, ob, prior, sos_on, rnd * width + v,
                              f"{ob[1]}_{tagc}_r{rnd}c{v}"): v for v in range(width)}
            for fut in as_completed(futs):
                results[futs[fut]] = fut.result()
        n += width
        win = next((r for r in results if r and r[0]), None)
        if win:
            return {"solved": True, "rounds": rnd + 1, "proposer_calls": n, "critic_calls": 0}
        prior = _carry(results)
    return {"solved": False, "rounds": rounds, "proposer_calls": n, "critic_calls": 0}


def arch_parallel_sos(ob, B, width):
    return _parallel(ob, B, width, True, "E2")


ARCHS = [
    ("C_seq_sos", arch_seq_sos),
    ("E_parallel_sos", arch_parallel_sos),
    ("G_retrieval_sos", arch_retrieval_sos),
    ("H_cot_sos", arch_cot_sos),
    ("I_kb_repair_sos", arch_kb_repair_sos),
    ("J_progressive_sos", arch_progressive_sos),
]


def main(budget=4, width=2):
    print(f"provider={PROVIDER} model={API_CONFIG['model']}  AGENT ARENA v2\n"
          f"budget B={budget}, width={width}, effort=high, oracle=strict_sorry\n"
          f"test set ({len(TESTSET)}): {', '.join(o[1] for o in TESTSET)}\n"
          f"architectures: {', '.join(a[0] for a in ARCHS)}\n")

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

    # comparison matrix
    print(f"\n\n{'#'*70}")
    print(f"CONTROLLED COMPARISON v2 (B={budget}, width={width})")
    print(f"{'#'*70}")
    oids = [o[1] for o in TESTSET]
    hdr = "arch".ljust(20) + "".join(f"{o[:10]:>11s}" for o in oids) + "  solve  tok  wall"
    print(hdr)
    print("-" * len(hdr))
    for arch_name, _ in ARCHS:
        g = grid[arch_name]
        cells = ""
        for oid in oids:
            r = g["row"][oid]
            cells += f"{'r'+str(r['rounds']) if r['solved'] else '·':>11s}"
        print(f"{arch_name:20s}{cells}   {g['solved']}/{g['n']}  "
              f"{g['out_tokens']:>5} {g['wall_s']:>4}s")

    print("\nRanking (solve-rate, then fewer calls, then fewer tokens):")
    ranked = sorted(ARCHS, key=lambda a: (-grid[a[0]]["solved"],
                    grid[a[0]]["proposer_calls"], grid[a[0]]["out_tokens"]))
    for i, (arch_name, _) in enumerate(ranked, 1):
        g = grid[arch_name]
        print(f"  {i}. {arch_name:20s} {g['solved']}/{g['n']} solved | "
              f"{g['proposer_calls']}+{g['critic_calls']}c calls | "
              f"{g['out_tokens']} tok | {g['wall_s']}s")

    # merge with v1 results for combined table
    v1_path = os.path.join(HERE, "agent_arena_results.json")
    if os.path.exists(v1_path):
        v1 = json.load(open(v1_path))
        combined = {**v1, **grid}
        combined_path = os.path.join(HERE, "agent_arena_combined.json")
        json.dump(combined, open(combined_path, "w"), indent=2, ensure_ascii=False, default=str)
        print(f"\nCombined v1+v2 → {combined_path}")
        print("\nFULL RANKING (10 architectures):")
        all_archs = sorted(combined.items(), key=lambda x: (-x[1]["solved"],
                           x[1]["proposer_calls"], x[1]["out_tokens"]))
        for i, (name, g) in enumerate(all_archs, 1):
            print(f"  {i}. {name:20s} {g['solved']}/{g['n']} | "
                  f"{g['proposer_calls']}+{g['critic_calls']}c | "
                  f"{g['out_tokens']} tok | {g['wall_s']}s")

    print(f"\nSaved → {ARENA_OUT}")
    return grid


if __name__ == "__main__":
    B = int(sys.argv[sys.argv.index("--budget") + 1]) if "--budget" in sys.argv else 4
    W = int(sys.argv[sys.argv.index("--width") + 1]) if "--width" in sys.argv else 2
    main(B, W)
