#!/usr/bin/env python3
"""
auto_expand_evolve.py — Self-evolving dataset expansion.

Integration with the self-evolution loop:
1. Load expansion manifest (lean4_expansion_v1.json)
2. For each system, attempt Lean proof using current recipe store
3. If proof fails, analyze the obstruction → candidate for new recipe mining
4. If new recipe mined → add to store (verified inequality ONLY)
5. Track: which systems proved, which need new recipes, overall coverage

KEY RULES (from user):
- Recipe store ONLY grows via verified mathematical inequalities
- No coefficient substitution (systems are genuinely different or parametric ∀α)
- Dataset expansion and recipe expansion are SEPARATE:
  * Dataset: new dynamical systems with Lean-necessary proofs
  * Recipes: new verified mathematical bridging lemmas
"""

import json, sys, time
sys.path.insert(0, "/Users/zhipeng/Desktop/paper4/6.11new")
from runtime_state import call_api, reset_tokens, TOKENS
from lean_proof import extract_lean_code, lean_compile_check
from self_evolve import _MINER_SYS, load_store

def attempt_proof(system, max_repairs=2):
    """Attempt to prove a system's Lean conditions."""
    store = load_store()
    recipes = store.get("recipes", {})

    # Build recipe injection
    recipe_text = ""
    for k, v in recipes.items():
        code = v.get("lean", "")
        if code:
            recipe_text += f"\n--- {k} ({v.get('goal','')}) ---\n```lean\n{code}\n```\n"

    prompt = f"""Prove the verification conditions for this dynamical system.

System: {system['dynamics']}
Task: {system['task']}
Certificate: {system['certificate']}
Proof strategy: {system['proof_core']}

Available verified recipes (use these Mathlib lemma names):
{recipe_text}

Write ONE complete Lean 4 file proving the key verification conditions:
- For Lyapunov: V(x*)=0, V>0 away, Vdot≤0
- For barrier: B<0 on unsafe, Bdot≥0 on boundary

Focus on the CORE algebraic/analytic conditions, not full formalization.
No sorry. Use only real Mathlib 4 lemma names from the recipes above."""

    reset_tokens()
    t0 = time.time()
    reply, _ = call_api(_MINER_SYS, [{"role": "user", "content": prompt}],
                       effort="high", label=f"{system['id']}-v1")
    code = extract_lean_code(reply)
    ok, diag = lean_compile_check(code, f"{system['id']}_v1", strict_sorry=True)
    calls = 1

    for rr in range(max_repairs):
        if ok:
            break
        calls += 1
        repair = f"Fix:\n```lean\n{code}\n```\nError: {diag[:1000]}\nNo sorry."
        reply2, _ = call_api(_MINER_SYS, [{"role": "user", "content": prompt + "\n\n---REPAIR---\n" + repair}],
                            effort="high", label=f"{system['id']}-v{calls}")
        code = extract_lean_code(reply2)
        ok, diag = lean_compile_check(code, f"{system['id']}_v{calls}", strict_sorry=True)

    dt = time.time() - t0
    tok = TOKENS["output"]

    return {
        "id": system["id"],
        "title": system["title"],
        "proved": ok,
        "calls": calls,
        "time_s": round(dt, 1),
        "tokens": tok,
        "code": code if ok else None,
        "error": diag[:300] if not ok else None,
        "verif_cond_class": system.get("verif_cond_class", "unknown"),
    }


def analyze_obstructions(results):
    """Analyze failed proofs to identify candidate recipe families."""
    obstructions = {}
    for r in results:
        if not r["proved"] and r.get("error"):
            err = r["error"]
            if "unknownIdentifier" in err:
                import re
                match = re.search(r"Unknown identifier `([^`]+)`", err)
                if match:
                    lemma = match.group(1)
                    obstructions.setdefault("hallucinated_lemma", []).append(
                        {"id": r["id"], "lemma": lemma})
            elif "failed to synthesize" in err:
                obstructions.setdefault("type_class_issue", []).append(r["id"])
            elif "linarith failed" in err or "nlinarith" in err:
                obstructions.setdefault("arithmetic_gap", []).append(r["id"])
            else:
                obstructions.setdefault("other", []).append(r["id"])
    return obstructions


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("--limit", type=int, default=5, help="Max systems to test")
    parser.add_argument("--category", type=str, default=None, help="Filter by category prefix")
    args = parser.parse_args()

    # Load expansion
    expansion = json.load(open("lean4_expansion_v1.json"))
    systems = expansion["expansion_v1"]

    if args.category:
        systems = [s for s in systems if s["id"].startswith(args.category)]

    systems = systems[:args.limit]
    print(f"Testing {len(systems)} systems from expansion set...")

    results = []
    for s in systems:
        print(f"\n{'─'*50}")
        print(f"Testing {s['id']}: {s['title']}")
        r = attempt_proof(s)
        results.append(r)
        status = "✓ PROVED" if r["proved"] else "✗ partial"
        print(f"  {status}  calls={r['calls']}  {r['time_s']}s  tok={r['tokens']}")

    # Summary
    proved = [r for r in results if r["proved"]]
    print(f"\n{'='*60}")
    print(f"EXPANSION TEST: {len(proved)}/{len(results)} proved ({100*len(proved)/len(results):.0f}%)")

    # Obstruction analysis
    obs = analyze_obstructions(results)
    if obs:
        print("\nObstruction analysis (potential new recipe targets):")
        for cat, items in obs.items():
            print(f"  {cat}: {len(items)}")
            for item in items[:3]:
                print(f"    {item}")

    # Save results
    with open("expansion_test_results.json", "w") as f:
        json.dump(results, f, indent=2, ensure_ascii=False)
    print(f"\nSaved to expansion_test_results.json")
