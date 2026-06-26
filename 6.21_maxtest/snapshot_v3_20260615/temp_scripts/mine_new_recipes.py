#!/usr/bin/env python3
"""Mine 3 new recipe families: rational, convex_combination, convex (log-sum-exp)."""

import sys, json, time
sys.path.insert(0, "/Users/zhipeng/Desktop/paper4/6.11new")
from runtime_state import call_api, reset_tokens, TOKENS
from lean_proof import extract_lean_code, lean_compile_check
from self_evolve import _MINER_SYS, load_store, save_store

store = load_store()
recipes = store.get("recipes", {})

def mine_recipe(recipe_id, family, obstruction, goal, desc, prompt, max_attempts=3):
    """Mine a single recipe with repair loop."""
    print(f"\n{'='*60}")
    print(f"Mining: {recipe_id} ({goal})")
    reset_tokens()
    t0 = time.time()

    reply, _ = call_api(_MINER_SYS, [{"role": "user", "content": prompt}], effort="high", label=f"{recipe_id}-v1")
    code = extract_lean_code(reply)
    ok, diag = lean_compile_check(code, f"{recipe_id}_v1", strict_sorry=True)
    rounds = 1

    for rr in range(max_attempts - 1):
        if ok:
            break
        rounds += 1
        repair = f"""Fix this Lean 4 proof:
```lean
{code}
```
Compiler error:
{diag[:1500]}
Rules: No sorry. Only use real Mathlib 4 lemma names. Check exact types carefully."""
        reply2, _ = call_api(_MINER_SYS, [{"role": "user", "content": prompt + "\n\n--- REPAIR ---\n" + repair}],
                            effort="high", label=f"{recipe_id}-v{rounds}")
        code = extract_lean_code(reply2)
        ok, diag = lean_compile_check(code, f"{recipe_id}_v{rounds}", strict_sorry=True)

    dt = time.time() - t0
    tok = TOKENS["output"]
    status = "PASS" if ok else "FAIL"
    print(f"  {status}  rounds={rounds}  {dt:.0f}s  tok={tok}")

    if ok:
        recipes[recipe_id] = {
            "family": family,
            "obstruction": obstruction,
            "goal": goal,
            "desc": desc,
            "lean": code,
            "verified": True,
            "rounds": rounds,
            "out_tokens": tok
        }
        store["recipes"] = recipes
        save_store(store)
        print(f"  Saved to recipe_store.json")
    else:
        print(f"  FAILED: {diag[:300]}")

    return ok, code


# ═══ Family 1: rational ═══
# For L1-006 / B1-017: x/(1-x) expressions, need division safety lemmas

mine_recipe(
    "rational.div_pos_of_pos",
    "rational", "div_pos",
    "0 < a → 0 < b → 0 < a / b",
    "Division of positives is positive",
    """Write a Lean 4 proof of: for real numbers a, b, if 0 < a and 0 < b then 0 < a / b.

```lean
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < a / b := by
  exact div_pos ha hb
```

Verify this compiles. Write ONE complete Lean 4 file. No sorry."""
)

mine_recipe(
    "rational.div_le_one",
    "rational", "div_le_one",
    "0 < b → a ≤ b → a / b ≤ 1",
    "Ratio ≤ 1 when numerator ≤ denominator (both positive)",
    """Write a Lean 4 proof: for reals a, b with 0 < b and a ≤ b, show a / b ≤ 1.

Use `div_le_one` from Mathlib. Write ONE complete Lean 4 file. No sorry.

```lean
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

example (a b : ℝ) (hb : 0 < b) (h : a ≤ b) : a / b ≤ 1 := by
  exact div_le_one_of_le h (le_of_lt hb)
```
"""
)

mine_recipe(
    "rational.sq_div_sq",
    "rational", "sq_div_sq",
    "0 < b → (a / b) ^ 2 = a ^ 2 / b ^ 2",
    "Square distributes over division",
    """Write a Lean 4 proof: for reals a, b with b ≠ 0, (a/b)^2 = a^2/b^2.

Use `div_pow` from Mathlib. Write ONE complete Lean 4 file. No sorry.

```lean
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

example (a b : ℝ) : (a / b) ^ 2 = a ^ 2 / b ^ 2 := by
  exact div_pow a b 2
```
"""
)

mine_recipe(
    "rational.one_sub_div",
    "rational", "one_sub_div",
    "b ≠ 0 → 1 - a / b = (b - a) / b",
    "1 - a/b = (b-a)/b for nonzero denominator",
    """Write a Lean 4 proof: for reals a, b with b ≠ 0, 1 - a/b = (b - a) / b.

This is useful for barrier certificates like B = 1 - (x/(1-x))^2.

Write ONE complete Lean 4 file. No sorry. Try `field_simp` then `ring`."""
)


# ═══ Family 2: convex_combination ═══
# For L7-003: convex combo lies between min and max

mine_recipe(
    "convex.weighted_avg_le_max",
    "convex", "weighted_avg_le_max",
    "0 ≤ w₁ → 0 ≤ w₂ → w₁ + w₂ = 1 → w₁*a + w₂*b ≤ max a b",
    "Convex combination of two values ≤ max",
    """Write a Lean 4 proof: for reals w1, w2, a, b with 0 ≤ w1, 0 ≤ w2, w1+w2=1,
show w1*a + w2*b ≤ max a b.

Proof idea: max a b ≥ a and max a b ≥ b, so
w1*a + w2*b ≤ w1*(max a b) + w2*(max a b) = (w1+w2)*(max a b) = max a b.

Write ONE complete Lean 4 file. No sorry. Use `le_max_left`, `le_max_right`, `nlinarith`."""
)

mine_recipe(
    "convex.weighted_avg_ge_min",
    "convex", "weighted_avg_ge_min",
    "0 ≤ w₁ → 0 ≤ w₂ → w₁ + w₂ = 1 → min a b ≤ w₁*a + w₂*b",
    "min ≤ convex combination of two values",
    """Write a Lean 4 proof: for reals w1, w2, a, b with 0 ≤ w1, 0 ≤ w2, w1+w2=1,
show min a b ≤ w1*a + w2*b.

Proof idea: min a b ≤ a and min a b ≤ b, so
w1*(min a b) + w2*(min a b) ≤ w1*a + w2*b, and LHS = min a b.

Write ONE complete Lean 4 file. No sorry. Use `min_le_left`, `min_le_right`, `nlinarith`."""
)

mine_recipe(
    "convex.three_weighted_le_max",
    "convex", "three_weighted_le_max",
    "0≤w₁ → 0≤w₂ → 0≤w₃ → w₁+w₂+w₃=1 → w₁*a+w₂*b+w₃*c ≤ max a (max b c)",
    "Convex combination of three values ≤ max",
    """Write a Lean 4 proof: for reals w1,w2,w3,a,b,c with 0≤wi and w1+w2+w3=1,
show w1*a + w2*b + w3*c ≤ max a (max b c).

Proof: let M = max a (max b c). Then a ≤ M, b ≤ M, c ≤ M.
So w1*a + w2*b + w3*c ≤ w1*M + w2*M + w3*M = M.

Use `le_max_left`, `le_max_of_le_right (le_max_left b c)`, `le_max_of_le_right (le_max_right b c)`, and `nlinarith`.

Write ONE complete Lean 4 file. No sorry."""
)


# ═══ Family 3: log-sum-exp / Jensen ═══
# For L7-001: need log(sum exp) inequality

mine_recipe(
    "convex.log_sum_two_le",
    "convex", "log_sum_two",
    "0 < a → 0 < b → a + b ≤ 1 → Real.log (a + b) ≤ 0",
    "log of sub-unit sum is nonpositive",
    """Write a Lean 4 proof: for reals a, b with 0 < a, 0 < b, a + b ≤ 1,
show Real.log (a + b) ≤ 0.

Proof: a + b ≤ 1, and log is monotone, so log(a+b) ≤ log(1) = 0.

Use `Real.log_nonpos` or `Real.log_le_log` + `Real.log_one`.

Write ONE complete Lean 4 file. No sorry."""
)

mine_recipe(
    "convex.exp_sum_bound",
    "convex", "exp_sum_bound",
    "Real.exp a + Real.exp b ≥ 2",
    "Sum of two exponentials ≥ 2 (AM-GM consequence)",
    """Write a Lean 4 proof: for all reals a, b with a + b = 0,
exp(a) + exp(b) ≥ 2.

Proof: By AM-GM, (exp(a) + exp(b))/2 ≥ sqrt(exp(a)*exp(b)) = sqrt(exp(a+b)) = sqrt(exp(0)) = 1.
So exp(a) + exp(b) ≥ 2.

Alternative: use exp(a) ≥ 1 + a and exp(b) ≥ 1 + b (from `add_one_le_exp`), sum them:
exp(a) + exp(b) ≥ 2 + a + b = 2 + 0 = 2.

Write ONE complete Lean 4 file. No sorry. Use `add_one_le_exp` from Mathlib."""
)


# ═══ Print summary ═══
print("\n" + "="*60)
print("RECIPE MINING SUMMARY")
print("="*60)
store2 = load_store()
total = len(store2.get("recipes", {}))
new_families = {}
for k, v in store2.get("recipes", {}).items():
    fam = v["family"]
    if fam in ("rational", "convex"):
        new_families.setdefault(fam, []).append(k)

print(f"Total recipes: {total}")
for fam, keys in new_families.items():
    print(f"  {fam}: {len(keys)} recipes — {keys}")
