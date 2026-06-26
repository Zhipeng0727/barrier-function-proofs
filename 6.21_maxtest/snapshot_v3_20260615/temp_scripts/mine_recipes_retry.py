#!/usr/bin/env python3
"""Retry failed recipes with better prompts."""

import sys, json, time
sys.path.insert(0, "/Users/zhipeng/Desktop/paper4/6.11new")
from runtime_state import call_api, reset_tokens, TOKENS
from lean_proof import extract_lean_code, lean_compile_check
from self_evolve import _MINER_SYS, load_store, save_store

store = load_store()
recipes = store.get("recipes", {})

def mine_recipe(recipe_id, family, obstruction, goal, desc, prompt, max_attempts=4):
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
No sorry. Only use real Mathlib 4 lemma names."""
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
            "family": family, "obstruction": obstruction,
            "goal": goal, "desc": desc, "lean": code,
            "verified": True, "rounds": rounds, "out_tokens": tok
        }
        store["recipes"] = recipes
        save_store(store)
        print(f"  Saved to recipe_store.json")
    else:
        print(f"  FAILED: {diag[:400]}")
    return ok, code


# ---- rational.div_le_one ----
mine_recipe(
    "rational.div_le_one", "rational", "div_le_one",
    "0 < b → a ≤ b → a / b ≤ 1",
    "Ratio ≤ 1 when numerator ≤ denominator",
    """Prove in Lean 4: for reals a b, 0 < b → a ≤ b → a / b ≤ 1.

The correct approach:
```lean
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

example (a b : ℝ) (hb : 0 < b) (h : a ≤ b) : a / b ≤ 1 := by
  rw [div_le_iff hb]
  linarith [one_mul b]
```

Or use `div_le_one_of_le h (le_of_lt hb)` if available.
Write ONE complete Lean 4 file. No sorry."""
)

# ---- rational.one_sub_div ----
mine_recipe(
    "rational.one_sub_div", "rational", "one_sub_div",
    "b ≠ 0 → 1 - a / b = (b - a) / b",
    "1 - a/b = (b-a)/b",
    """Prove in Lean 4: for reals a b with b ≠ 0, (1 : ℝ) - a / b = (b - a) / b.

Key: use `field_simp` to clear denominators, then `ring`.

```lean
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

example (a b : ℝ) (hb : b ≠ 0) : (1 : ℝ) - a / b = (b - a) / b := by
  field_simp
  ring
```

Write ONE complete Lean 4 file. No sorry. Make sure numeric literals have type annotation `(1 : ℝ)`."""
)

# ---- convex.weighted_avg_le_max ----
# The key: nlinarith needs explicit witnesses like mul_le_mul_of_nonneg_left
mine_recipe(
    "convex.weighted_avg_le_max", "convex", "weighted_avg_le_max",
    "0 ≤ w₁ → 0 ≤ w₂ → w₁ + w₂ = 1 → w₁*a + w₂*b ≤ max a b",
    "Convex combination ≤ max of two values",
    """Prove in Lean 4: for reals w1 w2 a b, if 0 ≤ w1, 0 ≤ w2, w1+w2=1,
then w1*a + w2*b ≤ max a b.

KEY PROOF STRATEGY: Let M = max a b. Then a ≤ M and b ≤ M.
Since w1 ≥ 0: w1*a ≤ w1*M (by `mul_le_mul_of_nonneg_left`)
Since w2 ≥ 0: w2*b ≤ w2*M (by `mul_le_mul_of_nonneg_left`)
Adding: w1*a + w2*b ≤ w1*M + w2*M = (w1+w2)*M = M.

```lean
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

example (w1 w2 a b : ℝ) (h1 : 0 ≤ w1) (h2 : 0 ≤ w2) (h3 : w1 + w2 = 1) :
    w1 * a + w2 * b ≤ max a b := by
  have ha : a ≤ max a b := le_max_left a b
  have hb : b ≤ max a b := le_max_right a b
  have s1 : w1 * a ≤ w1 * max a b := mul_le_mul_of_nonneg_left ha h1
  have s2 : w2 * b ≤ w2 * max a b := mul_le_mul_of_nonneg_left hb h2
  nlinarith
```

Write ONE complete Lean 4 file. No sorry."""
)

# ---- convex.weighted_avg_ge_min ----
mine_recipe(
    "convex.weighted_avg_ge_min", "convex", "weighted_avg_ge_min",
    "0 ≤ w₁ → 0 ≤ w₂ → w₁ + w₂ = 1 → min a b ≤ w₁*a + w₂*b",
    "min ≤ convex combination of two values",
    """Prove in Lean 4: for reals w1 w2 a b, if 0 ≤ w1, 0 ≤ w2, w1+w2=1,
then min a b ≤ w1*a + w2*b.

KEY: Let m = min a b. Then m ≤ a and m ≤ b.
w1*m ≤ w1*a and w2*m ≤ w2*b (by mul_le_mul_of_nonneg_left).
Adding: m = (w1+w2)*m = w1*m + w2*m ≤ w1*a + w2*b.

```lean
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

example (w1 w2 a b : ℝ) (h1 : 0 ≤ w1) (h2 : 0 ≤ w2) (h3 : w1 + w2 = 1) :
    min a b ≤ w1 * a + w2 * b := by
  have ha : min a b ≤ a := min_le_left a b
  have hb : min a b ≤ b := min_le_right a b
  have s1 : w1 * min a b ≤ w1 * a := mul_le_mul_of_nonneg_left ha h1
  have s2 : w2 * min a b ≤ w2 * b := mul_le_mul_of_nonneg_left hb h2
  nlinarith
```

Write ONE complete Lean 4 file. No sorry."""
)

# ---- convex.three_weighted_le_max ----
mine_recipe(
    "convex.three_weighted_le_max", "convex", "three_weighted_le_max",
    "nonneg weights summing to 1 → w₁*a+w₂*b+w₃*c ≤ max a (max b c)",
    "3-element convex combination ≤ max",
    """Prove in Lean 4: for reals w1 w2 w3 a b c, with 0≤wi and w1+w2+w3=1,
show w1*a + w2*b + w3*c ≤ max a (max b c).

Proof: Let M = max a (max b c). Then a ≤ M, b ≤ max b c ≤ M, c ≤ max b c ≤ M.
Each wi*xi ≤ wi*M, sum them, use w1+w2+w3=1.

```lean
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

example (w1 w2 w3 a b c : ℝ)
    (hw1 : 0 ≤ w1) (hw2 : 0 ≤ w2) (hw3 : 0 ≤ w3) (hw : w1 + w2 + w3 = 1) :
    w1 * a + w2 * b + w3 * c ≤ max a (max b c) := by
  have ha : a ≤ max a (max b c) := le_max_left a (max b c)
  have hb : b ≤ max a (max b c) := le_max_of_le_right (le_max_left b c)
  have hc : c ≤ max a (max b c) := le_max_of_le_right (le_max_right b c)
  have s1 : w1 * a ≤ w1 * max a (max b c) := mul_le_mul_of_nonneg_left ha hw1
  have s2 : w2 * b ≤ w2 * max a (max b c) := mul_le_mul_of_nonneg_left hb hw2
  have s3 : w3 * c ≤ w3 * max a (max b c) := mul_le_mul_of_nonneg_left hc hw3
  nlinarith
```

Write ONE complete Lean 4 file. No sorry."""
)

# ---- convex.exp_sum_bound ----
mine_recipe(
    "convex.exp_sum_bound", "convex", "exp_sum_bound",
    "a + b = 0 → exp a + exp b ≥ 2",
    "Sum of exp ≥ 2 when arguments sum to 0",
    """Prove in Lean 4: for reals a b with a + b = 0, exp a + exp b ≥ 2.

Proof using `add_one_le_exp`: for any x, 1 + x ≤ exp x, i.e. exp x ≥ 1 + x.
So exp(a) ≥ 1 + a and exp(b) ≥ 1 + b.
Sum: exp(a) + exp(b) ≥ 2 + a + b = 2 + 0 = 2.

```lean
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

open Real

example (a b : ℝ) (h : a + b = 0) : exp a + exp b ≥ 2 := by
  have h1 : 1 + a ≤ exp a := by linarith [add_one_le_exp a]
  have h2 : 1 + b ≤ exp b := by linarith [add_one_le_exp b]
  linarith
```

Write ONE complete Lean 4 file. No sorry."""
)


print("\n" + "="*60)
print("RETRY SUMMARY")
store2 = load_store()
total = len(store2.get("recipes", {}))
print(f"Total recipes now: {total}")
for fam in ("rational", "convex"):
    keys = [k for k, v in store2.get("recipes", {}).items() if v["family"] == fam]
    print(f"  {fam}: {len(keys)} — {keys}")
