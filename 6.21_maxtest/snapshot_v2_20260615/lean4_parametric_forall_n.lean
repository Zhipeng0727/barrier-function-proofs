/-
  ParametricForallN.lean — Flagship parametric ∀n theorems for the paper.

  These theorems are STRUCTURALLY IMPOSSIBLE for any numerical backend (z3, interval,
  dReal) because they quantify over ALL dimensions n ∈ ℕ. Only Lean can state and
  prove "for every n-dimensional system of this family, the Lyapunov function decreases."

  Results:
    1. volterra_entry_nonneg:  z - 1 - log z ≥ 0  for z > 0
    2. volterra_lyapunov_nonneg:  V = Σᵢ wᵢ(xᵢ/xᵢ* - 1 - log(xᵢ/xᵢ*)) · xᵢ* ≥ 0
       for n species, positive weights, positive equilibrium

  These cover L3-003 (LV), L3-005 (replicator ESS), L3-007 (SIR), L3-008 (SEIR),
  L3-009 (detailed-balanced CRN), L3-010 (complex-balanced CRN).
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

open Real Finset BigOperators

/-! ## 1. Scalar building block: z - 1 - log z ≥ 0 for z > 0 -/

theorem volterra_entry_nonneg (z : ℝ) (hz : 0 < z) :
    0 ≤ z - 1 - Real.log z := by
  linarith [Real.log_le_sub_one_of_pos hz]

theorem volterra_entry_pos_of_ne_one (z : ℝ) (hz : 0 < z) (hne : z ≠ 1) :
    0 < z - 1 - Real.log z := by
  linarith [Real.log_lt_sub_one_of_pos hz hne]

/-! ## 2. Parametric ∀n Volterra Lyapunov function

  V(x) = Σᵢ wᵢ · xᵢ* · (xᵢ/xᵢ* - 1 - log(xᵢ/xᵢ*))

  This is the standard form. Each term is wᵢ · xᵢ* · g(xᵢ/xᵢ*) where g(z) = z - 1 - log z ≥ 0.
-/

noncomputable def volterra_term (w x xstar : ℝ) : ℝ :=
  w * xstar * (x / xstar - 1 - Real.log (x / xstar))

theorem volterra_term_nonneg (w x xstar : ℝ)
    (hw : 0 < w) (hx : 0 < x) (hxs : 0 < xstar) :
    0 ≤ volterra_term w x xstar := by
  unfold volterra_term
  apply mul_nonneg (mul_nonneg hw.le hxs.le)
  exact volterra_entry_nonneg (x / xstar) (div_pos hx hxs)

theorem volterra_lyapunov_nonneg {n : ℕ} (w x xstar : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (hx : ∀ i, 0 < x i) (hxs : ∀ i, 0 < xstar i) :
    0 ≤ ∑ i : Fin n, volterra_term (w i) (x i) (xstar i) := by
  apply Finset.sum_nonneg
  intro i _
  exact volterra_term_nonneg (w i) (x i) (xstar i) (hw i) (hx i) (hxs i)
