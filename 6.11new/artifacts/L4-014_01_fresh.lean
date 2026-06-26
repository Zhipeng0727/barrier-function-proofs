-- strategy=fresh cert=0.5*x**2+0.5*y**2
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic

open Real

-- Condition P0: V(x*) = 0 at the equilibrium x* = [0.0, 0.0]
theorem condition_P0 : (0.5 * (0 : ℝ)^2) + (0.5 * (0 : ℝ)^2) = 0 := by
  norm_num

-- Condition P1: V(x) > 0 for all x in X with x != x*
theorem condition_P1 (x y : ℝ) (h : ¬(x = 0 ∧ y = 0)) :
    0.5 * x^2 + 0.5 * y^2 > 0 := by
  rcases not_and_or.mp h with hx | hy
  · have : x^2 > 0 := by positivity
    nlinarith [sq_nonneg y]
  · have : y^2 > 0 := by positivity
    nlinarith [sq_nonneg x]

-- Bridging Lemma: damping term y·tanh(y) is nonneg
lemma y_tanh_y_nonneg (y : ℝ) : 0 ≤ y * Real.tanh y := by
  rw [tanh_eq_sinh_div_cosh, ← mul_div_assoc]
  apply div_nonneg _ (cosh_pos y).le
  rcases le_total 0 y with hy | hy
  · exact mul_nonneg hy (sinh_nonneg_iff.mpr hy)
  · have hs : sinh y ≤ 0 := by
      have h := sinh_nonneg_iff (x := -y)
      rw [sinh_neg] at h
      linarith [h.mpr (by linarith : (0:ℝ) ≤ -y)]
    nlinarith [mul_nonneg (neg_nonneg.2 hy) (neg_nonneg.2 hs)]

-- Condition D: Vdot(x) = ∇V(x) · f(x) <= 0 for all x in the domain X
theorem condition_D (x y : ℝ) : x * y + y * (-x - Real.tanh y) ≤ 0 := by
  have h1 : x * y + y * (-x - Real.tanh y) = -(y * Real.tanh y) := by ring
  rw [h1]
  nlinarith [y_tanh_y_nonneg y]

-- Main theorem combining all conditions for Lyapunov stability
theorem lyapunov_stability (x y : ℝ) (h : ¬(x = 0 ∧ y = 0)) :
    0.5 * x^2 + 0.5 * y^2 > 0 ∧
    x * y + y * (-x - Real.tanh y) ≤ 0 := by
  exact ⟨condition_P1 x y h, condition_D x y⟩
