import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace BBLinear
def f1 (x1 x2 : ℝ) : ℝ := -5*x1 - 4*x2
def f2 (x1 x2 : ℝ) : ℝ := -x1 - 2*x2
def h (x1 x2 : ℝ) : ℝ := 9 - x1^2 - x2^2
def hdot (x1 x2 : ℝ) : ℝ := (-2*x1) * f1 x1 x2 + (-2*x2) * f2 x1 x2

theorem cond1 (x1 x2 : ℝ) (hu : x1^2 + x2^2 > 9) : h x1 x2 < 0 := by
  unfold h; nlinarith [hu]

theorem cond2 (x1 x2 : ℝ) : hdot x1 x2 ≥ 0 := by
  unfold hdot f1 f2
  nlinarith [sq_nonneg (2*x1 + x2), sq_nonneg x2, sq_nonneg (x1 + x2), sq_nonneg x1]
end BBLinear
