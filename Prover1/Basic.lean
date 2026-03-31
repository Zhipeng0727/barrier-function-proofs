import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith -- 线性算术战术
import Mathlib.Tactic.Polyrith -- 多项式算术战术
import Mathlib.Tactic

--  a, b，(a + b)^2 ≥ 4ab
theorem square_plus_ge_4ab (a b : ℝ) : (a + b)^2 ≥ 4 * a * b := by
  -- 第一步：展开左边的平方
  -- 我们知道 (a + b)^2 - 4ab = (a - b)^2
  -- 在 Lean 中，我们可以通过移项来简化目标
  have h : (a + b)^2 - 4 * a * b = (a - b)^2 := by
    ring -- ring 战术专门处理多项式环的展开和化简

  have h : (a + b)^2 - 4 * a * b ≥ 0 := by
    calc (a + b)^2 - 4 * a * b
      _ = (a - b)^2 := by ring
      _ ≥ 0         := by positivity

  linarith

theorem square_sum_le_two_sq (a b : ℝ) : (a + b)^2 ≤ 2 * (a^2 + b^2) := by
  have h : 2 * (a^2 + b^2) - (a + b)^2 ≥ 0 := by
    calc 2 * (a^2 + b^2) - (a + b)^2
        _ = (a - b)^2 := by ring
        _ ≥ 0 := by positivity
  linarith
