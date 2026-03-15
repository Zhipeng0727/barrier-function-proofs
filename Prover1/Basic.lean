import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith -- 线性算术战术
import Mathlib.Tactic.Polyrith -- 多项式算术战术
import Mathlib.Tactic

-- 命题：对于任意实数 a, b，(a + b)^2 ≥ 4ab
theorem square_plus_ge_4ab (a b : ℝ) : (a + b)^2 ≥ 4 * a * b := by
  -- 第一步：展开左边的平方
  -- 我们知道 (a + b)^2 - 4ab = (a - b)^2
  -- 在 Lean 中，我们可以通过移项来简化目标
  have h : (a + b)^2 - 4 * a * b = (a - b)^2 := by
    ring -- ring 战术专门处理多项式环的展开和化简

  -- 第二步：利用“平方数非负”的性质
  have h_nonneg : (a - b)^2 ≥ 0 := by
    nlinarith -- nlinarith 处理非线性算术不等式，它知道平方 ≥ 0

  -- 第三步：结合上述两点
  rw [h] -- 用 h 替换掉目标中的表达式
  exact h_nonneg -- 此时目标变为 (a - b)^2 ≥ 0，与 h_nonneg 完全一致
