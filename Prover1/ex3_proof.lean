import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul   -- 确保导入
import Mathlib.Tactic

noncomputable section
open Real

namespace CBFExample

def lie (B : ℝ → ℝ → ℝ) (vf1 vf2 : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t : ℝ => B (x + t * vf1 x y) (y + t * vf2 x y)) 0

namespace Ex1

def vf1 (x y : ℝ) : ℝ := y + 2 * x * y
def vf2 (x y : ℝ) : ℝ := -x - y ^ 2 + 2 * x ^ 2
def barrier (x y : ℝ) : ℝ := -8 * x ^ 2 + 10 * x + 12 * y ^ 2 - 5
def cofactor (x y : ℝ) : ℝ := -2 * y + 0*x

theorem barrier_lie (x y : ℝ) :
    lie barrier vf1 vf2 x y = cofactor x y * barrier x y := by
  simp only [lie, barrier, vf1, vf2, cofactor]
  -- 使用点语法构造导数为 t * c 的函数，并简化导数 1*c 为 c
  have h1lin : HasDerivAt (fun t => t * (y + 2 * x * y)) (y + 2 * x * y) 0 := by
    exact (hasDerivAt_id 0).mul_const (y + 2 * x * y) |>.congr_deriv (by rw [one_mul])
  have h2lin : HasDerivAt (fun t => t * (-x - y ^ 2 + 2 * x ^ 2)) (-x - y ^ 2 + 2 * x ^ 2) 0 := by
    exact (hasDerivAt_id 0).mul_const (-x - y ^ 2 + 2 * x ^ 2) |>.congr_deriv (by rw [one_mul])
  -- 构造 x + t * f1 和 y + t * f2 的导数
  have h1' : HasDerivAt (fun t => x + t * (y + 2 * x * y)) (y + 2 * x * y) 0 := by
    simpa using h1lin.const_add x
  have h2' : HasDerivAt (fun t => y + t * (-x - y ^ 2 + 2 * x ^ 2))
      (-x - y ^ 2 + 2 * x ^ 2) 0 := by
    simpa using h2lin.const_add y
  -- 组合得到 B 的导数
  have hB :
      HasDerivAt
        (fun t =>
          -8 * (x + t * (y + 2 * x * y)) ^ 2 +
            10 * (x + t * (y + 2 * x * y)) +
            12 * (y + t * (-x - y ^ 2 + 2 * x ^ 2)) ^ 2 - 5)
        ((-2 * y) * (-8 * x ^ 2 + 10 * x + 12 * y ^ 2 - 5)) 0 := by
    -- 先组合导数，再把右侧导数值化简成目标形式
    have hB' :=
      (((h1'.pow 2).const_mul (-8)).add (h1'.const_mul 10)).add
      ((h2'.pow 2).const_mul 12) |>.sub (by
        simpa using (hasDerivAt_const (c := 5) (x := (0 : ℝ))))
    -- 将 hB' 的导数值用 `ring` 化简成 -2*y*barrier x y
    have hEq :
        ((-8 : ℝ) *
            (↑2 * (x + 0 * (y + 2 * x * y)) ^ (2 - 1) * (y + 2 * x * y)) +
          10 * (y + 2 * x * y) +
          12 * (↑2 * (y + 0 * (-x - y ^ 2 + 2 * x ^ 2)) ^ (2 - 1) * (-x - y ^ 2 + 2 * x ^ 2)) - 0)
        = (-2 * y) * (-8 * x ^ 2 + 10 * x + 12 * y ^ 2 - 5) := by
      ring
    -- 利用上面的等式改写导数值
    refine hEq ▸ hB'
  -- 把 HasDerivAt 变成导数等式，并直接完成证明
  simpa using (HasDerivAt.deriv hB)

end Ex1
end CBFExample
