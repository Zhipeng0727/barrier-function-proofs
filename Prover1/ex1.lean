import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic
-- 1. 定义不变集的通用概念 (对应Definition 1.1)
-- 这里的 C 是一个集合，f 是动力系统函数
def IsInvariant (f : ℝ → ℝ) (C : Set ℝ) : Prop :=
  ∀ x, x ∈ C → f x ∈ C

-- 2. 定义具体的系统参数和安全集
-- 系统动力学: f(x) = a * x
-- 安全集: S = [-1, 1]
def f (a : ℝ) (x : ℝ) : ℝ := a * x
def S : Set ℝ := Set.Icc (-1) 1  -- Icc 表示 [left, right] 闭区间

--方法1:通过直接证明，得到不变集
-- 3. 证明：当 |a| ≤ 1 时，S 是 f 的不变集
theorem safety_set_invariant (a : ℝ) (ha : |a| ≤ 1) : IsInvariant (f a) S := by
  -- 展开定义：我们要证明对于任意 x ∈ S，f(a, x) 也在 S 中
  unfold IsInvariant
  intro x hx

  -- 展开 S 的定义：x ∈ [-1, 1] 等价于 |x| ≤ 1
  rw [S,Set.mem_Icc] at hx ⊢

  -- 目标是证明 -1 ≤ a * x ∧ a * x ≤ 1
  have h_abs : |f a x| = |a| * |x| := by
    unfold f
    exact abs_mul a x

  -- 利用已知条件 |a| ≤ 1 和 |x| ≤ 1 推导 |a| * |x| ≤ 1
  have h_bound : |a| * |x| ≤ 1 := by
      -- 1. 先证明 |a| * |x| ≤ 1 * |x|
      have h1 : |a| * |x| ≤ 1 * |x| := by
        apply mul_le_mul_of_nonneg_right ha
        exact abs_nonneg x

      -- 2. 再利用 1 * |x| = |x| ≤ 1
      have h2 : 1 * |x| ≤ 1 := by
        rw [one_mul]
        exact abs_le.mpr hx

      -- 3. 传递性
      exact le_trans h1 h2
  -- 最后将绝对值界限转回区间界限 [-1, 1]
  exact abs_le.mp (h_abs.symm ▸ h_bound)

--方法2:通过构造barrier函数来得到不变集
-- 定义离散时间 Barrier Function 的性质
structure IsBarrierFunction (f : ℝ → ℝ) (S : Set ℝ) (B : ℝ → ℝ) (α : ℝ) : Prop where
  -- 1. α 必须在 (0, 1] 之间
  α_bounds : 0 < α ∧ α ≤ 1
  -- 2. 安全集之外 B < 0
  outside_safe : ∀ x, x ∉ S → B x < 0
  -- 3. 安全集之内满足下降/维持条件：B(f(x)) - αB(x) ≥ 0
  barrier_condition : ∀ x, x ∈ S → B (f x) - α * B x ≥ 0

-- 定义基于 B 构造的集合：{x ∈ S | B(x) ≥ 0}
def InvariantSetFromB (S : Set ℝ) (B : ℝ → ℝ) : Set ℝ :=
  {x | x ∈ S ∧ B x ≥ 0}

--证明满足这样的barrier函数构造的集合一定是不变集：
theorem invariant_from_barrier (f : ℝ → ℝ) (S : Set ℝ) (B : ℝ → ℝ) (α : ℝ)
    (hB : IsBarrierFunction f S B α) :
    ∀ x, x ∈ InvariantSetFromB S B → f x ∈ InvariantSetFromB S B := by
  intro x hx
  -- 展开 InvariantSetFromB 的定义
  rcases hx with ⟨hxS, hxB⟩

  -- 我们需要证明 f(x) ∈ S 且 B(f(x)) ≥ 0
  constructor
  · -- 证明 f(x) ∈ S：利用反证法。如果 f(x) ∉ S，则 B(f(x)) < 0
    by_contra h_not_S
    have h_neg := hB.outside_safe (f x) h_not_S
    -- 但根据 barrier_condition: B(f(x)) ≥ α * B(x) ≥ 0
    have h_cond := hB.barrier_condition x hxS
    have h_ge_zero : B (f x) ≥ 0 := by
      -- α > 0 且 B(x) ≥ 0，所以 α * B(x) ≥ 0
      have : α * B x ≥ 0 := mul_nonneg (le_of_lt hB.α_bounds.1) hxB
      linarith
    linarith -- 矛盾：B(f(x)) 既 < 0 又 ≥ 0
  · -- 证明 B(f(x)) ≥ 0
    have h_cond := hB.barrier_condition x hxS
    have : α * B x ≥ 0 := mul_nonneg (le_of_lt hB.α_bounds.1) hxB
    linarith

def f_ex (a x : ℝ) : ℝ := a * x
def S_ex : Set ℝ := Set.Icc (-1) 1
def B_ex (x : ℝ) : ℝ := 1 - x^2

theorem example_is_barrier (a : ℝ) (ha : |a| < 1) :
    IsBarrierFunction (f_ex a) S_ex B_ex 1 where
  α_bounds := ⟨by linarith, by linarith⟩
  outside_safe := by
    intro x hx
    unfold S_ex B_ex at *
    -- 1. 转化为标准的不等式或关系
    rw [Set.mem_Icc, not_and_or] at hx
    -- 2. 分情况讨论证明 x^2 > 1
    have : x^2 > 1 := by
      rcases hx with h_left | h_right
      · nlinarith
      · nlinarith
    -- 3. 闭合 B(x) < 0 的证明，即 1 - x^2 < 0
    linarith
  barrier_condition := by
    intro x hx
    unfold f_ex B_ex S_ex at *
    have h_a2 : a^2 < 1 := by nlinarith [abs_lt.mp ha]
    calc
      (1 - (a * x)^2) - 1 * (1 - x^2) = (1 - a^2) * x^2 := by ring
      _ ≥ 0 := by
        nlinarith

-- 定义系统 2
def f_ex2 (a x : ℝ) : ℝ := a * x * (1 - x)
def S_ex2 : Set ℝ := Set.Icc 0 1
def B_ex2 (x : ℝ) : ℝ := x * (1 - x)

theorem example2_is_barrier (a : ℝ) (h_a_low : 0 < a) (h_a_high : a < 4) :
    IsBarrierFunction (f_ex2 a) S_ex2 B_ex2 (a * (1 - a / 4)) where
  α_bounds := by
    constructor
    · -- 证明 λ > 0
      nlinarith
    · -- 证明 λ ≤ 1，即 a(1 - a/4) ≤ 1 -> -(a-2)^2/4 ≤ 0
      have h_quad : a * (1 - a / 4) = 1 - (a - 2)^2 / 4 := by ring
      rw [h_quad]
      nlinarith
  outside_safe := by
    intro x hx
    unfold S_ex2 B_ex2 at *
    rw [Set.mem_Icc, not_and_or] at hx
    rcases hx with h_left | h_right
    · nlinarith -- x < 0
    · nlinarith -- x > 1
  barrier_condition := by
      intro x hx
      unfold f_ex2 B_ex2 S_ex2 at *
      rw [Set.mem_Icc] at hx

      -- 先定义 Bx，简化后续书写
      let Bx := x * (1 - x)

      -- 证明 Bx 的范围
      have hBx_ge : 0 ≤ Bx := by nlinarith
      have hBx_le : Bx ≤ 1 / 4 := by
        have : Bx = 1/4 - (x - 1/2)^2 := by ring
        nlinarith

      -- 使用 calc 进行链式推导
      -- 目标是证明 B(f(x)) - λB(x) ≥ 0
      calc
        (a * x * (1 - x)) * (1 - (a * x * (1 - x))) - (a * (1 - a / 4)) * (x * (1 - x))
            = (a * Bx) * (1 - a * Bx) - a * (1 - a / 4) * Bx := by ring
          _ = a * Bx * ((1 - a * Bx) - (1 - a / 4))     := by ring
          _ = a * Bx * (a / 4 - a * Bx)                  := by ring
          _ = a^2 * Bx * (1 / 4 - Bx)                    := by ring
          _ ≥ 0 := by
            -- 最后一步：a^2 ≥ 0, Bx ≥ 0, (1/4 - Bx) ≥ 0
            apply mul_nonneg
            · apply mul_nonneg (pow_two_nonneg a) hBx_ge
            · linarith
