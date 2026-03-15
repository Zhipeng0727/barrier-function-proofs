import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

noncomputable section

noncomputable section

-- ==========================================
-- 1. 基础框架定义 (Robust Barrier Function)
-- ==========================================
structure IsRobustBarrierFunction
  (f : (ℝ × ℝ) → (ℝ × ℝ) → (ℝ × ℝ))
  (S U : Set (ℝ × ℝ)) (B : (ℝ × ℝ) → ℝ) (l : ℝ) : Prop where
  l_bounds : 0 < l ∧ l ≤ 1
  outside_safe : ∀ p, p ∉ S → B p < 0
  robust_barrier_condition : ∀ p, p ∈ S → ∀ u, u ∈ U → B (f p u) - l * B p ≥ 0

-- ==========================================
-- 2. 系统参数与函数定义 (Example 3)
-- ==========================================
def f_ex3 (p u : ℝ × ℝ) : ℝ × ℝ :=
  ((1 / 2 : ℝ) * p.1 + (2 / 5 : ℝ) * p.2 + u.1,
   (1 / 2 : ℝ) * p.2 + u.2)

def S_ex3 : Set (ℝ × ℝ) :=
  {p | |p.1| ≤ (1 / 5 : ℝ) ∧ |p.2| ≤ (1 / 5 : ℝ)}

def U_ex3 : Set (ℝ × ℝ) :=
  {u | |u.1| ≤ (3 / 100 : ℝ) ∧ |u.2| ≤ (3 / 100 : ℝ)}

def B_ex3 (p : ℝ × ℝ) : ℝ :=
  (17 / 100 : ℝ) ^ 2 - (p.1 ^ 2 + p.2 ^ 2)

lemma ex3_outside_safe : ∀ p, p ∉ S_ex3 → B_ex3 p < 0 := by
  intro ⟨x,y⟩ hp
  dsimp [S_ex3] at hp

  by_cases hx : |x| ≤ (1/5 : ℝ)

  · -- 从 ¬(A ∧ B) 和 A 推出 ¬B
    have hy_not : ¬ |y| ≤ (1/5 : ℝ) := by
      exact (not_and.mp hp) hx

    have hy : (1/5 : ℝ) < |y| := by
      exact lt_of_not_ge hy_not

    have hy2 : (1/5 : ℝ)^2 < y^2 := by
      rw [← sq_abs]
      nlinarith [hy]

    dsimp [B_ex3]
    nlinarith [hy2, sq_nonneg x]

  · have hx' : (1/5 : ℝ) < |x| := by
      exact lt_of_not_ge hx

    have hx2 : (1/5 : ℝ)^2 < x^2 := by
      rw [← sq_abs]
      nlinarith [hx']

    dsimp [B_ex3]
    nlinarith [hx2, sq_nonneg y]
-- ==========================================
-- 4. 关键一步：
--    对所有状态 (x,y) 都有 barrier inequality，
--    所以当然也对所有 p ∈ S_ex3 成立
-- ==========================================
lemma ex3_barrier_step
    {x y u1 u2 : ℝ}
    (hu1 : |u1| ≤ (3 / 100 : ℝ))
    (hu2 : |u2| ≤ (3 / 100 : ℝ)) :
    B_ex3 (f_ex3 (x, y) (u1, u2)) - (7 / 10 : ℝ) * B_ex3 (x, y) ≥ 0 := by

  have hquad :
      (3 / 20 : ℝ) * x^2 + (3 / 20 : ℝ) * y^2
        ≤ (9 / 20 : ℝ) * x^2 - (2 / 5 : ℝ) * x * y + (29 / 100 : ℝ) * y^2 := by
    nlinarith [sq_nonneg (3 * x - 2 * y), sq_nonneg y]

  have hu1sq : u1^2 ≤ (3 / 100 : ℝ)^2 := by
    rw [← sq_abs]
    nlinarith [hu1, abs_nonneg u1]

  have hu2sq : u2^2 ≤ (3 / 100 : ℝ)^2 := by
    rw [← sq_abs]
    nlinarith [hu2, abs_nonneg u2]

  have hxu1abs : |x * u1| ≤ (3 / 100 : ℝ) * |x| := by
    calc
      |x * u1| = |x| * |u1| := by rw [abs_mul]
      _ ≤ |x| * (3 / 100 : ℝ) := by
        exact mul_le_mul_of_nonneg_left hu1 (abs_nonneg x)
      _ = (3 / 100 : ℝ) * |x| := by ring

  have hyu1abs : |y * u1| ≤ (3 / 100 : ℝ) * |y| := by
    calc
      |y * u1| = |y| * |u1| := by rw [abs_mul]
      _ ≤ |y| * (3 / 100 : ℝ) := by
        exact mul_le_mul_of_nonneg_left hu1 (abs_nonneg y)
      _ = (3 / 100 : ℝ) * |y| := by ring

  have hyu2abs : |y * u2| ≤ (3 / 100 : ℝ) * |y| := by
    calc
      |y * u2| = |y| * |u2| := by rw [abs_mul]
      _ ≤ |y| * (3 / 100 : ℝ) := by
        exact mul_le_mul_of_nonneg_left hu2 (abs_nonneg y)
      _ = (3 / 100 : ℝ) * |y| := by ring

  have hxu1 : -x * u1 ≥ -(3 / 100 : ℝ) * |x| := by
    have h : x * u1 ≤ (3 / 100 : ℝ) * |x| := (abs_le.mp hxu1abs).2
    nlinarith

  have hyu1 : -(4 / 5 : ℝ) * y * u1 ≥ -(3 / 125 : ℝ) * |y| := by
    have h : y * u1 ≤ (3 / 100 : ℝ) * |y| := (abs_le.mp hyu1abs).2
    nlinarith

  have hyu2 : -y * u2 ≥ -(3 / 100 : ℝ) * |y| := by
    have h : y * u2 ≤ (3 / 100 : ℝ) * |y| := (abs_le.mp hyu2abs).2
    nlinarith

  have hxlower :
      (3 / 20 : ℝ) * x^2 - (3 / 100 : ℝ) * |x| ≥ -(3 / 2000 : ℝ) := by
    rw [← sq_abs]
    nlinarith [sq_nonneg (|x| - (1 / 10 : ℝ))]

  have hylower :
      (3 / 20 : ℝ) * y^2 - (27 / 500 : ℝ) * |y| ≥ -(243 / 50000 : ℝ) := by
    rw [← sq_abs]
    nlinarith [sq_nonneg (|y| - (9 / 50 : ℝ))]

  have hmain :
      B_ex3 (f_ex3 (x, y) (u1, u2)) - (7 / 10 : ℝ) * B_ex3 (x, y)
        =
        (867 / 100000 : ℝ)
        + (9 / 20 : ℝ) * x^2
        - (2 / 5 : ℝ) * x * y
        + (29 / 100 : ℝ) * y^2
        - u1^2 - u2^2
        - x * u1
        - (4 / 5 : ℝ) * y * u1
        - y * u2 := by
    dsimp [B_ex3, f_ex3]
    ring

  rw [hmain]
  nlinarith [hquad, hu1sq, hu2sq, hxu1, hyu1, hyu2, hxlower, hylower]

-- ==========================================
-- 5. 最终结论：B_ex3 是 robust barrier function
-- ==========================================
theorem ex3_B_isRobustBarrier :
  IsRobustBarrierFunction f_ex3 S_ex3 U_ex3 B_ex3 (7 / 10 : ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · constructor <;> norm_num
  · exact ex3_outside_safe
  · intro p _hpS u hu
    rcases p with ⟨x, y⟩
    rcases u with ⟨u1, u2⟩
    dsimp [U_ex3] at hu
    rcases hu with ⟨hu1, hu2⟩
    exact ex3_barrier_step hu1 hu2
