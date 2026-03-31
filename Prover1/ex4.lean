import Mathlib.Data.Real.Basic
import Mathlib.Tactic

-- 开启不可计算区域，跳过可执行代码的生成阶段
noncomputable section

namespace TranscendentalBarrierC

/-- State domain `X = [-2,2] × [-2,2]`. -/
def InX (x1 x2 : ℝ) : Prop :=
  -2 ≤ x1 ∧ x1 ≤ 2 ∧ -2 ≤ x2 ∧ x2 ≤ 2

/-- Unsafe disk centered at `(0.7,-0.7)` with radius `0.3`. -/
def Unsafe (x1 x2 : ℝ) : Prop :=
  (x1 - (7 : ℝ) / 10)^2 + (x2 + (7 : ℝ) / 10)^2 ≤ ((3 : ℝ) / 10)^2

/-- The vector field. -/
def f1 (x1 x2 : ℝ) : ℝ := Real.exp (-x1) + x2 - 1
def f2 (x1 : ℝ) (x2 : ℝ) : ℝ := -(Real.sin x1)^2 + 0*x2

/-- The auxiliary drift coordinate `b = x₁'`. -/
def b (x1 x2 : ℝ) : ℝ := Real.exp (-x1) + x2 - 1

/-- The potential term with derivative `H' = sin²`. -/
def H (x1 : ℝ) : ℝ := x1 / 2 - Real.sin (2 * x1) / 4

/-- Candidate energy function. -/
def V (x1 x2 : ℝ) : ℝ := (b x1 x2)^2 / 2 + H x1

/-- Candidate barrier `B = c - V`, with the explicit constant `c = 1/50`. -/
def B (x1 x2 : ℝ) : ℝ := (1 : ℝ) / 50 - V x1 x2

/-- We use `α(s) = 0`. -/
def alpha (s : ℝ) : ℝ := 0 + 0*s

/-- Certified set `C = {B ≥ 0}`. -/
def InC (x1 x2 : ℝ) : Prop := 0 ≤ B x1 x2

/-- Analytically computed partial derivatives of `B`. -/
def Bx1 (x1 x2 : ℝ) : ℝ := Real.exp (-x1) * b x1 x2 - (Real.sin x1)^2
def Bx2 (x1 x2 : ℝ) : ℝ := - b x1 x2

/-- Lie derivative of `B` along the vector field. -/
def lieB (x1 x2 : ℝ) : ℝ := Bx1 x1 x2 * f1 x1 x2 + Bx2 x1 x2 * f2 x1 x2

lemma unsafe_x1_lower {x1 x2 : ℝ} (hu : Unsafe x1 x2) : (2 : ℝ) / 5 ≤ x1 := by
  unfold Unsafe at hu
  have hx1sq : (x1 - (7 : ℝ) / 10)^2 ≤ ((3 : ℝ) / 10)^2 := by
    nlinarith [hu, sq_nonneg (x2 + (7 : ℝ) / 10)]
  nlinarith

lemma unsafe_x1_upper {x1 x2 : ℝ} (hu : Unsafe x1 x2) : x1 ≤ (1 : ℝ) := by
  unfold Unsafe at hu
  have hx1sq : (x1 - (7 : ℝ) / 10)^2 ≤ ((3 : ℝ) / 10)^2 := by
    nlinarith [hu, sq_nonneg (x2 + (7 : ℝ) / 10)]
  nlinarith

lemma unsafe_x2_lower {x1 x2 : ℝ} (hu : Unsafe x1 x2) : -(1 : ℝ) ≤ x2 := by
  unfold Unsafe at hu
  have hx2sq : (x2 + (7 : ℝ) / 10)^2 ≤ ((3 : ℝ) / 10)^2 := by
    nlinarith [hu, sq_nonneg (x1 - (7 : ℝ) / 10)]
  nlinarith

lemma unsafe_x2_upper {x1 x2 : ℝ} (hu : Unsafe x1 x2) : x2 ≤ -(2 : ℝ) / 5 := by
  unfold Unsafe at hu
  have hx2sq : (x2 + (7 : ℝ) / 10)^2 ≤ ((3 : ℝ) / 10)^2 := by
    nlinarith [hu, sq_nonneg (x1 - (7 : ℝ) / 10)]
  nlinarith

lemma H_lower_bound_of_x1_ge_two_fifths {x1 : ℝ} (hx : (2 : ℝ) / 5 ≤ x1) :
    -(1 : ℝ) / 20 ≤ H x1 := by
  unfold H
  have hsin : Real.sin (2 * x1) ≤ 1 := by
    exact Real.sin_le_one (2 * x1)
  nlinarith

lemma b_upper_on_unsafe {x1 x2 : ℝ} (hu : Unsafe x1 x2) : b x1 x2 ≤ -(2 : ℝ) / 5 := by
  have hx1 : (2 : ℝ) / 5 ≤ x1 := unsafe_x1_lower hu
  have hx2 : x2 ≤ -(2 : ℝ) / 5 := unsafe_x2_upper hu
  have hexp : Real.exp (-x1) ≤ 1 := by
    have hneg : -x1 ≤ 0 := by nlinarith
    have h := Real.exp_le_exp.mpr hneg
    simpa using h
  unfold b
  nlinarith

lemma half_sq_lower_of_b_upper {u : ℝ} (hu : u ≤ -(2 : ℝ) / 5) :
    (2 : ℝ) / 25 ≤ u^2 / 2 := by
  nlinarith

/-- The candidate barrier is strictly negative on the unsafe disk. -/
lemma B_neg_on_unsafe {x1 x2 : ℝ} (hu : Unsafe x1 x2) : B x1 x2 < 0 := by
  have hb : b x1 x2 ≤ -(2 : ℝ) / 5 := b_upper_on_unsafe hu
  have hsq : (2 : ℝ) / 25 ≤ (b x1 x2)^2 / 2 := half_sq_lower_of_b_upper hb
  have hH : -(1 : ℝ) / 20 ≤ H x1 := H_lower_bound_of_x1_ge_two_fifths (unsafe_x1_lower hu)
  unfold B V
  nlinarith

/-- Exact factorization of the Lie derivative. -/
lemma lieB_eq (x1 x2 : ℝ) :
    lieB x1 x2 = Real.exp (-x1) * (b x1 x2)^2 := by
  unfold lieB Bx1 Bx2 f1 f2 b
  ring

lemma lieB_plus_alpha_eq (x1 x2 : ℝ) :
    lieB x1 x2 + alpha (B x1 x2) = Real.exp (-x1) * (b x1 x2)^2 := by
  rw [lieB_eq]
  unfold alpha
  ring

/-- `C`-version: on all of `C`, the condition `Ḃ + α(B) ≥ 0` holds.
In fact it holds globally, independently of `C`. -/
lemma flow_condition_on_C {x1 x2 : ℝ} (hc : InC x1 x2) :
    0 ≤ lieB x1 x2 + alpha (B x1 x2) := by
  rw [lieB_plus_alpha_eq]
  -- 推荐做法：直接使用 positivity 策略，它能完美识别指数与平方的乘积
  positivity

/-- Summary theorem for the barrier certificate on `C = {B ≥ 0}`. -/
theorem barrier_certificate_on_C {x1 x2 : ℝ} (_hx : InX x1 x2) :
    (Unsafe x1 x2 → B x1 x2 < 0) ∧
    (InC x1 x2 → 0 ≤ lieB x1 x2 + alpha (B x1 x2)) := by
  constructor
  · intro hu
    exact B_neg_on_unsafe hu
  · intro hc
    exact flow_condition_on_C hc
end TranscendentalBarrierC
