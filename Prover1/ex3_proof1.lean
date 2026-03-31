--使用两种方法来证明这个barrier性质，一个是边界一个是整个不变集C

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace DarbouxBarrier1

/-- State domain `X = [-2,2] × [-2,2]`. -/
def InX (x1 x2 : ℝ) : Prop :=
  (-2 ≤ x1 ∧ x1 ≤ 2) ∧ (-2 ≤ x2 ∧ x2 ≤ 2)

/-- Unsafe set `X_u = {(x1,x2) | x1 + x2^2 ≤ 0}`. -/
def Unsafe (x1 x2 : ℝ) : Prop := x1 + x2^2 ≤ 0

/-- The polynomial vector field. -/
def f1 (x1 x2 : ℝ) : ℝ := x2 + 2 * x1 * x2
def f2 (x1 x2 : ℝ) : ℝ := -x1 - x2^2 + 2 * x1^2

/-- Candidate Darboux barrier. -/
def h (x1 x2 : ℝ) : ℝ := -8 * x1^2 + 10 * x1 + 12 * x2^2 - 5

/-- `α(s) = 4 s`. -/
def alpha (s : ℝ) : ℝ := 4 * s

/-- Coordinate partial derivatives of `h`. -/
def hx1 (x1 x2 : ℝ) : ℝ := -16 * x1 + 10 + 0*x2
def hx2 (x1 x2 : ℝ) : ℝ := 24 * x2 + 0*x1

/-- Lie derivative of `h` along the vector field. -/
def lieH (x1 x2 : ℝ) : ℝ := hx1 x1 x2 * f1 x1 x2 + hx2 x1 x2 * f2 x1 x2

/-- Certified set `C = {h ≥ 0}`. -/
def InC (x1 x2 : ℝ) : Prop := 0 ≤ h x1 x2

/-- Boundary of `C`, written as the level set `h = 0`. -/
def OnBoundaryC (x1 x2 : ℝ) : Prop := h x1 x2 = 0

lemma lieH_eq_darboux (x1 x2 : ℝ) :
    lieH x1 x2 = -2 * x2 * h x1 x2 := by
  unfold lieH hx1 hx2 f1 f2 h
  ring

lemma lieH_plus_alpha_eq_factorized (x1 x2 : ℝ) :
    lieH x1 x2 + alpha (h x1 x2) = (4 - 2 * x2) * h x1 x2 := by
  rw [lieH_eq_darboux]
  unfold alpha
  ring

/-- `h` is strictly negative on the unsafe set. -/
lemma h_neg_on_unsafe {x1 x2 : ℝ} (hu : Unsafe x1 x2) : h x1 x2 < 0 := by
  unfold Unsafe at hu
  have hx2 : x2^2 ≤ -x1 := by
    linarith
  have hmajor : h x1 x2 ≤ -8 * x1^2 - 2 * x1 - 5 := by
    unfold h
    nlinarith
  have hsquare : -8 * x1^2 - 2 * x1 - 5 = -8 * (x1 + (1/8 : ℝ))^2 - 39/8 := by
    ring
  rw [hsquare] at hmajor
  have hstrict : -8 * (x1 + (1/8 : ℝ))^2 - 39/8 < 0 := by
    have hs : 0 ≤ (x1 + (1/8 : ℝ))^2 := sq_nonneg (x1 + (1/8 : ℝ))
    nlinarith
  linarith

/-- `C`-version: on all of `C`, the condition `ḣ + α(h) ≥ 0` holds. -/
lemma flow_condition_on_C {x1 x2 : ℝ} (hx : InX x1 x2) (hc : InC x1 x2) :
    0 ≤ lieH x1 x2 + alpha (h x1 x2) := by
  rcases hx with ⟨⟨_, hx1u⟩, ⟨_, hx2u⟩⟩
  unfold InC at hc
  rw [lieH_plus_alpha_eq_factorized]
  have hk : 0 ≤ 4 - 2 * x2 := by
    linarith
  nlinarith

/-- Boundary-only version: on `∂C = {h = 0}`, the Lie derivative is exactly zero. -/
lemma lieH_eq_zero_on_boundary {x1 x2 : ℝ} (hb : OnBoundaryC x1 x2) :
    lieH x1 x2 = 0 := by
  unfold OnBoundaryC at hb
  rw [lieH_eq_darboux, hb]
  ring

lemma lieH_nonneg_on_boundary {x1 x2 : ℝ} (hb : OnBoundaryC x1 x2) :
    0 ≤ lieH x1 x2 := by
  rw [lieH_eq_zero_on_boundary hb]

/-- The gradient of `h` cannot vanish on the boundary `h = 0`. -/
lemma grad_nonzero_on_boundary {x1 x2 : ℝ} (hb : OnBoundaryC x1 x2) :
    hx1 x1 x2 ≠ 0 ∨ hx2 x1 x2 ≠ 0 := by
  by_contra hcontra
  push_neg at hcontra
  rcases hcontra with ⟨hhx1, hhx2⟩
  have hx1eq : x1 = (5/8 : ℝ) := by
    unfold hx1 at hhx1
    linarith
  have hx2eq : x2 = 0 := by
    unfold hx2 at hhx2
    linarith
  unfold OnBoundaryC at hb
  rw [hx1eq, hx2eq] at hb
  norm_num [h] at hb

/-- Equivalent packaging of regularity: the two partials are not both zero on `∂C`. -/
lemma grad_pair_ne_zero_on_boundary {x1 x2 : ℝ} (hb : OnBoundaryC x1 x2) :
    ¬ (hx1 x1 x2 = 0 ∧ hx2 x1 x2 = 0) := by
  intro hzero
  have hreg := grad_nonzero_on_boundary hb
  rcases hreg with h1 | h2
  · exact h1 hzero.1
  · exact h2 hzero.2

/-- Summary theorem for the `C`-based barrier certificate. -/
theorem barrier_certificate_on_C {x1 x2 : ℝ}
    (hx : InX x1 x2) :
    (Unsafe x1 x2 → h x1 x2 < 0) ∧
    ((InC x1 x2) → 0 ≤ lieH x1 x2 + alpha (h x1 x2)) := by
  constructor
  · intro hu
    exact h_neg_on_unsafe hu
  · intro hc
    exact flow_condition_on_C hx hc

/-- Summary theorem for the boundary-only certificate, including regularity. -/
theorem barrier_certificate_on_boundary {x1 x2 : ℝ} :
    (Unsafe x1 x2 → h x1 x2 < 0) ∧
    ((OnBoundaryC x1 x2) → 0 ≤ lieH x1 x2) ∧
    ((OnBoundaryC x1 x2) → (hx1 x1 x2 ≠ 0 ∨ hx2 x1 x2 ≠ 0)) := by
  constructor
  · intro hu
    exact h_neg_on_unsafe hu
  constructor
  · intro hb
    exact lieH_nonneg_on_boundary hb
  · intro hb
    exact grad_nonzero_on_boundary hb

/-- Same boundary-only certificate, but stated as “the gradient pair is not both zero”. -/
theorem barrier_certificate_on_boundary_pair_form {x1 x2 : ℝ} :
    (Unsafe x1 x2 → h x1 x2 < 0) ∧
    ((OnBoundaryC x1 x2) → 0 ≤ lieH x1 x2) ∧
    ((OnBoundaryC x1 x2) → ¬ (hx1 x1 x2 = 0 ∧ hx2 x1 x2 = 0)) := by
  constructor
  · intro hu
    exact h_neg_on_unsafe hu
  constructor
  · intro hb
    exact lieH_nonneg_on_boundary hb
  · intro hb
    exact grad_pair_ne_zero_on_boundary hb

end DarbouxBarrier1
