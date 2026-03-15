import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic

-- ============================================================
-- 1. Definition of invariant set (corresponding to Definition 1.1)
-- C is a subset of ℝ and f is the system dynamics
-- ============================================================

def IsInvariant (f : ℝ → ℝ) (C : Set ℝ) : Prop :=
  ∀ x, x ∈ C → f x ∈ C


-- ============================================================
-- 2. Definition of system dynamics and safety set
-- System dynamics: f(x) = a * x
-- Safety set: S = [-1, 1]
-- ============================================================

def f (a : ℝ) (x : ℝ) : ℝ := a * x

def S : Set ℝ := Set.Icc (-1) 1


-- ============================================================
-- Method 1: Direct proof of invariance
-- Prove that S is invariant when |a| ≤ 1
-- ============================================================

theorem safety_set_invariant (a : ℝ) (ha : |a| ≤ 1) :
  IsInvariant (f a) S := by

  unfold IsInvariant
  intro x hx

  -- Expand the definition of S
  rw [S, Set.mem_Icc] at hx ⊢

  -- Use the identity |ax| = |a||x|
  have h_abs : |f a x| = |a| * |x| := by
    unfold f
    exact abs_mul a x

  -- Bound |a||x| using |a| ≤ 1 and |x| ≤ 1
  have h_bound : |a| * |x| ≤ 1 := by

    have h1 : |a| * |x| ≤ 1 * |x| := by
      apply mul_le_mul_of_nonneg_right ha
      exact abs_nonneg x

    have h2 : 1 * |x| ≤ 1 := by
      rw [one_mul]
      exact abs_le.mpr hx

    exact le_trans h1 h2

  -- Convert the absolute value bound back to interval form
  exact abs_le.mp (h_abs.symm ▸ h_bound)


-- ============================================================
-- Method 2: Barrier function construction
-- ============================================================

structure IsBarrierFunction
  (f : ℝ → ℝ) (S : Set ℝ) (B : ℝ → ℝ) (α : ℝ) : Prop where

  -- α must lie in (0,1]
  α_bounds : 0 < α ∧ α ≤ 1

  -- B(x) < 0 outside the safety set
  outside_safe : ∀ x, x ∉ S → B x < 0

  -- Barrier condition inside S
  barrier_condition :
    ∀ x, x ∈ S → B (f x) - α * B x ≥ 0


-- ============================================================
-- Set induced by barrier function
-- ============================================================

def InvariantSetFromB (S : Set ℝ) (B : ℝ → ℝ) : Set ℝ :=
  {x | x ∈ S ∧ B x ≥ 0}


-- ============================================================
-- The set induced by a valid barrier function is invariant
-- ============================================================

theorem invariant_from_barrier
  (f : ℝ → ℝ) (S : Set ℝ) (B : ℝ → ℝ) (α : ℝ)
  (hB : IsBarrierFunction f S B α) :

  ∀ x, x ∈ InvariantSetFromB S B →
       f x ∈ InvariantSetFromB S B := by

  intro x hx
  rcases hx with ⟨hxS, hxB⟩

  constructor

  · -- Prove f(x) ∈ S via contradiction
    by_contra h_not_S

    have h_neg := hB.outside_safe (f x) h_not_S
    have h_cond := hB.barrier_condition x hxS

    have h_ge_zero : B (f x) ≥ 0 := by
      have : α * B x ≥ 0 :=
        mul_nonneg (le_of_lt hB.α_bounds.1) hxB
      linarith

    linarith

  · -- Prove B(f(x)) ≥ 0
    have h_cond := hB.barrier_condition x hxS
    have : α * B x ≥ 0 :=
      mul_nonneg (le_of_lt hB.α_bounds.1) hxB
    linarith


-- ============================================================
-- Example 1
-- B(x) = 1 - x²
-- ============================================================

def f_ex (a x : ℝ) : ℝ := a * x

def S_ex : Set ℝ := Set.Icc (-1) 1

def B_ex (x : ℝ) : ℝ := 1 - x^2


theorem example_is_barrier (a : ℝ) (ha : |a| < 1) :
  IsBarrierFunction (f_ex a) S_ex B_ex 1 where

  α_bounds := ⟨by linarith, by linarith⟩

  outside_safe := by
    intro x hx
    unfold S_ex B_ex at *
    rw [Set.mem_Icc, not_and_or] at hx

    have : x^2 > 1 := by
      rcases hx with h_left | h_right
      · nlinarith
      · nlinarith

    linarith

  barrier_condition := by
    intro x hx
    unfold f_ex B_ex S_ex at *

    have h_a2 : a^2 < 1 := by
      nlinarith [abs_lt.mp ha]

    calc
      (1 - (a * x)^2) - 1 * (1 - x^2)
          = (1 - a^2) * x^2 := by ring
      _ ≥ 0 := by nlinarith


-- ============================================================
-- Example 2
-- ============================================================

def f_ex2 (a x : ℝ) : ℝ := a * x * (1 - x)

def S_ex2 : Set ℝ := Set.Icc 0 1

def B_ex2 (x : ℝ) : ℝ := x * (1 - x)


theorem example2_is_barrier
  (a : ℝ) (h_a_low : 0 < a) (h_a_high : a < 4) :

  IsBarrierFunction (f_ex2 a) S_ex2 B_ex2
    (a * (1 - a / 4)) where

  α_bounds := by
    constructor
    · nlinarith
    ·
      have h_quad :
        a * (1 - a / 4) =
        1 - (a - 2)^2 / 4 := by ring
      rw [h_quad]
      nlinarith

  outside_safe := by
    intro x hx
    unfold S_ex2 B_ex2 at *
    rw [Set.mem_Icc, not_and_or] at hx
    rcases hx with h_left | h_right
    · nlinarith
    · nlinarith

  barrier_condition := by

    intro x hx
    unfold f_ex2 B_ex2 S_ex2 at *
    rw [Set.mem_Icc] at hx

    let Bx := x * (1 - x)

    have hBx_ge : 0 ≤ Bx := by nlinarith

    have hBx_le : Bx ≤ 1 / 4 := by
      have : Bx = 1/4 - (x - 1/2)^2 := by ring
      nlinarith

    calc
      (a * x * (1 - x))
        * (1 - (a * x * (1 - x)))
        - (a * (1 - a / 4)) * (x * (1 - x))

        = (a * Bx) * (1 - a * Bx)
          - a * (1 - a / 4) * Bx := by ring

      _ = a * Bx * ((1 - a * Bx)
        - (1 - a / 4)) := by ring

      _ = a * Bx * (a / 4 - a * Bx) := by ring

      _ = a^2 * Bx * (1 / 4 - Bx) := by ring

      _ ≥ 0 := by
        apply mul_nonneg
        · apply mul_nonneg
            (pow_two_nonneg a) hBx_ge
        · linarith
