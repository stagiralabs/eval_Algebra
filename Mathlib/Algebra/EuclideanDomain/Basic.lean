import VerifiedAgora.tagger
/-
Copyright (c) 2018 Louis Carlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Louis Carlin, Mario Carneiro
-/
import Mathlib.Algebra.EuclideanDomain.Defs
import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.Algebra.Ring.Regular
import Mathlib.Algebra.GroupWithZero.Divisibility
import Mathlib.Algebra.Ring.Basic

/-!
# Lemmas about Euclidean domains

## Main statements

* `gcd_eq_gcd_ab`: states Bézout's lemma for Euclidean domains.

-/


universe u

namespace EuclideanDomain

variable {R : Type u}
variable [EuclideanDomain R]

/-- The well founded relation in a Euclidean Domain satisfying `a % b ≺ b` for `b ≠ 0` -/
local infixl:50 " ≺ " => EuclideanDomain.r

-- See note [lower instance priority]
instance (priority := 100) toMulDivCancelClass : MulDivCancelClass R where
  mul_div_cancel a b hb := by
    refine (eq_of_sub_eq_zero ?_).symm
    by_contra h
    have := mul_right_not_lt b h
    rw [sub_mul, mul_comm (_ / _), sub_eq_iff_eq_add'.2 (div_add_mod (a * b) b).symm] at this
    exact this (mod_lt _ hb)

theorem mod_eq_sub_mul_div {R : Type*} [EuclideanDomain R] (a b : R) : a % b = a - b * (a / b) :=
  calc
    a % b = b * (a / b) + a % b - b * (a / b) := (add_sub_cancel_left _ _).symm
    _ = a - b * (a / b) := by rw [div_add_mod]

@[target] theorem val_dvd_le : ∀ a b : R, b ∣ a → a ≠ 0 → ¬a ≺ b
  | _, b, ⟨d, rfl⟩, ha => mul_left_not_lt b (mt (by sorry


@[simp]
theorem mod_eq_zero {a b : R} : a % b = 0 ↔ b ∣ a :=
  ⟨fun h => by
    rw [← div_add_mod a b, h, add_zero]
    exact dvd_mul_right _ _, fun ⟨c, e⟩ => by
    rw [e, ← add_left_cancel_iff, div_add_mod, add_zero]
    haveI := Classical.dec
    by_cases b0 : b = 0
    · simp only [b0, zero_mul]
    · rw [mul_div_cancel_left₀ _ b0]⟩

@[target] theorem mod_self (a : R) : a % a = 0 := by sorry


@[target] theorem dvd_mod_iff {a b c : R} (h : c ∣ b) : c ∣ a % b ↔ c ∣ a := by
  sorry


@[target] theorem mod_one (a : R) : a % 1 = 0 := by sorry


@[target] theorem zero_mod (b : R) : 0 % b = 0 := by sorry


@[target] theorem zero_div (a : G₀) : 0 / a = 0 := by sorry


@[target] theorem div_self {a : R} (a0 : a ≠ 0) : a / a = 1 := by
  sorry


@[target] theorem eq_div_of_mul_eq_left {a b c : R} (hb : b ≠ 0) (h : a * b = c) : a = c / b := by
  sorry


@[target] theorem eq_div_of_mul_eq_right {a b c : R} (ha : a ≠ 0) (h : a * b = c) : b = c / a := by
  sorry


@[target] theorem mul_div_assoc (a b c : G) : a * b / c = a * (b / c) := by
  sorry


protected theorem mul_div_cancel' {a b : R} (hb : b ≠ 0) (hab : b ∣ a) : b * (a / b) = a := by
  rw [← mul_div_assoc _ hab, mul_div_cancel_left₀ _ hb]

-- This generalizes `Int.div_one`, see note [simp-normal form]
@[target] theorem div_one (a : G) : a / 1 = a := by sorry


@[target] theorem div_dvd_of_dvd {p q : R} (hpq : q ∣ p) : p / q ∣ p := by
  sorry


@[target] theorem dvd_div_of_mul_dvd {a b c : R} (h : a * b ∣ c) : b ∣ c / a := by
  sorry


section GCD

variable [DecidableEq R]

@[target] theorem gcd_zero_right (a : R) : gcd a 0 = a := by
  sorry


@[target] theorem gcd_val (a b : R) : gcd a b = gcd (b % a) a := by
  sorry


theorem gcd_dvd (a b : R) : gcd a b ∣ a ∧ gcd a b ∣ b :=
  GCD.induction a b
    (fun b => by
      rw [gcd_zero_left]
      exact ⟨dvd_zero _, dvd_rfl⟩)
    fun a b _ ⟨IH₁, IH₂⟩ => by
    rw [gcd_val]
    exact ⟨IH₂, (dvd_mod_iff IH₂).1 IH₁⟩

theorem gcd_dvd_left (a b : R) : gcd a b ∣ a :=
  (gcd_dvd a b).left

theorem gcd_dvd_right (a b : R) : gcd a b ∣ b :=
  (gcd_dvd a b).right

protected theorem gcd_eq_zero_iff {a b : R} : gcd a b = 0 ↔ a = 0 ∧ b = 0 :=
  ⟨fun h => by simpa [h] using gcd_dvd a b, by
    rintro ⟨rfl, rfl⟩
    exact gcd_zero_right _⟩

@[target] theorem dvd_gcd {a b c : R} : c ∣ a → c ∣ b → c ∣ gcd a b :=
  GCD.induction a b (fun _ _ H => by sorry


@[target] theorem gcd_eq_left {a b : R} : gcd a b = a ↔ a ∣ b :=
  ⟨fun h => by
    sorry


@[target] theorem gcd_one_left (a : R) : gcd 1 a = 1 := by sorry


@[target] theorem gcd_self (a : R) : gcd a a = a := by sorry


@[target] theorem xgcdAux_fst (x y : R) : ∀ s t s' t', (xgcdAux x s t y s' t').1 = gcd x y :=
  GCD.induction x y
    (by
      sorry


@[target] theorem xgcdAux_val (x y : R) : xgcdAux x 1 0 y 0 1 = (gcd x y, xgcd x y) := by
  sorry


private def P (a b : R) : R × R × R → Prop
  | (r, s, t) => (r : R) = a * s + b * t

@[target] theorem xgcdAux_P (a b : R) {r r' : R} {s t s' t'} (p : P a b (r, s, t))
    (p' : P a b (r', s', t')) : P a b (xgcdAux r s t r' s' t') := by
  sorry


/-- An explicit version of **Bézout's lemma** for Euclidean domains. -/
/-- An explicit version of **Bézout's lemma** for Euclidean domains. -/
@[target] theorem gcd_eq_gcd_ab (a b : R) : (gcd a b : R) = a * gcdA a b + b * gcdB a b := by
  sorry

instance (priority := 70) (R : Type*) [e : EuclideanDomain R] : NoZeroDivisors R :=
  haveI := Classical.decEq R
  { eq_zero_or_eq_zero_of_mul_eq_zero := fun {a b} h =>
      or_iff_not_and_not.2 fun h0 => h0.1 <| by rw [← mul_div_cancel_right₀ a h0.2, h, zero_div] }

-- see Note [lower instance priority]
instance (priority := 70) (R : Type*) [e : EuclideanDomain R] : IsDomain R :=
  { e, NoZeroDivisors.to_isDomain R with }

end GCD

section LCM

variable [DecidableEq R]

@[target] theorem dvd_lcm_left (x y : R) : x ∣ lcm x y :=
  by_cases
    (fun hxy : gcd x y = 0 => by
      sorry


@[target] theorem dvd_lcm_right (x y : R) : y ∣ lcm x y :=
  by_cases
    (fun hxy : gcd x y = 0 => by
      sorry


@[target] theorem lcm_dvd {x y z : R} (hxz : x ∣ z) (hyz : y ∣ z) : lcm x y ∣ z := by
  sorry


@[simp]
theorem lcm_dvd_iff {x y z : R} : lcm x y ∣ z ↔ x ∣ z ∧ y ∣ z :=
  ⟨fun hz => ⟨(dvd_lcm_left _ _).trans hz, (dvd_lcm_right _ _).trans hz⟩, fun ⟨hxz, hyz⟩ =>
    lcm_dvd hxz hyz⟩

@[target] theorem lcm_zero_left (x : R) : lcm 0 x = 0 := by sorry


@[target] theorem lcm_zero_right (x : R) : lcm x 0 = 0 := by sorry


@[target] theorem lcm_eq_zero_iff {x y : R} : lcm x y = 0 ↔ x = 0 ∨ y = 0 := by
  sorry


@[target] theorem gcd_mul_lcm (x y : R) : gcd x y * lcm x y = x * y := by
  sorry


end LCM

section Div

theorem mul_div_mul_cancel {a b c : R} (ha : a ≠ 0) (hcb : c ∣ b) : a * b / (a * c) = b / c := by
  by_cases hc : c = 0; · simp [hc]
  refine eq_div_of_mul_eq_right hc (mul_left_cancel₀ ha ?_)
  rw [← mul_assoc, ← mul_div_assoc _ (mul_dvd_mul_left a hcb),
    mul_div_cancel_left₀ _ (mul_ne_zero ha hc)]

@[target] theorem mul_div_mul_comm_of_dvd_dvd {a b c d : R} (hac : c ∣ a) (hbd : d ∣ b) :
    a * b / (c * d) = a / c * (b / d) := by
  sorry


end Div

end EuclideanDomain
