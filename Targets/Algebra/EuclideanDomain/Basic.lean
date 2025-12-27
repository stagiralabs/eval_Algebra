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

@[target]
theorem val_dvd_le : ∀ a b : R, b ∣ a → a ≠ 0 → ¬a ≺ b
  | _, b, ⟨d, rfl⟩, ha => mul_left_not_lt b (mt (by rintro rfl; exact mul_zero _) ha)

@[simp]
theorem mod_eq_zero {a b : R} : a % b = 0 ↔ b ∣ a :=
  sorry

@[target, simp]
theorem mod_self (a : R) : a % a = 0 :=
  sorry

theorem dvd_mod_iff {a b c : R} (h : c ∣ b) : c ∣ a % b ↔ c ∣ a := by
  rw [← dvd_add_right (h.mul_right _), div_add_mod]

@[target, simp]
theorem mod_one (a : R) : a % 1 = 0 :=
  sorry

@[target, simp]
theorem zero_mod (b : R) : 0 % b = 0 :=
  sorry

@[target, simp]
theorem zero_div {a : R} : 0 / a = 0 :=
  sorry

@[simp]
theorem div_self {a : R} (a0 : a ≠ 0) : a / a = 1 := by
  simpa only [one_mul] using mul_div_cancel_right₀ 1 a0

theorem eq_div_of_mul_eq_left {a b c : R} (hb : b ≠ 0) (h : a * b = c) : a = c / b := by
  rw [← h, mul_div_cancel_right₀ _ hb]

@[target]
theorem eq_div_of_mul_eq_right {a b c : R} (ha : a ≠ 0) (h : a * b = c) : b = c / a := by sorry

theorem mul_div_assoc (x : R) {y z : R} (h : z ∣ y) : x * y / z = x * (y / z) := by
  by_cases hz : z = 0
  · subst hz
    rw [div_zero, div_zero, mul_zero]
  rcases h with ⟨p, rfl⟩
  rw [mul_div_cancel_left₀ _ hz, mul_left_comm, mul_div_cancel_left₀ _ hz]

protected theorem mul_div_cancel' {a b : R} (hb : b ≠ 0) (hab : b ∣ a) : b * (a / b) = a := by
  rw [← mul_div_assoc _ hab, mul_div_cancel_left₀ _ hb]

-- This generalizes `Int.div_one`, see note [simp-normal form]
@[target, simp]
theorem div_one (p : R) : p / 1 = p :=
  sorry

@[target]
theorem div_dvd_of_dvd {p q : R} (hpq : q ∣ p) : p / q ∣ p := by sorry

@[target]
theorem dvd_div_of_mul_dvd {a b c : R} (h : a * b ∣ c) : b ∣ c / a := by sorry

section GCD

variable [DecidableEq R]

@[simp]
theorem gcd_zero_right (a : R) : gcd a 0 = a := by
  rw [gcd]
  split_ifs with h <;> simp only [h, zero_mod, gcd_zero_left]

theorem gcd_val (a b : R) : gcd a b = gcd (b % a) a := by
  rw [gcd]
  split_ifs with h <;> [simp only [h, mod_zero, gcd_zero_right]; rfl]

theorem gcd_dvd (a b : R) : gcd a b ∣ a ∧ gcd a b ∣ b :=
  GCD.induction a b
    (fun b => by
      rw [gcd_zero_left]
      exact ⟨dvd_zero _, dvd_rfl⟩)
    fun a b _ ⟨IH₁, IH₂⟩ => by
    rw [gcd_val]
    exact ⟨IH₂, (dvd_mod_iff IH₂).1 IH₁⟩

@[target]
theorem gcd_dvd_left (a b : R) : gcd a b ∣ a :=
  sorry

theorem gcd_dvd_right (a b : R) : gcd a b ∣ b :=
  (gcd_dvd a b).right

protected theorem gcd_eq_zero_iff {a b : R} : gcd a b = 0 ↔ a = 0 ∧ b = 0 :=
  ⟨fun h => by simpa [h] using gcd_dvd a b, by
    rintro ⟨rfl, rfl⟩
    exact gcd_zero_right _⟩

theorem dvd_gcd {a b c : R} : c ∣ a → c ∣ b → c ∣ gcd a b :=
  GCD.induction a b (fun _ _ H => by simpa only [gcd_zero_left] using H) fun a b _ IH ca cb => by
    rw [gcd_val]
    exact IH ((dvd_mod_iff ca).2 cb) ca

@[target]
theorem gcd_eq_left {a b : R} : gcd a b = a ↔ a ∣ b :=
  sorry

@[simp]
theorem gcd_one_left (a : R) : gcd 1 a = 1 :=
  gcd_eq_left.2 (one_dvd _)

@[simp]
theorem gcd_self (a : R) : gcd a a = a :=
  gcd_eq_left.2 dvd_rfl

@[simp]
theorem xgcdAux_fst (x y : R) : ∀ s t s' t', (xgcdAux x s t y s' t').1 = gcd x y :=
  GCD.induction x y
    (by
      intros
      rw [xgcd_zero_left, gcd_zero_left])
    fun x y h IH s t s' t' => by
    simp only [xgcdAux_rec h, if_neg h, IH]
    rw [← gcd_val]

@[target]
theorem xgcdAux_val (x y : R) : xgcdAux x 1 0 y 0 1 = (gcd x y, xgcd x y) := by sorry

@[target]
theorem xgcdAux_P (a b : R) {r r' : R} {s t s' t'} (p : P a b (r, s, t))
    (p' : P a b (r', s', t')) : P a b (xgcdAux r s t r' s' t') := by sorry
@[target]
theorem gcd_eq_gcd_ab (a b : R) : (gcd a b : R) = a * gcdA a b + b * gcdB a b := by sorry

-- see Note [lower instance priority]
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

theorem dvd_lcm_left (x y : R) : x ∣ lcm x y :=
  by_cases
    (fun hxy : gcd x y = 0 => by
      rw [lcm, hxy, div_zero]
      exact dvd_zero _)
    fun hxy =>
    let ⟨z, hz⟩ := (gcd_dvd x y).2
    ⟨z, Eq.symm <| eq_div_of_mul_eq_left hxy <| by rw [mul_right_comm, mul_assoc, ← hz]⟩

@[target]
theorem dvd_lcm_right (x y : R) : y ∣ lcm x y :=
  sorry

theorem lcm_dvd {x y z : R} (hxz : x ∣ z) (hyz : y ∣ z) : lcm x y ∣ z := by
  rw [lcm]
  by_cases hxy : gcd x y = 0
  · rw [hxy, div_zero]
    rw [EuclideanDomain.gcd_eq_zero_iff] at hxy
    rwa [hxy.1] at hxz
  rcases gcd_dvd x y with ⟨⟨r, hr⟩, ⟨s, hs⟩⟩
  suffices x * y ∣ z * gcd x y by
    obtain ⟨p, hp⟩ := this
    use p
    generalize gcd x y = g at hxy hs hp ⊢
    subst hs
    rw [mul_left_comm, mul_div_cancel_left₀ _ hxy, ← mul_left_inj' hxy, hp]
    rw [← mul_assoc]
    simp only [mul_right_comm]
  rw [gcd_eq_gcd_ab, mul_add]
  apply dvd_add
  · rw [mul_left_comm]
    exact mul_dvd_mul_left _ (hyz.mul_right _)
  · rw [mul_left_comm, mul_comm]
    exact mul_dvd_mul_left _ (hxz.mul_right _)

@[simp]
theorem lcm_dvd_iff {x y z : R} : lcm x y ∣ z ↔ x ∣ z ∧ y ∣ z :=
  ⟨fun hz => ⟨(dvd_lcm_left _ _).trans hz, (dvd_lcm_right _ _).trans hz⟩, fun ⟨hxz, hyz⟩ =>
    lcm_dvd hxz hyz⟩

@[simp]
theorem lcm_zero_left (x : R) : lcm 0 x = 0 := by rw [lcm, zero_mul, zero_div]

@[target, simp]
theorem lcm_zero_right (x : R) : lcm x 0 = 0 := by sorry

@[simp]
theorem lcm_eq_zero_iff {x y : R} : lcm x y = 0 ↔ x = 0 ∨ y = 0 := by
  constructor
  · intro hxy
    rw [lcm, mul_div_assoc _ (gcd_dvd_right _ _), mul_eq_zero] at hxy
    apply Or.imp_right _ hxy
    intro hy
    by_cases hgxy : gcd x y = 0
    · rw [EuclideanDomain.gcd_eq_zero_iff] at hgxy
      exact hgxy.2
    · rcases gcd_dvd x y with ⟨⟨r, hr⟩, ⟨s, hs⟩⟩
      generalize gcd x y = g at hr hs hy hgxy ⊢
      subst hs
      rw [mul_div_cancel_left₀ _ hgxy] at hy
      rw [hy, mul_zero]
  rintro (hx | hy)
  · rw [hx, lcm_zero_left]
  · rw [hy, lcm_zero_right]

@[target, simp]
theorem gcd_mul_lcm (x y : R) : gcd x y * lcm x y = x * y := by sorry

end LCM

section Div

@[target]
theorem mul_div_mul_cancel {a b c : R} (ha : a ≠ 0) (hcb : c ∣ b) : a * b / (a * c) = b / c := by sorry

theorem mul_div_mul_comm_of_dvd_dvd {a b c d : R} (hac : c ∣ a) (hbd : d ∣ b) :
    a * b / (c * d) = a / c * (b / d) := by
  rcases eq_or_ne c 0 with (rfl | hc0); · simp
  rcases eq_or_ne d 0 with (rfl | hd0); · simp
  obtain ⟨k1, rfl⟩ := hac
  obtain ⟨k2, rfl⟩ := hbd
  rw [mul_div_cancel_left₀ _ hc0, mul_div_cancel_left₀ _ hd0, mul_mul_mul_comm,
    mul_div_cancel_left₀ _ (mul_ne_zero hc0 hd0)]

end Div

end EuclideanDomain
