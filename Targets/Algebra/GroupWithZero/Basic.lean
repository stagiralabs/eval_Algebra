import VerifiedAgora.tagger
/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Logic.Unique
import Mathlib.Tactic.Conv

/-!
# Groups with an adjoined zero element

This file describes structures that are not usually studied on their own right in mathematics,
namely a special sort of monoid: apart from a distinguished “zero element” they form a group,
or in other words, they are groups with an adjoined zero element.

Examples are:

* division rings;
* the value monoid of a multiplicative valuation;
* in particular, the non-negative real numbers.

## Main definitions

Various lemmas about `GroupWithZero` and `CommGroupWithZero`.
To reduce import dependencies, the type-classes themselves are in
`Algebra.GroupWithZero.Defs`.

## Implementation details

As is usual in mathlib, we extend the inverse function to the zero element,
and require `0⁻¹ = 0`.

-/

assert_not_exists DenselyOrdered

open Function

variable {M₀ G₀ : Type*}

section

section MulZeroClass

variable [MulZeroClass M₀] {a b : M₀}

@[target]
theorem left_ne_zero_of_mul : a * b ≠ 0 → a ≠ 0 :=
  sorry

theorem right_ne_zero_of_mul : a * b ≠ 0 → b ≠ 0 :=
  mt (mul_eq_zero_of_right a)

@[target]
theorem ne_zero_and_ne_zero_of_mul (h : a * b ≠ 0) : a ≠ 0 ∧ b ≠ 0 :=
  sorry

theorem mul_eq_zero_of_ne_zero_imp_eq_zero {a b : M₀} (h : a ≠ 0 → b = 0) : a * b = 0 := by
  have : Decidable (a = 0) := Classical.propDecidable (a = 0)
  exact if ha : a = 0 then by rw [ha, zero_mul] else by rw [h ha, mul_zero]

/-- To match `one_mul_eq_id`. -/
@[target]
theorem zero_mul_eq_const : ((0 : M₀) * ·) = Function.const _ 0 :=
  sorry
@[target]
theorem mul_zero_eq_const : (· * (0 : M₀)) = Function.const _ 0 :=
  sorry

end MulZeroClass

section Mul

variable [Mul M₀] [Zero M₀] [NoZeroDivisors M₀] {a b : M₀}

@[target]
theorem eq_zero_of_mul_self_eq_zero (h : a * a = 0) : a = 0 :=
  sorry

@[field_simps]
theorem mul_ne_zero (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 :=
  mt eq_zero_or_eq_zero_of_mul_eq_zero <| not_or.mpr ⟨ha, hb⟩

end Mul

namespace NeZero

instance mul [Zero M₀] [Mul M₀] [NoZeroDivisors M₀] {x y : M₀} [NeZero x] [NeZero y] :
    NeZero (x * y) :=
  ⟨mul_ne_zero out out⟩

end NeZero

end

section

variable [MulZeroOneClass M₀]

/-- In a monoid with zero, if zero equals one, then zero is the only element. -/
@[target]
theorem eq_zero_of_zero_eq_one (h : (0 : M₀) = 1) (a : M₀) : a = 0 := by sorry
def uniqueOfZeroEqOne (h : (0 : M₀) = 1) : Unique M₀ where
  default := 0
  uniq := eq_zero_of_zero_eq_one h

/-- In a monoid with zero, zero equals one if and only if all elements of that semiring
are equal. -/
theorem subsingleton_iff_zero_eq_one : (0 : M₀) = 1 ↔ Subsingleton M₀ :=
  ⟨fun h => haveI := uniqueOfZeroEqOne h; inferInstance, fun h => @Subsingleton.elim _ h _ _⟩

alias ⟨subsingleton_of_zero_eq_one, _⟩ := subsingleton_iff_zero_eq_one

@[target]
theorem eq_of_zero_eq_one (h : (0 : M₀) = 1) (a b : M₀) : a = b :=
  sorry
@[target]
theorem zero_ne_one_or_forall_eq_0 : (0 : M₀) ≠ 1 ∨ ∀ a : M₀, a = 0 :=
  sorry

variable [MulZeroOneClass M₀] [Nontrivial M₀] {a b : M₀}

theorem left_ne_zero_of_mul_eq_one (h : a * b = 1) : a ≠ 0 :=
  left_ne_zero_of_mul <| ne_zero_of_eq_one h

@[target]
theorem right_ne_zero_of_mul_eq_one (h : a * b = 1) : b ≠ 0 :=
  sorry

section MonoidWithZero
variable [MonoidWithZero M₀] {a : M₀} {n : ℕ}

@[simp] lemma zero_pow : ∀ {n : ℕ}, n ≠ 0 → (0 : M₀) ^ n = 0
  | n + 1, _ => by rw [pow_succ, mul_zero]

lemma zero_pow_eq (n : ℕ) : (0 : M₀) ^ n = if n = 0 then 1 else 0 := by
  split_ifs with h
  · rw [h, pow_zero]
  · rw [zero_pow h]

lemma zero_pow_eq_one₀ [Nontrivial M₀] : (0 : M₀) ^ n = 1 ↔ n = 0 := by
  rw [zero_pow_eq, one_ne_zero.ite_eq_left_iff]

@[target]
lemma pow_eq_zero_of_le : ∀ {m n}, m ≤ n → a ^ m = 0 → a ^ n = 0
  | _, _, Nat.le.refl, ha => ha
  | _, _, Nat.le.step hmn, ha => by rw [pow_succ, pow_eq_zero_of_le hmn ha, zero_mul]

lemma ne_zero_pow (hn : n ≠ 0) (ha : a ^ n ≠ 0) : a ≠ 0 := by sorry

@[simp]
lemma zero_pow_eq_zero [Nontrivial M₀] : (0 : M₀) ^ n = 0 ↔ n ≠ 0 :=
  ⟨by rintro h rfl; simp at h, zero_pow⟩

@[target]
lemma pow_mul_eq_zero_of_le {a b : M₀} {m n : ℕ} (hmn : m ≤ n)
    (h : a ^ m * b = 0) : a ^ n * b = 0 := by sorry

variable [NoZeroDivisors M₀]

lemma pow_eq_zero : ∀ {n}, a ^ n = 0 → a = 0
  | 0, ha => by simpa using congr_arg (a * ·) ha
  | n + 1, ha => by rw [pow_succ, mul_eq_zero] at ha; exact ha.elim pow_eq_zero id

@[simp] lemma pow_eq_zero_iff (hn : n ≠ 0) : a ^ n = 0 ↔ a = 0 :=
  ⟨pow_eq_zero, by rintro rfl; exact zero_pow hn⟩

lemma pow_ne_zero_iff (hn : n ≠ 0) : a ^ n ≠ 0 ↔ a ≠ 0 := (pow_eq_zero_iff hn).not

@[field_simps]
lemma pow_ne_zero (n : ℕ) (h : a ≠ 0) : a ^ n ≠ 0 := mt pow_eq_zero h

instance NeZero.pow [NeZero a] : NeZero (a ^ n) := ⟨pow_ne_zero n NeZero.out⟩

@[target]
lemma sq_eq_zero_iff : a ^ 2 = 0 ↔ a = 0 := sorry

@[simp] lemma pow_eq_zero_iff' [Nontrivial M₀] : a ^ n = 0 ↔ a = 0 ∧ n ≠ 0 := by
  obtain rfl | hn := eq_or_ne n 0 <;> simp [*]

theorem exists_right_inv_of_exists_left_inv {α} [MonoidWithZero α]
    (h : ∀ a : α, a ≠ 0 → ∃ b : α, b * a = 1) {a : α} (ha : a ≠ 0) : ∃ b : α, a * b = 1 := by
  obtain _ | _ := subsingleton_or_nontrivial α
  · exact ⟨a, Subsingleton.elim _ _⟩
  obtain ⟨b, hb⟩ := h a ha
  obtain ⟨c, hc⟩ := h b (left_ne_zero_of_mul <| hb.trans_ne one_ne_zero)
  refine ⟨b, ?_⟩
  conv_lhs => rw [← one_mul (a * b), ← hc, mul_assoc, ← mul_assoc b, hb, one_mul, hc]

end MonoidWithZero

section CancelMonoidWithZero

variable [CancelMonoidWithZero M₀] {a b c : M₀}

-- see Note [lower instance priority]
instance (priority := 10) CancelMonoidWithZero.to_noZeroDivisors : NoZeroDivisors M₀ :=
  ⟨fun ab0 => or_iff_not_imp_left.mpr fun ha => mul_left_cancel₀ ha <|
    ab0.trans (mul_zero _).symm⟩

@[target, simp]
theorem mul_eq_mul_right_iff : a * c = b * c ↔ a = b ∨ c = 0 := by sorry

@[simp]
theorem mul_eq_mul_left_iff : a * b = a * c ↔ b = c ∨ a = 0 := by
  by_cases ha : a = 0 <;> [simp only [ha, zero_mul, or_true]; simp [mul_right_inj', ha]]

theorem mul_right_eq_self₀ : a * b = a ↔ b = 1 ∨ a = 0 :=
  calc
    a * b = a ↔ a * b = a * 1 := by rw [mul_one]
    _ ↔ b = 1 ∨ a = 0 := mul_eq_mul_left_iff

@[target]
theorem mul_left_eq_self₀ : a * b = b ↔ a = 1 ∨ b = 0 :=
  sorry

@[simp]
theorem mul_eq_left₀ (ha : a ≠ 0) : a * b = a ↔ b = 1 := by
  rw [Iff.comm, ← mul_right_inj' ha, mul_one]

@[simp]
theorem mul_eq_right₀ (hb : b ≠ 0) : a * b = b ↔ a = 1 := by
  rw [Iff.comm, ← mul_left_inj' hb, one_mul]

@[target, simp]
theorem left_eq_mul₀ (ha : a ≠ 0) : a = a * b ↔ b = 1 := by sorry

@[target, simp]
theorem right_eq_mul₀ (hb : b ≠ 0) : b = a * b ↔ a = 1 := by sorry
@[target]
theorem eq_zero_of_mul_eq_self_right (h₁ : b ≠ 1) (h₂ : a * b = a) : a = 0 :=
  sorry
@[target]
theorem eq_zero_of_mul_eq_self_left (h₁ : b ≠ 1) (h₂ : b * a = a) : a = 0 :=
  sorry

end CancelMonoidWithZero

section GroupWithZero

variable [GroupWithZero G₀] {a b x : G₀}

theorem GroupWithZero.mul_right_injective (h : x ≠ 0) :
    Function.Injective fun y => x * y := fun y y' w => by
  simpa only [← mul_assoc, inv_mul_cancel₀ h, one_mul] using congr_arg (fun y => x⁻¹ * y) w

@[target]
theorem GroupWithZero.mul_left_injective (h : x ≠ 0) :
    Function.Injective fun y => y * x := sorry

@[target, simp]
theorem inv_mul_cancel_right₀ (h : b ≠ 0) (a : G₀) : a * b⁻¹ * b = a :=
  sorry


@[target, simp]
theorem inv_mul_cancel_left₀ (h : a ≠ 0) (b : G₀) : a⁻¹ * (a * b) = b :=
  sorry

-- See note [lower instance priority]
instance (priority := 100) GroupWithZero.toDivisionMonoid : DivisionMonoid G₀ :=
  { ‹GroupWithZero G₀› with
    inv := Inv.inv,
    inv_inv := fun a => by
      by_cases h : a = 0
      · simp [h]
      · exact left_inv_eq_right_inv (inv_mul_cancel₀ <| inv_ne_zero h) (inv_mul_cancel₀ h)
        ,
    mul_inv_rev := fun a b => by
      by_cases ha : a = 0
      · simp [ha]
      by_cases hb : b = 0
      · simp [hb]
      apply inv_eq_of_mul
      simp [mul_assoc, ha, hb],
    inv_eq_of_mul := fun _ _ => inv_eq_of_mul }

-- see Note [lower instance priority]
instance (priority := 10) GroupWithZero.toCancelMonoidWithZero : CancelMonoidWithZero G₀ :=
  { (‹_› : GroupWithZero G₀) with
    mul_left_cancel_of_ne_zero := @fun x y z hx h => by
      rw [← inv_mul_cancel_left₀ hx y, h, inv_mul_cancel_left₀ hx z],
    mul_right_cancel_of_ne_zero := @fun x y z hy h => by
      rw [← mul_inv_cancel_right₀ hy x, h, mul_inv_cancel_right₀ hy z] }

end GroupWithZero

section GroupWithZero

variable [GroupWithZero G₀] {a : G₀}

@[target, simp]
theorem zero_div (a : G₀) : 0 / a = 0 := by sorry

@[target, simp]
theorem div_zero (a : G₀) : a / 0 = 0 := by sorry
@[target, simp]
theorem mul_self_mul_inv (a : G₀) : a * a * a⁻¹ = a := by sorry
@[target, simp]
theorem mul_inv_mul_cancel (a : G₀) : a * a⁻¹ * a = a := by sorry
@[target, simp]
theorem inv_mul_mul_self (a : G₀) : a⁻¹ * a * a = a := by sorry
@[simp]
theorem mul_self_div_self (a : G₀) : a * a / a = a := by rw [div_eq_mul_inv, mul_self_mul_inv a]

/-- Dividing `a` by itself and then multiplying by itself results in `a`, whether or not `a` is
zero. -/
@[simp]
theorem div_self_mul_self (a : G₀) : a / a * a = a := by rw [div_eq_mul_inv, mul_inv_mul_cancel a]

attribute [local simp] div_eq_mul_inv mul_comm mul_assoc mul_left_comm

@[target, simp]
theorem div_self_mul_self' (a : G₀) : a / (a * a) = a⁻¹ :=
  sorry


theorem one_div_ne_zero {a : G₀} (h : a ≠ 0) : 1 / a ≠ 0 := by
  simpa only [one_div] using inv_ne_zero h

@[target, simp]
theorem inv_eq_zero {a : G₀} : a⁻¹ = 0 ↔ a = 0 := by sorry

@[simp]
theorem zero_eq_inv {a : G₀} : 0 = a⁻¹ ↔ 0 = a :=
  eq_comm.trans <| inv_eq_zero.trans eq_comm

/-- Dividing `a` by the result of dividing `a` by itself results in
`a` (whether or not `a` is zero). -/
@[simp]
theorem div_div_self (a : G₀) : a / (a / a) = a := by
  rw [div_div_eq_mul_div]
  exact mul_self_div_self a

@[target]
theorem ne_zero_of_one_div_ne_zero {a : G₀} (h : 1 / a ≠ 0) : a ≠ 0 := sorry

theorem eq_zero_of_one_div_eq_zero {a : G₀} (h : 1 / a = 0) : a = 0 :=
  Classical.byCases (fun ha => ha) fun ha => ((one_div_ne_zero ha) h).elim

@[target]
theorem mul_left_surjective₀ {a : G₀} (h : a ≠ 0) : Surjective fun g => a * g := sorry

@[target]
theorem mul_right_surjective₀ {a : G₀} (h : a ≠ 0) : Surjective fun g => g * a := sorry

@[target]
lemma zero_zpow : ∀ n : ℤ, n ≠ 0 → (0 : G₀) ^ n = 0
  | (n : ℕ), h => by rw [zpow_natCast, zero_pow]; simpa [Int.natCast_eq_zero] using h
  | .negSucc n, _ => by simp

lemma zero_zpow_eq (n : ℤ) : (0 : G₀) ^ n = if n = 0 then 1 else 0 := by sorry

lemma zero_zpow_eq_one₀ {n : ℤ} : (0 : G₀) ^ n = 1 ↔ n = 0 := by
  rw [zero_zpow_eq, one_ne_zero.ite_eq_left_iff]

@[target]
lemma zpow_add_one₀ (ha : a ≠ 0) : ∀ n : ℤ, a ^ (n + 1) = a ^ n * a
  | (n : ℕ) => by simp only [← Int.ofNat_succ, zpow_natCast, pow_succ]
  | .negSucc 0 => by simp [ha]
  | .negSucc (n + 1) => by
    rw [Int.negSucc_eq, zpow_neg, Int.neg_add, Int.neg_add_cancel_right, zpow_neg, ← Int.ofNat_succ,
      zpow_natCast, zpow_natCast, pow_succ' _ (n + 1), mul_inv_rev, mul_assoc, inv_mul_cancel₀ ha,
      mul_one]

lemma zpow_sub_one₀ (ha : a ≠ 0) (n : ℤ) : a ^ (n - 1) = a ^ n * a⁻¹ :=
  sorry

@[target]
lemma zpow_add₀ (ha : a ≠ 0) (m n : ℤ) : a ^ (m + n) = a ^ m * a ^ n := by sorry

@[target]
lemma zpow_add' {m n : ℤ} (h : a ≠ 0 ∨ m + n ≠ 0 ∨ m = 0 ∧ n = 0) :
    a ^ (m + n) = a ^ m * a ^ n := by sorry

lemma zpow_one_add₀ (h : a ≠ 0) (i : ℤ) : a ^ (1 + i) = a * a ^ i := by rw [zpow_add₀ h, zpow_one]

end GroupWithZero

section CommGroupWithZero

variable [CommGroupWithZero G₀]

@[target]
theorem div_mul_eq_mul_div₀ (a b c : G₀) : a / c * b = a * b / c := by sorry

@[target]
lemma div_sq_cancel (a b : G₀) : a ^ 2 * b / a = a * b := by sorry

end CommGroupWithZero
