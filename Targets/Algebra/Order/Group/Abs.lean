import VerifiedAgora.tagger
/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow

/-!
# Absolute values in ordered groups

The absolute value of an element in a group which is also a lattice is its supremum with its
negation. This generalizes the usual absolute value on real numbers (`|x| = max x (-x)`).

## Notations

- `|a|`: The *absolute value* of an element `a` of an additive lattice ordered group
- `|a|ₘ`: The *absolute value* of an element `a` of a multiplicative lattice ordered group
-/

open Function

variable {α : Type*}

section LinearOrderedCommGroup
variable [LinearOrderedCommGroup α] {a b : α}

@[to_additive] lemma mabs_pow (n : ℕ) (a : α) : |a ^ n|ₘ = |a|ₘ ^ n := by
  obtain ha | ha := le_total a 1
  · rw [mabs_of_le_one ha, ← mabs_inv, ← inv_pow, mabs_of_one_le]
    exact one_le_pow_of_one_le' (one_le_inv'.2 ha) n
  · rw [mabs_of_one_le ha, mabs_of_one_le (one_le_pow_of_one_le' ha n)]

@[to_additive] private lemma mabs_mul_eq_mul_mabs_le (hab : a ≤ b) :
    |a * b|ₘ = |a|ₘ * |b|ₘ ↔ 1 ≤ a ∧ 1 ≤ b ∨ a ≤ 1 ∧ b ≤ 1 := by
  obtain ha | ha := le_or_lt 1 a <;> obtain hb | hb := le_or_lt 1 b
  · simp [ha, hb, mabs_of_one_le, one_le_mul ha hb]
  · exact (lt_irrefl (1 : α) <| ha.trans_lt <| hab.trans_lt hb).elim
  swap
  · simp [ha.le, hb.le, mabs_of_le_one, mul_le_one', mul_comm]
  have : (|a * b|ₘ = a⁻¹ * b ↔ b ≤ 1) ↔
    (|a * b|ₘ = |a|ₘ * |b|ₘ ↔ 1 ≤ a ∧ 1 ≤ b ∨ a ≤ 1 ∧ b ≤ 1) := by
    simp [ha.le, ha.not_le, hb, mabs_of_le_one, mabs_of_one_le]
  refine this.mp ⟨fun h ↦ ?_, fun h ↦ by simp only [h.antisymm hb, mabs_of_lt_one ha, mul_one]⟩
  obtain ab | ab := le_or_lt (a * b) 1
  · refine (eq_one_of_inv_eq' ?_).le
    rwa [mabs_of_le_one ab, mul_inv_rev, mul_comm, mul_right_inj] at h
  · rw [mabs_of_one_lt ab, mul_left_inj] at h
    rw [eq_one_of_inv_eq' h.symm] at ha
    cases ha.false

@[to_additive] lemma mabs_mul_eq_mul_mabs_iff (a b : α) :
    |a * b|ₘ = |a|ₘ * |b|ₘ ↔ 1 ≤ a ∧ 1 ≤ b ∨ a ≤ 1 ∧ b ≤ 1 := by
  obtain ab | ab := le_total a b
  · exact mabs_mul_eq_mul_mabs_le ab
  · simpa only [mul_comm, and_comm] using mabs_mul_eq_mul_mabs_le ab

end LinearOrderedCommGroup

section LinearOrderedAddCommGroup

variable [LinearOrderedAddCommGroup α] {a b c : α}

@[target]
theorem abs_le : |a| ≤ b ↔ -b ≤ a ∧ a ≤ b := by sorry

theorem le_abs' : a ≤ |b| ↔ b ≤ -a ∨ a ≤ b := by rw [le_abs, or_comm, le_neg]

theorem neg_le_of_abs_le (h : |a| ≤ b) : -b ≤ a :=
  (abs_le.mp h).1

@[target]
theorem le_of_abs_le (h : |a| ≤ b) : a ≤ b :=
  sorry

@[to_additive]
theorem apply_abs_le_mul_of_one_le' {β : Type*} [MulOneClass β] [Preorder β]
    [MulLeftMono β] [MulRightMono β] {f : α → β}
    {a : α} (h₁ : 1 ≤ f a) (h₂ : 1 ≤ f (-a)) : f |a| ≤ f a * f (-a) :=
  (le_total a 0).rec (fun ha => (abs_of_nonpos ha).symm ▸ le_mul_of_one_le_left' h₁) fun ha =>
    (abs_of_nonneg ha).symm ▸ le_mul_of_one_le_right' h₂

@[target, to_additive]
theorem apply_abs_le_mul_of_one_le {β : Type*} [MulOneClass β] [Preorder β]
    [MulLeftMono β] [MulRightMono β] {f : α → β}
    (h : ∀ x, 1 ≤ f x) (a : α) : f |a| ≤ f a * f (-a) :=
  sorry
theorem abs_add (a b : α) : |a + b| ≤ |a| + |b| := by
  rw [abs_le, neg_add]
  constructor <;> gcongr <;> apply_rules [neg_abs_le, le_abs_self]

@[target]
theorem abs_add' (a b : α) : |a| ≤ |b| + |b + a| := by sorry

theorem abs_sub (a b : α) : |a - b| ≤ |a| + |b| := by
  rw [sub_eq_add_neg, ← abs_neg b]
  exact abs_add a _

@[target]
theorem abs_sub_le_iff : |a - b| ≤ c ↔ a - b ≤ c ∧ b - a ≤ c := by sorry

theorem abs_sub_lt_iff : |a - b| < c ↔ a - b < c ∧ b - a < c := by
  rw [abs_lt, neg_lt_sub_iff_lt_add', sub_lt_iff_lt_add', and_comm, sub_lt_iff_lt_add']

@[target]
theorem sub_le_of_abs_sub_le_left (h : |a - b| ≤ c) : b - c ≤ a :=
  sorry

@[target]
theorem sub_le_of_abs_sub_le_right (h : |a - b| ≤ c) : a - c ≤ b :=
  sorry

theorem sub_lt_of_abs_sub_lt_left (h : |a - b| < c) : b - c < a :=
  sub_lt_comm.1 <| (abs_sub_lt_iff.1 h).2

theorem sub_lt_of_abs_sub_lt_right (h : |a - b| < c) : a - c < b :=
  sub_lt_of_abs_sub_lt_left (abs_sub_comm a b ▸ h)

@[target]
theorem abs_sub_abs_le_abs_sub (a b : α) : |a| - |b| ≤ |a - b| :=
  sorry

@[target]
theorem abs_abs_sub_abs_le_abs_sub (a b : α) : |(|a| - |b|)| ≤ |a - b| :=
  sorry
@[target]
theorem abs_sub_le_of_nonneg_of_le {a b n : α} (a_nonneg : 0 ≤ a) (a_le_n : a ≤ n)
    (b_nonneg : 0 ≤ b) (b_le_n : b ≤ n) : |a - b| ≤ n := by sorry
@[target]
theorem abs_sub_lt_of_nonneg_of_lt {a b n : α} (a_nonneg : 0 ≤ a) (a_lt_n : a < n)
    (b_nonneg : 0 ≤ b) (b_lt_n : b < n) : |a - b| < n := by sorry

theorem abs_eq (hb : 0 ≤ b) : |a| = b ↔ a = b ∨ a = -b := by
  refine ⟨eq_or_eq_neg_of_abs_eq, ?_⟩
  rintro (rfl | rfl) <;> simp only [abs_neg, abs_of_nonneg hb]

@[target]
theorem abs_le_max_abs_abs (hab : a ≤ b) (hbc : b ≤ c) : |b| ≤ max |a| |c| :=
  sorry

@[target]
theorem min_abs_abs_le_abs_max : min |a| |b| ≤ |max a b| :=
  sorry

theorem min_abs_abs_le_abs_min : min |a| |b| ≤ |min a b| :=
  (le_total a b).elim (fun h => (min_le_left _ _).trans_eq <| congr_arg _ (min_eq_left h).symm)
    fun h => (min_le_right _ _).trans_eq <| congr_arg _ (min_eq_right h).symm

@[target]
theorem abs_max_le_max_abs_abs : |max a b| ≤ max |a| |b| :=
  sorry

theorem abs_min_le_max_abs_abs : |min a b| ≤ max |a| |b| :=
  (le_total a b).elim (fun h => (congr_arg _ <| min_eq_left h).trans_le <| le_max_left _ _) fun h =>
    (congr_arg _ <| min_eq_right h).trans_le <| le_max_right _ _

@[target]
theorem eq_of_abs_sub_eq_zero {a b : α} (h : |a - b| = 0) : a = b :=
  sorry

theorem abs_sub_le (a b c : α) : |a - c| ≤ |a - b| + |b - c| :=
  calc
    |a - c| = |a - b + (b - c)| := by rw [sub_add_sub_cancel]
    _ ≤ |a - b| + |b - c| := abs_add _ _

theorem abs_add_three (a b c : α) : |a + b + c| ≤ |a| + |b| + |c| :=
  (abs_add _ _).trans (add_le_add_right (abs_add _ _) _)

@[target]
theorem dist_bdd_within_interval {a b lb ub : α} (hal : lb ≤ a) (hau : a ≤ ub) (hbl : lb ≤ b)
    (hbu : b ≤ ub) : |a - b| ≤ ub - lb :=
  sorry

theorem eq_of_abs_sub_nonpos (h : |a - b| ≤ 0) : a = b :=
  eq_of_abs_sub_eq_zero (le_antisymm h (abs_nonneg (a - b)))

@[target]
lemma eq_of_abs_sub_lt_all {x y : α} (h : ∀ ε > 0, |x - y| < ε) : x = y :=
  sorry

@[target]
lemma eq_of_abs_sub_le_all [DenselyOrdered α] {x y : α} (h : ∀ ε > 0, |x - y| ≤ ε) : x = y :=
  sorry

@[target]
theorem abs_sub_nonpos : |a - b| ≤ 0 ↔ a = b :=
  sorry

@[target]
theorem abs_sub_pos : 0 < |a - b| ↔ a ≠ b :=
  sorry

@[simp]
theorem abs_eq_self : |a| = a ↔ 0 ≤ a := by
  rw [abs_eq_max_neg, max_eq_left_iff, neg_le_self_iff]

@[target, simp]
theorem abs_eq_neg_self : |a| = -a ↔ a ≤ 0 := by sorry
@[target]
theorem abs_cases (a : α) : |a| = a ∧ 0 ≤ a ∨ |a| = -a ∧ a < 0 := by sorry

@[simp]
theorem max_zero_add_max_neg_zero_eq_abs_self (a : α) : max a 0 + max (-a) 0 = |a| := by
  symm
  rcases le_total 0 a with (ha | ha) <;> simp [ha]

end LinearOrderedAddCommGroup
