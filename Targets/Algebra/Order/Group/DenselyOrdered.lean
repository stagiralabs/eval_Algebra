import VerifiedAgora.tagger
/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.OrderDual
import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE

/-!
# Lemmas about densely linearly ordered groups.
-/

variable {α : Type*}

section DenselyOrdered

variable [Group α] [LinearOrder α]
variable [MulLeftMono α]
variable [DenselyOrdered α] {a b : α}

@[to_additive]
theorem le_of_forall_lt_one_mul_le (h : ∀ ε < 1, a * ε ≤ b) : a ≤ b :=
  le_of_forall_one_lt_le_mul (α := αᵒᵈ) h

@[target, to_additive]
theorem le_of_forall_one_lt_div_le (h : ∀ ε : α, 1 < ε → a / ε ≤ b) : a ≤ b :=
  sorry

@[target, to_additive]
theorem le_iff_forall_lt_one_mul_le : a ≤ b ↔ ∀ ε < 1, a * ε ≤ b :=
  sorry

end DenselyOrdered

section DenselyOrdered

@[to_additive]
private lemma exists_lt_mul_left [Group α] [LT α] [DenselyOrdered α]
    [CovariantClass α α (Function.swap (· * ·)) (· < ·)] {a b c : α} (hc : c < a * b) :
    ∃ a' < a, c < a' * b := by
  obtain ⟨a', hc', ha'⟩ := exists_between (div_lt_iff_lt_mul.2 hc)
  exact ⟨a', ha', div_lt_iff_lt_mul.1 hc'⟩

@[to_additive]
private lemma exists_lt_mul_right [CommGroup α] [LT α] [DenselyOrdered α]
    [CovariantClass α α (· * ·) (· < ·)] {a b c : α} (hc : c < a * b) :
    ∃ b' < b, c < a * b' := by
  obtain ⟨a', hc', ha'⟩ := exists_between (div_lt_iff_lt_mul'.2 hc)
  exact ⟨a', ha', div_lt_iff_lt_mul'.1 hc'⟩

@[to_additive]
private lemma exists_mul_left_lt [Group α] [LT α] [DenselyOrdered α]
    [CovariantClass α α (Function.swap (· * ·)) (· < ·)] {a b c : α} (hc : a * b < c) :
    ∃ a' > a, a' * b < c := by
  obtain ⟨a', ha', hc'⟩ := exists_between (lt_div_iff_mul_lt.2 hc)
  exact ⟨a', ha', lt_div_iff_mul_lt.1 hc'⟩

@[to_additive]
private lemma exists_mul_right_lt [CommGroup α] [LT α] [DenselyOrdered α]
    [CovariantClass α α (· * ·) (· < ·)] {a b c : α} (hc : a * b < c) :
    ∃ b' > b, a * b' < c := by
  obtain ⟨a', ha', hc'⟩ := exists_between (lt_div_iff_mul_lt'.2 hc)
  exact ⟨a', ha', lt_div_iff_mul_lt'.1 hc'⟩

@[target, to_additive]
lemma le_mul_of_forall_lt [CommGroup α] [LinearOrder α] [CovariantClass α α (· * ·) (· ≤ ·)]
    [DenselyOrdered α] {a b c : α} (h : ∀ a' > a, ∀ b' > b, c ≤ a' * b') :
    c ≤ a * b := by sorry

@[target, to_additive]
lemma mul_le_of_forall_lt [CommGroup α] [LinearOrder α] [CovariantClass α α (· * ·) (· ≤ ·)]
    [DenselyOrdered α] {a b c : α} (h : ∀ a' < a, ∀ b' < b, a' * b' ≤ c) :
    a * b ≤ c := by sorry

end DenselyOrdered
