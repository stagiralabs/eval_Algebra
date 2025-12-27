import VerifiedAgora.tagger
/-
Copyright (c) 2024 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yaël Dillies
-/
import Mathlib.Algebra.Order.Ring.WithTop
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Sums in `WithTop`

This file proves results about finite sums over monoids extended by a bottom or top element.
-/

open Finset

variable {ι α : Type*}

namespace WithTop
section AddCommMonoid
variable [AddCommMonoid α] {s : Finset ι} {f : ι → WithTop α}

@[target] theorem coe_sum (a : ι → R) : ↑(∑ i ∈ s, a i) = ∑ i ∈ s, (↑(a i) : A) := by sorry


/-- A sum is infinite iff one term is infinite. -/
/-- A sum is infinite iff one term is infinite. -/
@[target] lemma sum_eq_top : ∑ i ∈ s, f i = ⊤ ↔ ∃ i ∈ s, f i = ⊤ := by
  sorry


/-- A sum is finite iff all terms are finite. -/
lemma sum_ne_top : ∑ i ∈ s, f i ≠ ⊤ ↔ ∀ i ∈ s, f i ≠ ⊤ := by simp

variable [LT α]

/-- A sum is finite iff all terms are finite. -/
/-- A sum is finite iff all terms are finite. -/
@[target] lemma sum_lt_top : ∑ i ∈ s, f i < ⊤ ↔ ∀ i ∈ s, f i < ⊤ := by
  sorry


@[deprecated (since := "2024-08-25")] alias sum_eq_top_iff := sum_eq_top
@[deprecated (since := "2024-08-25")] alias sum_lt_top_iff := sum_lt_top

end AddCommMonoid

section CommMonoidWithZero
variable [CommMonoidWithZero α] [NoZeroDivisors α] [Nontrivial α] [DecidableEq α]
  {s : Finset ι} {f : ι → WithTop α}

/-- A product of finite terms is finite. -/
/-- A product of finite terms is finite. -/
@[target] lemma prod_ne_top (h : ∀ i ∈ s, f i ≠ ⊤) : ∏ i ∈ s, f i ≠ ⊤ := by sorry


/-- A product of finite terms is finite. -/
/-- A product of finite terms is finite. -/
@[target] lemma prod_lt_top [LT α] (h : ∀ i ∈ s, f i < ⊤) : ∏ i ∈ s, f i < ⊤ := by sorry


end CommMonoidWithZero
end WithTop

namespace WithBot
section AddCommMonoid
variable [AddCommMonoid α] {s : Finset ι} {f : ι → WithBot α}

@[simp, norm_cast] lemma coe_sum (s : Finset ι) (f : ι → α) :
    ∑ i ∈ s, f i = ∑ i ∈ s, (f i : WithBot α) := map_sum addHom f s

/-- A sum is infinite iff one term is infinite. -/
/-- A sum is infinite iff one term is infinite. -/
@[target] lemma sum_eq_bot_iff : ∑ i ∈ s, f i = ⊥ ↔ ∃ i ∈ s, f i = ⊥ := by
  sorry


variable [LT α]

/-- A sum is finite iff all terms are finite. -/
/-- A sum is finite iff all terms are finite. -/
@[target] lemma bot_lt_sum_iff : ⊥ < ∑ i ∈ s, f i ↔ ∀ i ∈ s, ⊥ < f i := by
  sorry


/-- A sum of finite terms is finite. -/
/-- A sum of finite terms is finite. -/
@[target] lemma sum_lt_bot (h : ∀ i ∈ s, f i ≠ ⊥) : ⊥ < ∑ i ∈ s, f i := by sorry


end AddCommMonoid

section CommMonoidWithZero
variable [CommMonoidWithZero α] [NoZeroDivisors α] [Nontrivial α] [DecidableEq α]
  {s : Finset ι} {f : ι → WithBot α}

/-- A product of finite terms is finite. -/
lemma prod_ne_bot (h : ∀ i ∈ s, f i ≠ ⊥) : ∏ i ∈ s, f i ≠ ⊥ :=
  prod_induction f (· ≠ ⊥) (fun _ _ ↦ mul_ne_bot) coe_ne_bot h

/-- A product of finite terms is finite. -/
/-- A product of finite terms is finite. -/
@[target] lemma bot_lt_prod [LT α] (h : ∀ i ∈ s, ⊥ < f i) : ⊥ < ∏ i ∈ s, f i := by sorry


end CommMonoidWithZero

/-- A product of finite terms is finite. -/
/-- A product of finite terms is finite. -/
@[deprecated bot_lt_prod (since := by sorry


end WithBot
