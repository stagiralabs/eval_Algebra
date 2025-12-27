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

@[simp, norm_cast] lemma coe_sum (s : Finset ι) (f : ι → α) :
    ∑ i ∈ s, f i = ∑ i ∈ s, (f i : WithTop α) := map_sum addHom f s

/-- A sum is infinite iff one term is infinite. -/
@[simp] lemma sum_eq_top : ∑ i ∈ s, f i = ⊤ ↔ ∃ i ∈ s, f i = ⊤ := by
  induction s using Finset.cons_induction <;> simp [*]

/-- A sum is finite iff all terms are finite. -/
lemma sum_ne_top : ∑ i ∈ s, f i ≠ ⊤ ↔ ∀ i ∈ s, f i ≠ ⊤ := by simp

variable [LT α]

/-- A sum is finite iff all terms are finite. -/
@[simp] lemma sum_lt_top : ∑ i ∈ s, f i < ⊤ ↔ ∀ i ∈ s, f i < ⊤ := by
  simp [WithTop.lt_top_iff_ne_top]

@[deprecated (since := "2024-08-25")] alias sum_eq_top_iff := sum_eq_top
@[deprecated (since := "2024-08-25")] alias sum_lt_top_iff := sum_lt_top

end AddCommMonoid

section CommMonoidWithZero
variable [CommMonoidWithZero α] [NoZeroDivisors α] [Nontrivial α] [DecidableEq α]
  {s : Finset ι} {f : ι → WithTop α}

/-- A product of finite terms is finite. -/
@[target]
lemma prod_ne_top (h : ∀ i ∈ s, f i ≠ ⊤) : ∏ i ∈ s, f i ≠ ⊤ :=
  sorry
@[target]
lemma prod_lt_top [LT α] (h : ∀ i ∈ s, f i < ⊤) : ∏ i ∈ s, f i < ⊤ :=
  sorry

end CommMonoidWithZero
end WithTop

namespace WithBot
section AddCommMonoid
variable [AddCommMonoid α] {s : Finset ι} {f : ι → WithBot α}

@[simp, norm_cast] lemma coe_sum (s : Finset ι) (f : ι → α) :
    ∑ i ∈ s, f i = ∑ i ∈ s, (f i : WithBot α) := map_sum addHom f s

/-- A sum is infinite iff one term is infinite. -/
lemma sum_eq_bot_iff : ∑ i ∈ s, f i = ⊥ ↔ ∃ i ∈ s, f i = ⊥ := by
  induction s using Finset.cons_induction <;> simp [*]

variable [LT α]

/-- A sum is finite iff all terms are finite. -/
@[target]
lemma bot_lt_sum_iff : ⊥ < ∑ i ∈ s, f i ↔ ∀ i ∈ s, ⊥ < f i := by sorry
@[target]
lemma sum_lt_bot (h : ∀ i ∈ s, f i ≠ ⊥) : ⊥ < ∑ i ∈ s, f i :=
  sorry

end AddCommMonoid

section CommMonoidWithZero
variable [CommMonoidWithZero α] [NoZeroDivisors α] [Nontrivial α] [DecidableEq α]
  {s : Finset ι} {f : ι → WithBot α}

/-- A product of finite terms is finite. -/
@[target]
lemma prod_ne_bot (h : ∀ i ∈ s, f i ≠ ⊥) : ∏ i ∈ s, f i ≠ ⊥ :=
  sorry
@[target]
lemma bot_lt_prod [LT α] (h : ∀ i ∈ s, ⊥ < f i) : ⊥ < ∏ i ∈ s, f i :=
  sorry

end CommMonoidWithZero

/-- A product of finite terms is finite. -/
@[deprecated bot_lt_prod (since := "2024-08-25")]
lemma prod_lt_bot [CommMonoidWithZero α] [NoZeroDivisors α] [Nontrivial α] [DecidableEq α] [LT α]
    {s : Finset ι} {f : ι → WithBot α} (h : ∀ i ∈ s, f i ≠ ⊥) : ⊥ < ∏ i ∈ s, f i :=
  prod_induction f (⊥ < ·) (fun _ _ h₁ h₂ ↦ bot_lt_mul h₁ h₂) (bot_lt_coe 1)
    fun a ha ↦ WithBot.bot_lt_iff_ne_bot.2 (h a ha)

end WithBot
