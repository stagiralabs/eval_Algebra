import VerifiedAgora.tagger
/-
Copyright (c) 2021 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import Mathlib.Logic.Basic
import Mathlib.Data.One.Defs
import Mathlib.Order.Defs.PartialOrder

/-!
# `NeZero` typeclass

We give basic facts about the `NeZero n` typeclass.

-/

variable {R : Type*} [Zero R]

@[target] theorem not_neZero {n : R} : ¬NeZero n ↔ n = 0 := by sorry


@[target] theorem eq_zero_or_neZero (a : R) : a = 0 ∨ NeZero a := by sorry


section
variable {α : Type*} [Zero α]

@[target] lemma zero_ne_one [One α] [NeZero (1 : α)] : (0 : α) ≠ 1 := by sorry


@[target] lemma one_ne_zero [One α] [NeZero (1 : α)] : (1 : α) ≠ 0 := by sorry


@[target] lemma ne_zero_of_eq_one [One α] [NeZero (1 : α)] {a : α} (h : a = 1) : a ≠ 0 := by sorry


/-- We have `2 ≠ 0` in a nontrivial ring whose characteristic is not `2`. -/
protected lemma Ring.two_ne_zero {R : Type*} [NonAssocSemiring R] [Nontrivial R]
    (hR : ringChar R ≠ 2) : (2 : R) ≠ 0 := by
  sorry


@[target] lemma three_ne_zero [OfNat α 3] [NeZero (3 : α)] : (3 : α) ≠ 0 := by sorry


@[target] lemma four_ne_zero [OfNat α 4] [NeZero (4 : α)] : (4 : α) ≠ 0 := by sorry


variable (α)

lemma zero_ne_one' [One α] [NeZero (1 : α)] : (0 : α) ≠ 1 := zero_ne_one

lemma one_ne_zero' [One α] [NeZero (1 : α)] : (1 : α) ≠ 0 := one_ne_zero

lemma two_ne_zero' [OfNat α 2] [NeZero (2 : α)] : (2 : α) ≠ 0 := two_ne_zero

lemma three_ne_zero' [OfNat α 3] [NeZero (3 : α)] : (3 : α) ≠ 0 := three_ne_zero

lemma four_ne_zero' [OfNat α 4] [NeZero (4 : α)] : (4 : α) ≠ 0 := four_ne_zero

end

namespace NeZero

variable {M : Type*} {x : M}

theorem of_pos [Preorder M] [Zero M] (h : 0 < x) : NeZero x := ⟨ne_of_gt h⟩

end NeZero
