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

@[target]
theorem not_neZero {n : R} : ¬NeZero n ↔ n = 0 := by sorry

theorem eq_zero_or_neZero (a : R) : a = 0 ∨ NeZero a :=
  (eq_or_ne a 0).imp_right NeZero.mk

section
variable {α : Type*} [Zero α]

@[simp] lemma zero_ne_one [One α] [NeZero (1 : α)] : (0 : α) ≠ 1 := NeZero.ne' (1 : α)

@[simp] lemma one_ne_zero [One α] [NeZero (1 : α)] : (1 : α) ≠ 0 := NeZero.ne (1 : α)

@[target]
lemma ne_zero_of_eq_one [One α] [NeZero (1 : α)] {a : α} (h : a = 1) : a ≠ 0 := sorry

@[field_simps]
lemma two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) ≠ 0 := NeZero.ne (2 : α)

@[field_simps]
lemma three_ne_zero [OfNat α 3] [NeZero (3 : α)] : (3 : α) ≠ 0 := NeZero.ne (3 : α)

@[field_simps]
lemma four_ne_zero [OfNat α 4] [NeZero (4 : α)] : (4 : α) ≠ 0 := NeZero.ne (4 : α)

variable (α)

lemma zero_ne_one' [One α] [NeZero (1 : α)] : (0 : α) ≠ 1 := zero_ne_one

@[target]
lemma one_ne_zero' [One α] [NeZero (1 : α)] : (1 : α) ≠ 0 := sorry

lemma two_ne_zero' [OfNat α 2] [NeZero (2 : α)] : (2 : α) ≠ 0 := two_ne_zero

@[target]
lemma three_ne_zero' [OfNat α 3] [NeZero (3 : α)] : (3 : α) ≠ 0 := sorry

@[target]
lemma four_ne_zero' [OfNat α 4] [NeZero (4 : α)] : (4 : α) ≠ 0 := sorry

namespace NeZero

variable {M : Type*} {x : M}

@[target]
theorem of_pos [Preorder M] [Zero M] (h : 0 < x) : NeZero x := sorry

end NeZero
