import VerifiedAgora.tagger
/-
Copyright (c) 2022 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathlib.Algebra.GroupWithZero.Idempotent
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Notation
import Mathlib.Tactic.Convert

/-!
# Idempotent elements of a ring

This file proves result about idempotent elements of a ring, like:
* `IsIdempotentElem.one_sub_iff`: In a (non-associative) ring, `a` is an idempotent if and only if
  `1 - a` is an idempotent.
-/

variable {R : Type*}

namespace IsIdempotentElem
section NonAssocRing
variable [NonAssocRing R] {a : R}

@[target] lemma one_sub (h : IsIdempotentElem a) : IsIdempotentElem (1 - a) := by
  sorry


@[target] lemma one_sub_iff : IsIdempotentElem (1 - a) ↔ IsIdempotentElem a := by sorry


@[target] lemma mul_one_sub_self (h : IsIdempotentElem a) : a * (1 - a) = 0 := by
  sorry


@[simp]
lemma one_sub_mul_self (h : IsIdempotentElem a) : (1 - a) * a = 0 := by
  rw [sub_mul, one_mul, h.eq, sub_self]

instance : HasCompl {a : R // IsIdempotentElem a} where compl a := ⟨1 - a, a.prop.one_sub⟩

@[target] lemma coe_compl (a : {a : R // IsIdempotentElem a}) : ↑aᶜ = (1 : R) - ↑a := by sorry


@[simp] lemma compl_compl (a : {a : R // IsIdempotentElem a}) : aᶜᶜ = a := by ext; simp
@[target] lemma zero_compl : (0 : {a : R // IsIdempotentElem a})ᶜ = 1 := by sorry

@[target] lemma one_compl : (1 : {a : R // IsIdempotentElem a})ᶜ = 0 := by sorry


end NonAssocRing

section Semiring
variable [Semiring R] {a b : R}

@[target] lemma of_mul_add (mul : a * b = 0) (add : a + b = 1) : IsIdempotentElem a ∧ IsIdempotentElem b := by
  sorry


end Semiring

section Ring
variable [Ring R] {a b : R}

lemma add_sub_mul_of_commute (h : Commute a b) (hp : IsIdempotentElem a) (hq : IsIdempotentElem b) :
    IsIdempotentElem (a + b - a * b) := by
  convert (hp.one_sub.mul_of_commute ?_ hq.one_sub).one_sub using 1
  · simp_rw [sub_mul, mul_sub, one_mul, mul_one, sub_sub, sub_sub_cancel, add_sub, add_comm]
  · simp_rw [commute_iff_eq, sub_mul, mul_sub, one_mul, mul_one, sub_sub, add_sub, add_comm, h.eq]

end Ring

section CommRing
variable [CommRing R] {a b : R}

@[target] lemma add_sub_mul (hp : IsIdempotentElem a) (hq : IsIdempotentElem b) :
    IsIdempotentElem (a + b - a * b) := by sorry


end CommRing
end IsIdempotentElem
