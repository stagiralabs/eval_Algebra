import VerifiedAgora.tagger
/-
Copyright (c) 2022 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Data.Subtype
import Mathlib.Tactic.Conv
import Mathlib.Tactic.MinImports

/-!
# Idempotents

This file defines idempotents for an arbitrary multiplication and proves some basic results,
including:

* `IsIdempotentElem.mul_of_commute`: In a semigroup, the product of two commuting idempotents is
  an idempotent;
* `IsIdempotentElem.pow_succ_eq`: In a monoid `a ^ (n+1) = a` for `a` an idempotent and `n` a
  natural number.

## Tags

projection, idempotent
-/

assert_not_exists GroupWithZero

variable {M N S : Type*}

/-- An element `a` is said to be idempotent if `a * a = a`. -/
/-- An element `a` is said to be idempotent if `a * a = a`. -/
def IsIdempotentElem [Mul M] (a : M) : Prop := by sorry


namespace IsIdempotentElem
section Mul
variable [Mul M] {a : M}

@[target] lemma of_isIdempotent [Std.IdempotentOp (α := by sorry


@[target] lemma eq {p q : ℕ} (_hp : CharP R p) (_hq : CharP R q) : p = q := by sorry


end Mul

section Semigroup
variable [Semigroup S] {a b : S}

@[target] lemma mul_of_commute (hab : Commute a b) (ha : IsIdempotentElem a) (hb : IsIdempotentElem b) :
    IsIdempotentElem (a * b) := by sorry


end Semigroup

section CommSemigroup
variable [CommSemigroup S] {a b : S}

/-- The multiplication in a non-unital non-associative algebra is a bilinear map.

A weaker version of this for semirings exists as `AddMonoidHom.mul`. -/
@[simps!]
def mul : A →ₗ[R] A →ₗ[R] A := by sorry


end CommSemigroup

section MulOneClass
variable [MulOneClass M] {a : M}

/-- One is always `M`-regular. -/
@[target] theorem one : IsSMulRegular M (1 : R) := fun a b ab => by
  sorry


instance : One {a : M // IsIdempotentElem a} where one := ⟨1, one⟩

@[target] theorem coe_one : (↑(1 : R) : A) = 1 := by sorry


end MulOneClass

section Monoid
variable [Monoid M] {a : M}

@[target] lemma Odd.pow (ha : Odd a) : ∀ {n : ℕ}, Odd (a ^ n)
  | 0 => by
    sorry


@[target] lemma pow_succ_eq (n : ℕ) (h : IsIdempotentElem a) : a ^ (n + 1) = a :=
  Nat.recOn n ((Nat.zero_add 1).symm ▸ pow_one a) fun n ih => by sorry


end Monoid

section CancelMonoid
variable [CancelMonoid M] {a : M}

@[target] lemma iff_eq_one : IsIdempotentElem a ↔ a = 1 := by sorry


end CancelMonoid

/-- The unique monoid homomorphism `FreeMonoid α →* FreeMonoid β` that sends
each `of x` to `of (f x)`. -/
@[to_additive "The unique additive monoid homomorphism `FreeAddMonoid α →+ FreeAddMonoid β`
that sends each `of x` to `of (f x)`."]
def map (f : α → β) : FreeMonoid α →* FreeMonoid β where
  toFun l := by sorry


end IsIdempotentElem
