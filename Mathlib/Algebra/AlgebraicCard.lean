import VerifiedAgora.tagger
/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Algebra.Polynomial.Cardinal
import Mathlib.RingTheory.Algebraic.Basic

/-!
### Cardinality of algebraic numbers

In this file, we prove variants of the following result: the cardinality of algebraic numbers under
an R-algebra is at most `#R[X] * ℵ₀`.

Although this can be used to prove that real or complex transcendental numbers exist, a more direct
proof is given by `Liouville.transcendental`.
-/


universe u v

open Cardinal Polynomial Set

open Cardinal Polynomial

namespace Algebraic

@[target] theorem infinite_of_charZero (R A : Type*) [CommRing R] [IsDomain R] [Ring A] [Algebra R A]
    [CharZero A] : { x : A | IsAlgebraic R x }.Infinite := by sorry


@[target] theorem aleph0_le_cardinalMk_of_charZero (R A : Type*) [CommRing R] [IsDomain R] [Ring A]
    [Algebra R A] [CharZero A] : ℵ₀ ≤ #{ x : A // IsAlgebraic R x } := by sorry


@[deprecated (since := "2024-11-10")]
alias aleph0_le_cardinal_mk_of_charZero := aleph0_le_cardinalMk_of_charZero

section lift

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [IsDomain A] [Algebra R A]
  [NoZeroSMulDivisors R A]

@[target] theorem cardinalMk_lift_le_mul :
    Cardinal.lift.{u} #{ x : A // IsAlgebraic R x } ≤ Cardinal.lift.{v} #R[X] * ℵ₀ := by
  sorry


@[deprecated (since := "2024-11-10")] alias cardinal_mk_lift_le_mul := cardinalMk_lift_le_mul

theorem cardinalMk_lift_le_max :
    Cardinal.lift.{u} #{ x : A // IsAlgebraic R x } ≤ max (Cardinal.lift.{v} #R) ℵ₀ :=
  (cardinalMk_lift_le_mul R A).trans <|
    (mul_le_mul_right' (lift_le.2 cardinalMk_le_max) _).trans <| by simp

@[deprecated (since := "2024-11-10")] alias cardinal_mk_lift_le_max := cardinalMk_lift_le_max

@[simp]
theorem cardinalMk_lift_of_infinite [Infinite R] :
    Cardinal.lift.{u} #{ x : A // IsAlgebraic R x } = Cardinal.lift.{v} #R :=
  ((cardinalMk_lift_le_max R A).trans_eq (max_eq_left <| aleph0_le_mk _)).antisymm <|
    lift_mk_le'.2 ⟨⟨fun x => ⟨algebraMap R A x, isAlgebraic_algebraMap _⟩, fun _ _ h =>
      FaithfulSMul.algebraMap_injective R A (Subtype.ext_iff.1 h)⟩⟩

@[deprecated (since := "2024-11-10")]
alias cardinal_mk_lift_of_infinite := cardinalMk_lift_of_infinite

variable [Countable R]

@[simp]
protected theorem countable : Set.Countable { x : A | IsAlgebraic R x } := by
  rw [← le_aleph0_iff_set_countable, ← lift_le_aleph0]
  apply (cardinalMk_lift_le_max R A).trans
  simp

@[target] theorem cardinalMk_of_countable_of_charZero [CharZero A] [IsDomain R] :
    #{ x : A // IsAlgebraic R x } = ℵ₀ := by sorry


@[deprecated (since := "2024-11-10")]
alias cardinal_mk_of_countable_of_charZero := cardinalMk_of_countable_of_charZero

end lift

section NonLift

variable (R A : Type u) [CommRing R] [CommRing A] [IsDomain A] [Algebra R A]
  [NoZeroSMulDivisors R A]

@[target] theorem cardinalMk_le_mul : #{ x : A // IsAlgebraic R x } ≤ #R[X] * ℵ₀ := by
  sorry


@[deprecated (since := "2024-11-10")] alias cardinal_mk_le_mul := cardinalMk_le_mul

@[stacks 09GK]
theorem cardinalMk_le_max : #{ x : A // IsAlgebraic R x } ≤ max #R ℵ₀ := by
  rw [← lift_id #_, ← lift_id #R]
  exact cardinalMk_lift_le_max R A

@[deprecated (since := "2024-11-10")] alias cardinal_mk_le_max := cardinalMk_le_max

@[target] theorem cardinalMk_of_infinite [Infinite R] : #{ x : A // IsAlgebraic R x } = #R := by sorry


@[deprecated (since := "2024-11-10")] alias cardinal_mk_of_infinite := cardinalMk_of_infinite

end NonLift

end Algebraic
