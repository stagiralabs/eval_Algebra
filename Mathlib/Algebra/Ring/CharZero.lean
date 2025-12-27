import VerifiedAgora.tagger
/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Algebra.Group.Support
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Ring.Units
import Mathlib.Data.Nat.Cast.Basic

/-!
# Characteristic zero rings
-/

assert_not_exists Field

open Function Set

variable {α R S : Type*} {n : ℕ}

section AddMonoidWithOne
variable [AddMonoidWithOne R] [CharZero R]

/-- `Nat.cast` as an embedding into monoids of characteristic `0`. -/
@[simps]
def Nat.castEmbedding : ℕ ↪ R := ⟨Nat.cast, cast_injective⟩

instance CharZero.NeZero.two : NeZero (2 : R) where
  out := by rw [← Nat.cast_two, Nat.cast_ne_zero]; decide

namespace Function

lemma support_natCast (hn : n ≠ 0) : support (n : α → R) = univ :=
  support_const <| Nat.cast_ne_zero.2 hn

@[target] lemma mulSupport_natCast (hn : n ≠ 1) : mulSupport (n : α → R) = univ := by sorry


end Function
end AddMonoidWithOne

section NonAssocSemiring
variable [NonAssocSemiring R] [NonAssocSemiring S]

namespace RingHom

/-- A nontrivial `ℚ`-algebra has characteristic zero.

This cannot be a (local) instance because it would immediately form a loop with the
instance `DivisionRing.toRatAlgebra`. It's probably easier to go the other way: prove `CharZero R`
and automatically receive an `Algebra ℚ R` instance.
-/
@[target] theorem algebraRat.charZero [Ring R] [Algebra ℚ R] : CharZero R := by sorry


@[target] lemma charZero_iff {ϕ : R →+* S} (hϕ : Injective ϕ) : CharZero R ↔ CharZero S :=
  ⟨fun hR =>
    ⟨by sorry


@[target] lemma injective_nat (f : ℕ →+* R) [CharZero R] : Injective f := by sorry


end RingHom

variable [NoZeroDivisors R] [CharZero R] {a : R}

@[target] theorem add_self_eq_zero (x : R) : x + x = 0 := by sorry


end NonAssocSemiring

section Semiring
variable [Semiring R] [CharZero R]

@[simp] lemma Nat.cast_pow_eq_one {a : ℕ} (hn : n ≠ 0) : (a : R) ^ n = 1 ↔ a = 1 := by
  simp [← cast_pow, cast_eq_one, hn]

end Semiring

section NonAssocRing
variable [NonAssocRing R] [NoZeroDivisors R] [CharZero R]

@[scoped simp] theorem CharZero.neg_eq_self_iff {a : R} : -a = a ↔ a = 0 :=
  neg_eq_iff_add_eq_zero.trans add_self_eq_zero

@[scoped simp] theorem CharZero.eq_neg_self_iff {a : R} : a = -a ↔ a = 0 :=
  eq_neg_iff_add_eq_zero.trans add_self_eq_zero

@[target] theorem nat_mul_inj {n : ℕ} {a b : R} (h : (n : R) * a = (n : R) * b) : n = 0 ∨ a = b := by
  sorry


theorem nat_mul_inj' {n : ℕ} {a b : R} (h : (n : R) * a = (n : R) * b) (w : n ≠ 0) : a = b := by
  simpa [w] using nat_mul_inj h

end NonAssocRing

section Ring
variable [Ring R] [CharZero R]

@[target] theorem units_ne_neg_self (u : Rˣ) : u ≠ -u := by
  sorry


@[simp]
theorem neg_units_ne_self (u : Rˣ) : -u ≠ u := (units_ne_neg_self u).symm

end Ring
