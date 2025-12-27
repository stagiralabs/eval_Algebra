import VerifiedAgora.tagger
/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Characteristic and cardinality

We prove some results relating characteristic and cardinality of finite rings

## Tags
characteristic, cardinality, ring
-/


/-- A prime `p` is a unit in a commutative ring `R` of nonzero characteristic iff it does not divide
the characteristic. -/
/-- A prime `p` is a unit in a commutative ring `R` of nonzero characteristic iff it does not divide
the characteristic. -/
@[target] theorem isUnit_iff_not_dvd_char_of_ringChar_ne_zero (R : Type*) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : ringChar R ≠ 0) : IsUnit (p : R) ↔ ¬p ∣ ringChar R := by
  sorry


/-- A prime `p` is a unit in a finite commutative ring `R`
iff it does not divide the characteristic. -/
/-- A prime `p` is a unit in a finite commutative ring `R`
iff it does not divide the characteristic. -/
@[target] theorem isUnit_iff_not_dvd_char (R : Type*) [CommRing R] (p : ℕ) [Fact p.Prime] [Finite R] :
    IsUnit (p : R) ↔ ¬p ∣ ringChar R := by sorry


/-- The prime divisors of the characteristic of a finite commutative ring are exactly
the prime divisors of its cardinality. -/
/-- The prime divisors of the characteristic of a finite commutative ring are exactly
the prime divisors of its cardinality. -/
@[target] theorem prime_dvd_char_iff_dvd_card {R : Type*} [CommRing R] [Fintype R] (p : ℕ) [Fact p.Prime] :
    p ∣ ringChar R ↔ p ∣ Fintype.card R := by
  sorry


/-- A prime that divides the cardinality of a finite commutative ring `R`
isn't a unit in `R`. -/
theorem not_isUnit_prime_of_dvd_card {R : Type*} [CommRing R] [Fintype R] (p : ℕ) [Fact p.Prime]
    (hp : p ∣ Fintype.card R) : ¬IsUnit (p : R) :=
  mt (isUnit_iff_not_dvd_char R p).mp
    (Classical.not_not.mpr ((prime_dvd_char_iff_dvd_card p).mpr hp))

@[target] lemma charP_of_card_eq_prime {R : Type*} [NonAssocRing R] [Fintype R] (p : ℕ) [hp : Fact p.Prime]
    (hR : Fintype.card R = p) : CharP R p := by sorry
