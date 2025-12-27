import VerifiedAgora.tagger
/-
Copyright (c) 2021 Chris Hughes, Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Junyan Xu
-/
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Data.Finsupp.Fintype
import Mathlib.SetTheory.Cardinal.Finsupp

/-!
# Cardinality of Multivariate Polynomial Ring

The main result in this file is `MvPolynomial.cardinalMk_le_max`, which says that
the cardinality of `MvPolynomial σ R` is bounded above by the maximum of `#R`, `#σ`
and `ℵ₀`.
-/


universe u v

open Cardinal

namespace MvPolynomial

section TwoUniverses

variable {σ : Type u} {R : Type v} [CommSemiring R]

@[target] theorem cardinalMk_eq_max_lift [Nonempty σ] [Nontrivial R] :
    #(MvPolynomial σ R) = max (max (Cardinal.lift.{u} #R) <| Cardinal.lift.{v} #σ) ℵ₀ :=
  (mk_finsupp_lift_of_infinite _ R).trans <| by
    sorry


@[deprecated (since := "2024-11-10")] alias cardinal_mk_eq_max_lift := cardinalMk_eq_max_lift

@[target] theorem cardinalMk_eq_lift [IsEmpty σ] : #(MvPolynomial σ R) = Cardinal.lift.{u} #R := by sorry


@[deprecated (since := "2024-11-10")] alias cardinal_mk_eq_lift := cardinalMk_eq_lift

@[target] theorem cardinalMk_eq_one [Subsingleton R] : #(MvPolynomial σ R) = 1 := by sorry


theorem cardinalMk_le_max_lift {σ : Type u} {R : Type v} [CommSemiring R] : #(MvPolynomial σ R) ≤
    max (max (Cardinal.lift.{u} #R) <| Cardinal.lift.{v} #σ) ℵ₀ := by
  cases subsingleton_or_nontrivial R
  · exact (mk_eq_one _).trans_le (le_max_of_le_right one_le_aleph0)
  cases isEmpty_or_nonempty σ
  · exact cardinalMk_eq_lift.trans_le (le_max_of_le_left <| le_max_left _ _)
  · exact cardinalMk_eq_max_lift.le

@[deprecated (since := "2024-11-21")] alias cardinal_lift_mk_le_max := cardinalMk_le_max_lift

end TwoUniverses

variable {σ R : Type u} [CommSemiring R]

@[target] theorem cardinalMk_eq_max [Nonempty σ] [Nontrivial R] :
    #(MvPolynomial σ R) = max (max #R #σ) ℵ₀ := by sorry


@[deprecated (since := "2024-11-10")] alias cardinal_mk_eq_max := cardinalMk_eq_max

@[target] theorem cardinalMk_eq [IsEmpty σ] : #(MvPolynomial σ R) = #R := by sorry


/-- The cardinality of the multivariate polynomial ring, `MvPolynomial σ R` is at most the maximum
of `#R`, `#σ` and `ℵ₀` -/
/-- The cardinality of the multivariate polynomial ring, `MvPolynomial σ R` is at most the maximum
of `#R`, `#σ` and `ℵ₀` -/
@[target] theorem cardinalMk_le_max : #(MvPolynomial σ R) ≤ max (max #R #σ) ℵ₀ :=
  cardinalMk_le_max_lift.trans <| by sorry


@[deprecated (since := "2024-11-10")] alias cardinal_mk_le_max := cardinalMk_le_max

end MvPolynomial
