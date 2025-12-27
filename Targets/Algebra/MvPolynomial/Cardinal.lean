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

@[target, simp]
theorem cardinalMk_eq_max_lift [Nonempty σ] [Nontrivial R] :
    #(MvPolynomial σ R) = max (max (Cardinal.lift.{u} #R) <| Cardinal.lift.{v} #σ) ℵ₀ :=
  sorry

@[deprecated (since := "2024-11-10")] alias cardinal_mk_eq_max_lift := cardinalMk_eq_max_lift

@[target, simp]
theorem cardinalMk_eq_lift [IsEmpty σ] : #(MvPolynomial σ R) = Cardinal.lift.{u} #R :=
  sorry

@[deprecated (since := "2024-11-10")] alias cardinal_mk_eq_lift := cardinalMk_eq_lift

@[target, nontriviality]
theorem cardinalMk_eq_one [Subsingleton R] : #(MvPolynomial σ R) = 1 := sorry

@[target]
theorem cardinalMk_le_max_lift {σ : Type u} {R : Type v} [CommSemiring R] : #(MvPolynomial σ R) ≤
    max (max (Cardinal.lift.{u} #R) <| Cardinal.lift.{v} #σ) ℵ₀ := by sorry

@[deprecated (since := "2024-11-21")] alias cardinal_lift_mk_le_max := cardinalMk_le_max_lift

end TwoUniverses

variable {σ R : Type u} [CommSemiring R]

@[target]
theorem cardinalMk_eq_max [Nonempty σ] [Nontrivial R] :
    #(MvPolynomial σ R) = max (max #R #σ) ℵ₀ := by sorry

@[deprecated (since := "2024-11-10")] alias cardinal_mk_eq_max := cardinalMk_eq_max

theorem cardinalMk_eq [IsEmpty σ] : #(MvPolynomial σ R) = #R := by simp

/-- The cardinality of the multivariate polynomial ring, `MvPolynomial σ R` is at most the maximum
of `#R`, `#σ` and `ℵ₀` -/
theorem cardinalMk_le_max : #(MvPolynomial σ R) ≤ max (max #R #σ) ℵ₀ :=
  cardinalMk_le_max_lift.trans <| by rw [lift_id, lift_id]

@[deprecated (since := "2024-11-10")] alias cardinal_mk_le_max := cardinalMk_le_max

end MvPolynomial
