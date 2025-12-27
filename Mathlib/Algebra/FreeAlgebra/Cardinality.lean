import VerifiedAgora.tagger
/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.Algebra.FreeAlgebra
import Mathlib.SetTheory.Cardinal.Free

/-!
# Cardinality of free algebras

This file contains some results about the cardinality of `FreeAlgebra`,
parallel to that of `MvPolynomial`.
-/

universe u v

variable (R : Type u) [CommSemiring R]

open Cardinal

namespace FreeAlgebra

variable (X : Type v)

@[target] theorem cardinalMk_eq_max_lift [Nonempty σ] [Nontrivial R] :
    #(MvPolynomial σ R) = max (max (Cardinal.lift.{u} #R) <| Cardinal.lift.{v} #σ) ℵ₀ :=
  (mk_finsupp_lift_of_infinite _ R).trans <| by
    sorry


@[target] theorem cardinalMk_eq_lift [IsEmpty σ] : #(MvPolynomial σ R) = Cardinal.lift.{u} #R := by sorry


@[target] theorem cardinalMk_eq_one [Subsingleton R] : #(MvPolynomial σ R) = 1 := by sorry


@[target] theorem cardinalMk_le_max_lift {σ : Type u} {R : Type v} [CommSemiring R] : #(MvPolynomial σ R) ≤
    max (max (Cardinal.lift.{u} #R) <| Cardinal.lift.{v} #σ) ℵ₀ := by
  sorry


variable (X : Type u)

@[target] theorem cardinalMk_eq_max [Nonempty σ] [Nontrivial R] :
    #(MvPolynomial σ R) = max (max #R #σ) ℵ₀ := by sorry


theorem cardinalMk_eq [IsEmpty X] : #(FreeAlgebra R X) = #R := by
  simp

/-- The cardinality of the multivariate polynomial ring, `MvPolynomial σ R` is at most the maximum
of `#R`, `#σ` and `ℵ₀` -/
@[target] theorem cardinalMk_le_max : #(MvPolynomial σ R) ≤ max (max #R #σ) ℵ₀ :=
  cardinalMk_le_max_lift.trans <| by sorry


end FreeAlgebra

namespace Algebra

@[target] theorem lift_cardinalMk_adjoin_le {A : Type v} [Semiring A] [Algebra R A] (s : Set A) :
    lift.{u} #(adjoin R s) ≤ lift.{v} #R ⊔ lift.{u} #s ⊔ ℵ₀ := by
  sorry


@[target] theorem cardinalMk_adjoin_le {A : Type u} [Semiring A] [Algebra R A] (s : Set A) :
    #(adjoin R s) ≤ #R ⊔ #s ⊔ ℵ₀ := by
  sorry


end Algebra
