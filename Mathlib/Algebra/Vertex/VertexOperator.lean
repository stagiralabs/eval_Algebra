import VerifiedAgora.tagger
/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.Algebra.Vertex.HVertexOperator
import Mathlib.Data.Int.Interval

/-!
# Vertex operators
In this file we introduce vertex operators as linear maps to Laurent series.

## Definitions
 * `VertexOperator` is an `R`-linear map from an `R`-module `V` to `LaurentSeries V`.
 * `VertexOperator.ncoeff` is the coefficient of a vertex operator under normalized indexing.

## TODO
 * `HasseDerivative` : A divided-power derivative.
 * `Locality` : A weak form of commutativity.
 * `Residue products` : A family of products on `VertexOperator R V` parametrized by integers.

## References
 * [G. Mason, *Vertex rings and Pierce bundles*][mason2017]
 * [A. Matsuo, K. Nagatomo, *On axioms for a vertex algebra and locality of quantum
   fields*][matsuo1997]
-/

noncomputable section

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- A vertex operator over a commutative ring `R` is an `R`-linear map from an `R`-module `V` to
Laurent series with coefficients in `V`.  We write this as a specialization of the heterogeneous
case. -/
/-- A vertex operator over a commutative ring `R` is an `R`-linear map from an `R`-module `V` to
Laurent series with coefficients in `V`.  We write this as a specialization of the heterogeneous
case. -/
abbrev VertexOperator (R : Type*) (V : Type*) [CommRing R] [AddCommGroup V]
    [Module R V] := by sorry


namespace VertexOperator

open HVertexOperator

@[target] theorem Algebra.ext {S : Type u} {A : Type v} [CommSemiring S] [Semiring A] (h1 h2 : Algebra S A)
    (h : ∀ (r : S) (x : A), (by sorry


/-- The coefficient of a vertex operator under normalized indexing. -/
/-- The coefficient of a vertex operator under normalized indexing. -/
def ncoeff {R} [CommRing R] [AddCommGroup V] [Module R V] (A : VertexOperator R V) (n : ℤ) :
    Module.End R V := by sorry


/-- In the literature, the `n`th normalized coefficient of a vertex operator `A` is written as
either `Aₙ` or `A(n)`. -/
scoped[VertexOperator] notation A "[[" n "]]" => ncoeff A n

@[target] theorem coeff_eq_ncoeff (A : VertexOperator R V)
    (n : ℤ) : HVertexOperator.coeff A n = A [[-n - 1]] := by
  sorry


@[target] theorem ncoeff_add (A B : VertexOperator R V) (n : ℤ) : (A + B) [[n]] = A [[n]] + B [[n]] := by
  sorry


@[target] theorem ncoeff_smul (A : VertexOperator R V) (r : R) (n : ℤ) : (r • A) [[n]] = r • A [[n]] := by
  sorry


@[target] theorem ncoeff_eq_zero_of_lt_order (A : VertexOperator R V) (n : ℤ) (x : V)
    (h : -n - 1 < HahnSeries.order ((HahnModule.of R).symm (A x))) : (A [[n]]) x = 0 := by
  sorry


theorem coeff_eq_zero_of_lt_order (A : VertexOperator R V) (n : ℤ) (x : V)
    (h : n < HahnSeries.order ((HahnModule.of R).symm (A x))) : coeff A n x = 0 := by
  rw [coeff_eq_ncoeff, ncoeff_eq_zero_of_lt_order A (-n - 1) x]
  omega

/-- Given an endomorphism-valued function on integers satisfying a pointwise bounded-pole condition,
we produce a vertex operator. -/
noncomputable def of_coeff (f : ℤ → Module.End R V)
    (hf : ∀ (x : V), ∃ (n : ℤ), ∀ (m : ℤ), m < n → (f m) x = 0) : VertexOperator R V :=
  HVertexOperator.of_coeff f
    (fun x => HahnSeries.suppBddBelow_supp_PWO (fun n => (f n) x)
      (HahnSeries.forallLTEqZero_supp_BddBelow (fun n => (f n) x)
        (Exists.choose (hf x)) (Exists.choose_spec (hf x))))

@[target] theorem of_coeff_apply_coeff (f : ℤ → Module.End R V)
    (hf : ∀ (x : V), ∃ n, ∀ m < n, (f m) x = 0) (x : V) (n : ℤ) :
    ((HahnModule.of R).symm ((of_coeff f hf) x)).coeff n = (f n) x := by
  sorry


@[target] theorem ncoeff_of_coeff (f : ℤ → Module.End R V)
    (hf : ∀(x : V), ∃(n : ℤ), ∀(m : ℤ), m < n → (f m) x = 0) (n : ℤ) :
    (of_coeff f hf) [[n]] = f (-n - 1) := by
  sorry


end VertexOperator
