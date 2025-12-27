import VerifiedAgora.tagger
/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.RingTheory.HahnSeries.Multiplication

/-!
# Vertex operators
In this file we introduce heterogeneous vertex operators using Hahn series.  When `R = ℂ`, `V = W`,
and `Γ = ℤ`, then this is the usual notion of "meromorphic left-moving 2D field".  The notion we use
here allows us to consider composites and scalar-multiply by multivariable Laurent series.
## Definitions
* `HVertexOperator` : An `R`-linear map from an `R`-module `V` to `HahnModule Γ W`.
* The coefficient function as an `R`-linear map.
* Composition of heterogeneous vertex operators - values are Hahn series on lex order product.
## Main results
* Ext
## TODO
* `HahnSeries Γ R`-module structure on `HVertexOperator Γ R V W`
  (needs https://github.com/leanprover-community/mathlib4/pull/19062.
  This means we can consider products of the form `(X-Y)^n A(X)B(Y)` for all integers `n`,
  where `(X-Y)^n` is expanded as `X^n(1-Y/X)^n` in `R((X))((Y))`.
* curry for tensor product inputs
* more API to make ext comparisons easier.
* formal variable API, e.g., like the `T` function for Laurent polynomials.
## References

* [R. Borcherds, *Vertex Algebras, Kac-Moody Algebras, and the Monster*][borcherds1986vertex]

-/

assert_not_exists Cardinal

noncomputable section

variable {Γ : Type*} [PartialOrder Γ] {R : Type*} {V W : Type*} [CommRing R]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- A heterogeneous `Γ`-vertex operator over a commutator ring `R` is an `R`-linear map from an
`R`-module `V` to `Γ`-Hahn series with coefficients in an `R`-module `W`. -/
/-- A heterogeneous `Γ`-vertex operator over a commutator ring `R` is an `R`-linear map from an
`R`-module `V` to `Γ`-Hahn series with coefficients in an `R`-module `W`. -/
abbrev HVertexOperator (Γ : Type*) [PartialOrder Γ] (R : Type*) [CommRing R]
    (V : Type*) (W : Type*) [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W] := by sorry


namespace HVertexOperator

section Coeff

open HahnModule

@[target] theorem Algebra.ext {S : Type u} {A : Type v} [CommSemiring S] [Semiring A] (h1 h2 : Algebra S A)
    (h : ∀ (r : S) (x : A), (by sorry


/-- The coefficient of a heterogeneous vertex operator, viewed as a formal power series with
coefficients in linear maps. -/
/-- The coefficient of a heterogeneous vertex operator, viewed as a formal power series with
coefficients in linear maps. -/
@[simps]
def coeff (A : HVertexOperator Γ R V W) (n : Γ) : V →ₗ[R] W where
  toFun v := ((of R).symm (A v)).coeff n
  map_add' _ _ := by sorry


@[target] theorem coeff_isPWOsupport (A : HVertexOperator Γ R V W) (v : V) :
    ((of R).symm (A v)).coeff.support.IsPWO := by sorry


@[target] theorem coeff_inj : Function.Injective (coeff : HVertexOperator Γ R V W → Γ → (V →ₗ[R] W)) := by
  sorry


/-- Given a coefficient function valued in linear maps satisfying a partially well-ordered support
condition, we produce a heterogeneous vertex operator. -/
/-- Given a coefficient function valued in linear maps satisfying a partially well-ordered support
condition, we produce a heterogeneous vertex operator. -/
@[simps]
def of_coeff (f : Γ → V →ₗ[R] W)
    (hf : ∀(x : V), (Function.support (f · x)).IsPWO) : HVertexOperator Γ R V W where
  toFun x := (of R) { coeff := fun g => f g x, isPWO_support' := hf x }
  map_add' _ _ := by sorry


@[simp]
theorem coeff_add (A B : HVertexOperator Γ R V W) : (A + B).coeff = A.coeff + B.coeff := by
  ext
  simp

@[deprecated (since := "2025-01-31")] alias add_coeff := coeff_add

@[simp]
theorem coeff_smul (A : HVertexOperator Γ R V W) (r : R) : (r • A).coeff = r • (A.coeff) := by
  ext
  simp

@[deprecated (since := "2025-01-31")] alias smul_coeff := coeff_smul

end Coeff

section Products

variable {Γ Γ' : Type*} [OrderedCancelAddCommMonoid Γ] [OrderedCancelAddCommMonoid Γ'] {R : Type*}
  [CommRing R] {U V W : Type*} [AddCommGroup U] [Module R U][AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W] (A : HVertexOperator Γ R V W) (B : HVertexOperator Γ' R U V)

open HahnModule

/-- The composite of two heterogeneous vertex operators acting on a vector, as an iterated Hahn
series. -/
/-- The composite of two heterogeneous vertex operators acting on a vector, as an iterated Hahn
series. -/
@[simps]
def compHahnSeries (u : U) : HahnSeries Γ' (HahnSeries Γ W) where
  coeff g' := A (coeff B g' u)
  isPWO_support' := by
    sorry


@[target] theorem compHahnSeries_add (u v : U) :
    compHahnSeries A B (u + v) = compHahnSeries A B u + compHahnSeries A B v := by
  sorry


@[simp]
theorem compHahnSeries_smul (r : R) (u : U) :
    compHahnSeries A B (r • u) = r • compHahnSeries A B u := by
  ext
  simp only [compHahnSeries_coeff, LinearMapClass.map_smul, coeff_apply, HahnSeries.coeff_smul]
  rw [← HahnSeries.coeff_smul]

/-- The composite of two heterogeneous vertex operators, as a heterogeneous vertex operator. -/
set_option linter.unusedVariables false in
/-- The composition of morphisms is a morphism. -/
def comp (f : B →ₛₙₐ[ψ] C) (g : A →ₛₙₐ[φ] B) [κ : MonoidHom.CompTriple φ ψ χ] :
    A →ₛₙₐ[χ] C := by sorry


@[target] theorem coeff_comp (g : Γ' ×ₗ Γ) :
    (comp A B).coeff g = A.coeff (ofLex g).2 ∘ₗ B.coeff (ofLex g).1 := by
  sorry


@[deprecated (since := "2025-01-31")] alias comp_coeff := coeff_comp

end Products

end HVertexOperator
