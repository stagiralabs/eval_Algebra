import VerifiedAgora.tagger
/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Richard M. Hill
-/
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Module.AEval
import Mathlib.RingTheory.Adjoin.Polynomial
import Mathlib.RingTheory.Derivation.Basic
/-!
# Derivations of univariate polynomials

In this file we prove that an `R`-derivation of `Polynomial R` is determined by its value on `X`.
We also provide a constructor `Polynomial.mkDerivation` that
builds a derivation from its value on `X`, and a linear equivalence
`Polynomial.mkDerivationEquiv` between `A` and `Derivation (Polynomial R) A`.
-/

noncomputable section

namespace Polynomial

section CommSemiring

variable {R A : Type*} [CommSemiring R]

/-- `Polynomial.derivative` as a derivation. -/
/-- `derivative p` is the formal derivative of the polynomial `p` -/
def derivative : R[X] →ₗ[R] R[X] where
  toFun p := p.sum fun n a => C (a * n) * X ^ (n - 1)
  map_add' p q := by
    sorry


variable [AddCommMonoid A] [Module R A] [Module (Polynomial R) A]

@[target] theorem derivation_C (D : Derivation R (MvPolynomial σ R) A) (a : R) : D (C a) = 0 := by sorry


@[target] theorem C_smul_derivation_apply (D : Derivation R R[X] A) (a : R) (f : R[X]) :
    C a • D f = a • D f := by
  sorry


@[target] theorem derivation_ext {D₁ D₂ : Derivation R (MvPolynomial σ R) A} (h : ∀ i, D₁ (X i) = D₂ (X i)) :
    D₁ = D₂ := by sorry


variable [IsScalarTower R (Polynomial R) A]
variable (R)

/-- The derivation on `R[X]` that takes the value `a` on `X`. -/
/-- The derivation on `MvPolynomial σ R` that takes value `f i` on `X i`. -/
def mkDerivation (f : σ → A) : Derivation R (MvPolynomial σ R) A where
  toLinearMap := mkDerivationₗ R f
  map_one_eq_zero' := mkDerivationₗ_C _ 1
  leibniz' :=
    (leibniz_iff_X (mkDerivationₗ R f) (mkDerivationₗ_C _ 1)).2 fun s i => by
      sorry


@[target] lemma mkDerivation_apply (a : A) (f : R[X]) :
    mkDerivation R a f = derivative f • a := by
  sorry


@[target] theorem mkDerivation_X (f : σ → A) (i : σ) : mkDerivation R f (X i) = f i := by sorry


@[target] lemma mkDerivation_one_eq_derivative (f : R[X]) : mkDerivation R (1 : R[X]) f = derivative f := by
  sorry


lemma mkDerivation_one_eq_derivative (f : R[X]) : mkDerivation R (1 : R[X]) f = derivative f := by
  rw [mkDerivation_one_eq_derivative']
  rfl

/-- `Polynomial.mkDerivation` as a linear equivalence. -/
/-- `MvPolynomial.mkDerivation` as a linear equivalence. -/
def mkDerivationEquiv : (σ → A) ≃ₗ[R] Derivation R (MvPolynomial σ R) A := by sorry


@[target] lemma mkDerivationEquiv_apply (a : A) :
    mkDerivationEquiv R a = mkDerivation R a := by
  sorry


@[target] lemma mkDerivationEquiv_symm_apply (D : Derivation R R[X] A) :
    (mkDerivationEquiv R).symm D = D X := by sorry


end CommSemiring
end Polynomial

namespace Derivation

variable {R A M : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] [AddCommMonoid M]
  [Module A M] [Module R M] [IsScalarTower R A M] (d : Derivation R A M) (a : A)

open Polynomial Module

/--
For a derivation `d : A → M` and an element `a : A`, `d.compAEval a` is the
derivation of `R[X]` which takes a polynomial `f` to `d(aeval a f)`.

This derivation takes values in `Module.AEval R M a`, which is `M`, regarded as an
`R[X]`-module, with the action of a polynomial `f` defined by `f • m = (aeval a f) • m`.
-/
/-
Note: `compAEval` is not defined using `Derivation.compAlgebraMap`.
This because `A` is not an `R[X]` algebra and it would be messy to create an algebra instance
within the definition.
-/
@[simps]
def compAEval : Derivation R R[X] <| AEval R M a where
  toFun f          := AEval.of R M a (d (aeval a f))
  map_add'         := by simp
  map_smul'        := by simp
  leibniz'         := by simp [AEval.of_aeval_smul, -Derivation.map_aeval]
  map_one_eq_zero' := by simp

/--
A form of the chain rule: if `f` is a polynomial over `R`
and `d : A → M` is an `R`-derivation then for all `a : A` we have
$$ d(f(a)) = f' (a) d a. $$
The equation is in the `R[X]`-module `Module.AEval R M a`.
For the same equation in `M`, see `Derivation.compAEval_eq`.
-/
/--
A form of the chain rule: if `f` is a polynomial over `R`
and `d : A → M` is an `R`-derivation then for all `a : A` we have
$$ d(f(a)) = f' (a) d a. $$
The equation is in the `R[X]`-module `Module.AEval R M a`.
For the same equation in `M`, see `Derivation.compAEval_eq`.
-/
@[target] theorem compAEval_eq (d : Derivation R A M) (f : R[X]) :
    d.compAEval a f = derivative f • (AEval.of R M a (d a)) := by
  sorry


/--
A form of the chain rule: if `f` is a polynomial over `R`
and `d : A → M` is an `R`-derivation then for all `a : A` we have
$$ d(f(a)) = f' (a) d a. $$
The equation is in `M`. For the same equation in `Module.AEval R M a`,
see `Derivation.compAEval_eq`.
-/
/--
A form of the chain rule: if `f` is a polynomial over `R`
and `d : A → M` is an `R`-derivation then for all `a : A` we have
$$ d(f(a)) = f' (a) d a. $$
The equation is in `M`. For the same equation in `Module.AEval R M a`,
see `Derivation.compAEval_eq`.
-/
@[target] theorem comp_aeval_eq (d : Derivation R A M) (f : R[X]) :
    d (aeval a f) = aeval a (derivative f) • d a :=
  calc
    _ = (AEval.of R M a).symm (d.compAEval a f) := rfl
    _ = _ := by sorry


end Derivation
