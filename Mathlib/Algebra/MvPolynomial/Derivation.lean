import VerifiedAgora.tagger
/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.MvPolynomial.Supported
import Mathlib.RingTheory.Derivation.Basic

/-!
# Derivations of multivariate polynomials

In this file we prove that a derivation of `MvPolynomial σ R` is determined by its values on all
monomials `MvPolynomial.X i`. We also provide a constructor `MvPolynomial.mkDerivation` that
builds a derivation from its values on `X i`s and a linear equivalence
`MvPolynomial.mkDerivationEquiv` between `σ → A` and `Derivation (MvPolynomial σ R) A`.
-/


namespace MvPolynomial

noncomputable section

variable {σ R A : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A]
  [Module (MvPolynomial σ R) A]

section

variable (R)

/-- The derivation on `MvPolynomial σ R` that takes value `f i` on `X i`, as a linear map.
Use `MvPolynomial.mkDerivation` instead. -/
def mkDerivationₗ (f : σ → A) : MvPolynomial σ R →ₗ[R] A :=
  Finsupp.lsum R fun xs : σ →₀ ℕ =>
    (LinearMap.ringLmapEquivSelf R R A).symm <|
      xs.sum fun i k => monomial (xs - Finsupp.single i 1) (k : R) • f i

end

theorem mkDerivationₗ_monomial (f : σ → A) (s : σ →₀ ℕ) (r : R) :
    mkDerivationₗ R f (monomial s r) =
      r • s.sum fun i k => monomial (s - Finsupp.single i 1) (k : R) • f i :=
  sum_monomial_eq <| LinearMap.map_zero _

theorem mkDerivationₗ_C (f : σ → A) (r : R) : mkDerivationₗ R f (C r) = 0 :=
  (mkDerivationₗ_monomial f _ _).trans (smul_zero _)

theorem mkDerivationₗ_X (f : σ → A) (i : σ) : mkDerivationₗ R f (X i) = f i :=
  (mkDerivationₗ_monomial f _ _).trans <| by simp [tsub_self]

@[target] theorem derivation_C (D : Derivation R (MvPolynomial σ R) A) (a : R) : D (C a) = 0 := by sorry


@[target] theorem derivation_C_mul (D : Derivation R (MvPolynomial σ R) A) (a : R) (f : MvPolynomial σ R) :
    C (σ := σ) a • D f = a • D f := by
  sorry


/-- If two derivations agree on `X i`, `i ∈ s`, then they agree on all polynomials from
`MvPolynomial.supported R s`. -/
/-- If two derivations agree on `X i`, `i ∈ s`, then they agree on all polynomials from
`MvPolynomial.supported R s`. -/
@[target] theorem derivation_eqOn_supported {D₁ D₂ : Derivation R (MvPolynomial σ R) A} {s : Set σ}
    (h : Set.EqOn (D₁ ∘ X) (D₂ ∘ X) s) {f : MvPolynomial σ R} (hf : f ∈ supported R s) :
    D₁ f = D₂ f := by sorry


@[target] theorem derivation_eq_of_forall_mem_vars {D₁ D₂ : Derivation R (MvPolynomial σ R) A}
    {f : MvPolynomial σ R} (h : ∀ i ∈ f.vars, D₁ (X i) = D₂ (X i)) : D₁ f = D₂ f := by sorry


@[target] theorem derivation_eq_zero_of_forall_mem_vars {D : Derivation R (MvPolynomial σ R) A}
    {f : MvPolynomial σ R} (h : ∀ i ∈ f.vars, D (X i) = 0) : D f = 0 := by sorry


@[ext]
theorem derivation_ext {D₁ D₂ : Derivation R (MvPolynomial σ R) A} (h : ∀ i, D₁ (X i) = D₂ (X i)) :
    D₁ = D₂ :=
  Derivation.ext fun _ => derivation_eq_of_forall_mem_vars fun i _ => h i

variable [IsScalarTower R (MvPolynomial σ R) A]

@[target] theorem leibniz_iff_X (D : MvPolynomial σ R →ₗ[R] A) (h₁ : D 1 = 0) :
    (∀ p q, D (p * q) = p • D q + q • D p) ↔ ∀ s i, D (monomial s 1 * X i) =
    (monomial s 1 : MvPolynomial σ R) • D (X i) + (X i : MvPolynomial σ R) • D (monomial s 1) := by
  sorry


variable (R)

/-- The derivation on `MvPolynomial σ R` that takes value `f i` on `X i`. -/
/-- The derivation on `MvPolynomial σ R` that takes value `f i` on `X i`. -/
def mkDerivation (f : σ → A) : Derivation R (MvPolynomial σ R) A where
  toLinearMap := mkDerivationₗ R f
  map_one_eq_zero' := mkDerivationₗ_C _ 1
  leibniz' :=
    (leibniz_iff_X (mkDerivationₗ R f) (mkDerivationₗ_C _ 1)).2 fun s i => by
      sorry


@[target] theorem mkDerivation_X (f : σ → A) (i : σ) : mkDerivation R f (X i) = f i := by sorry


@[target] theorem mkDerivation_monomial (f : σ → A) (s : σ →₀ ℕ) (r : R) :
    mkDerivation R f (monomial s r) =
      r • s.sum fun i k => monomial (s - Finsupp.single i 1) (k : R) • f i := by sorry


/-- `MvPolynomial.mkDerivation` as a linear equivalence. -/
def mkDerivationEquiv : (σ → A) ≃ₗ[R] Derivation R (MvPolynomial σ R) A :=
  LinearEquiv.symm <|
    { invFun := mkDerivation R
      toFun := fun D i => D (X i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => derivation_ext <| mkDerivation_X _ _
      right_inv := fun _ => funext <| mkDerivation_X _ _ }

end

end MvPolynomial
