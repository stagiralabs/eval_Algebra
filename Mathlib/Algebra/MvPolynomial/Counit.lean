import VerifiedAgora.tagger
/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.MvPolynomial.Eval

/-!
## Counit morphisms for multivariate polynomials

One may consider the ring of multivariate polynomials `MvPolynomial A R` with coefficients in `R`
and variables indexed by `A`. If `A` is not just a type, but an algebra over `R`,
then there is a natural surjective algebra homomorphism `MvPolynomial A R →ₐ[R] A`
obtained by `X a ↦ a`.

### Main declarations

* `MvPolynomial.ACounit R A` is the natural surjective algebra homomorphism
  `MvPolynomial A R →ₐ[R] A` obtained by `X a ↦ a`
* `MvPolynomial.counit` is an “absolute” variant with `R = ℤ`
* `MvPolynomial.counitNat` is an “absolute” variant with `R = ℕ`

-/


namespace MvPolynomial

open Function

variable (A B R : Type*) [CommSemiring A] [CommSemiring B] [CommRing R] [Algebra A B]

/-- `MvPolynomial.ACounit A B` is the natural surjective algebra homomorphism
`MvPolynomial B A →ₐ[A] B` obtained by `X a ↦ a`.

See `MvPolynomial.counit` for the “absolute” variant with `A = ℤ`,
and `MvPolynomial.counitNat` for the “absolute” variant with `A = ℕ`. -/
noncomputable def ACounit : MvPolynomial B A →ₐ[A] B :=
  aeval id

variable {B}

@[target] theorem ACounit_X (b : B) : ACounit A B (X b) = b := by sorry


variable {A} (B)

@[target] theorem ACounit_C (a : A) : ACounit A B (C a) = algebraMap A B a := by sorry


variable (A)

@[target] theorem ACounit_surjective : Surjective (ACounit A B) := by sorry


/-- `MvPolynomial.counit R` is the natural surjective ring homomorphism
`MvPolynomial R ℤ →+* R` obtained by `X r ↦ r`.

See `MvPolynomial.ACounit` for a “relative” variant for algebras over a base ring,
and `MvPolynomial.counitNat` for the “absolute” variant with `R = ℕ`. -/
noncomputable def counit : MvPolynomial R ℤ →+* R :=
  (ACounit ℤ R).toRingHom

/-- `MvPolynomial.counitNat A` is the natural surjective ring homomorphism
`MvPolynomial A ℕ →+* A` obtained by `X a ↦ a`.

See `MvPolynomial.ACounit` for a “relative” variant for algebras over a base ring
and `MvPolynomial.counit` for the “absolute” variant with `A = ℤ`. -/
noncomputable def counitNat : MvPolynomial A ℕ →+* A :=
  ACounit ℕ A

@[target] theorem counit_surjective : Surjective (counit R) := by sorry


theorem counitNat_surjective : Surjective (counitNat A) :=
  ACounit_surjective ℕ A

@[target] theorem counit_C (n : ℤ) : counit R (C n) = n := by sorry


@[target] theorem counitNat_C (n : ℕ) : counitNat A (C n) = n := by sorry


variable {R A}

@[target] theorem counit_X (r : R) : counit R (X r) = r := by sorry


@[target] theorem counitNat_X (a : A) : counitNat A (X a) = a := by sorry


end MvPolynomial
