import VerifiedAgora.tagger
/-
Copyright (c) 2020 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Polynomial.Reverse

/-!
# "Mirror" of a univariate polynomial

In this file we define `Polynomial.mirror`, a variant of `Polynomial.reverse`. The difference
between `reverse` and `mirror` is that `reverse` will decrease the degree if the polynomial is
divisible by `X`.

## Main definitions

- `Polynomial.mirror`

## Main results

- `Polynomial.mirror_mul_of_domain`: `mirror` preserves multiplication.
- `Polynomial.irreducible_of_mirror`: an irreducibility criterion involving `mirror`

-/


namespace Polynomial

section Semiring

variable {R : Type*} [Semiring R] (p q : R[X])

/-- mirror of a polynomial: reverses the coefficients while preserving `Polynomial.natDegree` -/
noncomputable def mirror :=
  p.reverse * X ^ p.natTrailingDegree

@[target] theorem mirror_zero : (0 : R[X]).mirror = 0 := by sorry


@[target] theorem mirror_monomial (n : ℕ) (a : R) : (monomial n a).mirror = monomial n a := by
  sorry

  classical
    by_cases ha : a = 0
    · rw [ha, monomial_zero_right, mirror_zero]
    · rw [mirror, reverse, natDegree_monomial n a, if_neg ha, natTrailingDegree_monomial ha, ←
        C_mul_X_pow_eq_monomial, reflect_C_mul_X_pow, revAt_le (le_refl n), tsub_self, pow_zero,
        mul_one]

@[target] theorem mirror_C (a : R) : (C a).mirror = C a := by sorry


@[target] theorem mirror_X : X.mirror = (X : R[X]) := by sorry


@[target] theorem mirror_natDegree : p.mirror.natDegree = p.natDegree := by
  sorry


@[target] theorem mirror_natTrailingDegree : p.mirror.natTrailingDegree = p.natTrailingDegree := by
  sorry


@[target] theorem coeff_mirror (n : ℕ) :
    p.mirror.coeff n = p.coeff (revAt (p.natDegree + p.natTrailingDegree) n) := by
  sorry

@[target] theorem mirror_eval_one : p.mirror.eval 1 = p.eval 1 := by
  sorry


@[target] theorem mirror_mirror : p.mirror.mirror = p :=
  Polynomial.ext fun n => by
    sorry


variable {p q}

@[target] theorem mirror_involutive : Function.Involutive (mirror : R[X] → R[X]) := by sorry


@[target] theorem mirror_eq_iff : p.mirror = q ↔ p = q.mirror := by sorry


@[target] theorem mirror_inj : p.mirror = q.mirror ↔ p = q := by sorry


@[simp]
theorem mirror_eq_zero : p.mirror = 0 ↔ p = 0 :=
  ⟨fun h => by rw [← p.mirror_mirror, h, mirror_zero], fun h => by rw [h, mirror_zero]⟩

variable (p q)

@[target] theorem mirror_trailingCoeff : p.mirror.trailingCoeff = p.leadingCoeff := by
  sorry


@[target] theorem mirror_leadingCoeff : p.mirror.leadingCoeff = p.trailingCoeff := by
  sorry


@[target] theorem coeff_mul_mirror :
    (p * p.mirror).coeff (p.natDegree + p.natTrailingDegree) = p.sum fun _ => (· ^ 2) := by
  sorry


variable [NoZeroDivisors R]

@[target] theorem natDegree_mul_mirror : (p * p.mirror).natDegree = 2 * p.natDegree := by
  sorry


@[target] theorem natTrailingDegree_mul_mirror :
    (p * p.mirror).natTrailingDegree = 2 * p.natTrailingDegree := by
  sorry


end Semiring

section Ring

variable {R : Type*} [Ring R] (p q : R[X])

@[target] theorem mirror_neg : (-p).mirror = -p.mirror := by
  sorry


variable [NoZeroDivisors R]

@[target] theorem mirror_mul_of_domain : (p * q).mirror = p.mirror * q.mirror := by
  sorry


@[target] theorem mirror_smul (a : R) : (a • p).mirror = a • p.mirror := by
  sorry


end Ring

section CommRing

variable {R : Type*} [CommRing R] [NoZeroDivisors R] {f : R[X]}

@[target] theorem irreducible_of_mirror (h1 : ¬IsUnit f)
    (h2 : ∀ k, f * f.mirror = k * k.mirror → k = f ∨ k = -f ∨ k = f.mirror ∨ k = -f.mirror)
    (h3 : IsRelPrime f f.mirror) : Irreducible f := by
  sorry


end CommRing

end Polynomial
