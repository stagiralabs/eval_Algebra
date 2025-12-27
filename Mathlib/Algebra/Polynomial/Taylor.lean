import VerifiedAgora.tagger
/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Algebra.Polynomial.HasseDeriv

/-!
# Taylor expansions of polynomials

## Main declarations

* `Polynomial.taylor`: the Taylor expansion of the polynomial `f` at `r`
* `Polynomial.taylor_coeff`: the `k`th coefficient of `taylor r f` is
  `(Polynomial.hasseDeriv k f).eval r`
* `Polynomial.eq_zero_of_hasseDeriv_eq_zero`:
  the identity principle: a polynomial is 0 iff all its Hasse derivatives are zero

-/


noncomputable section

namespace Polynomial

variable {R : Type*} [Semiring R] (r : R) (f : R[X])

/-- The Taylor expansion of a polynomial `f` at `r`. -/
/-- The Taylor expansion of a polynomial `f` at `r`. -/
def taylor (r : R) : R[X] →ₗ[R] R[X] where
  toFun f := f.comp (X + C r)
  map_add' _ _ := add_comp
  map_smul' c f := by sorry


@[target] theorem taylor_apply : taylor r f = f.comp (X + C r) := by sorry


@[target] theorem taylor_X : taylor r X = X + C r := by sorry


@[simp]
theorem taylor_C (x : R) : taylor r (C x) = C x := by simp only [taylor_apply, C_comp]

@[target] theorem taylor_zero (f : R[X]) : taylor 0 f = f := by sorry


theorem taylor_zero (f : R[X]) : taylor 0 f = f := by rw [taylor_zero', LinearMap.id_apply]

@[simp]
theorem taylor_one : taylor r (1 : R[X]) = C 1 := by rw [← C_1, taylor_C]

@[simp]
theorem taylor_monomial (i : ℕ) (k : R) : taylor r (monomial i k) = C k * (X + C r) ^ i := by
  simp [taylor_apply]

/-- The `k`th coefficient of `Polynomial.taylor r f` is `(Polynomial.hasseDeriv k f).eval r`. -/
/-- The `k`th coefficient of `Polynomial.taylor r f` is `(Polynomial.hasseDeriv k f).eval r`. -/
@[target] theorem taylor_coeff (n : ℕ) : (taylor r f).coeff n = (hasseDeriv n f).eval r :=
  show (lcoeff R n).comp (taylor r) f = (leval r).comp (hasseDeriv n) f by
    sorry


@[target] theorem taylor_coeff_zero : (taylor r f).coeff 0 = f.eval r := by
  sorry


@[simp]
theorem taylor_coeff_one : (taylor r f).coeff 1 = f.derivative.eval r := by
  rw [taylor_coeff, hasseDeriv_one]

@[target] theorem natDegree_taylor (p : R[X]) (r : R) : natDegree (taylor r p) = natDegree p := by
  sorry


@[target] theorem taylor_mul {R} [CommSemiring R] (r : R) (p q : R[X]) :
    taylor r (p * q) = taylor r p * taylor r q := by sorry


/-- `Polynomial.taylor` as an `AlgHom` for commutative semirings -/
@[simps!]
def taylorAlgHom {R} [CommSemiring R] (r : R) : R[X] →ₐ[R] R[X] :=
  AlgHom.ofLinearMap (taylor r) (taylor_one r) (taylor_mul r)

@[target] theorem taylor_taylor {R} [CommSemiring R] (f : R[X]) (r s : R) :
    taylor r (taylor s f) = taylor (r + s) f := by
  sorry


@[target] theorem taylor_eval {R} [CommSemiring R] (r : R) (f : R[X]) (s : R) :
    (taylor r f).eval s = f.eval (s + r) := by
  sorry


@[target] theorem taylor_eval_sub {R} [CommRing R] (r : R) (f : R[X]) (s : R) :
    (taylor r f).eval (s - r) = f.eval s := by sorry


@[target] theorem taylor_injective {R} [CommRing R] (r : R) : Function.Injective (taylor r) := by
  sorry


@[target] theorem eq_zero_of_hasseDeriv_eq_zero {R} [CommRing R] (f : R[X]) (r : R)
    (h : ∀ k, (hasseDeriv k f).eval r = 0) : f = 0 := by
  sorry


/-- Taylor's formula. -/
/-- Taylor's formula. -/
@[target] theorem sum_taylor_eq {R} [CommRing R] (f : R[X]) (r : R) :
    ((taylor r f).sum fun i a => C a * (X - C r) ^ i) = f := by
  sorry


@[target] theorem eval_add_of_sq_eq_zero {A} [CommSemiring A] (p : Polynomial A) (x y : A) (hy : y ^ 2 = 0) :
    p.eval (x + y) = p.eval x + p.derivative.eval x * y := by
  sorry


end Polynomial
