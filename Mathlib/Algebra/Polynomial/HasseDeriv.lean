import VerifiedAgora.tagger
/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Hasse derivative of polynomials

The `k`th Hasse derivative of a polynomial `∑ a_i X^i` is `∑ (i.choose k) a_i X^(i-k)`.
It is a variant of the usual derivative, and satisfies `k! * (hasseDeriv k f) = derivative^[k] f`.
The main benefit is that is gives an atomic way of talking about expressions such as
`(derivative^[k] f).eval r / k!`, that occur in Taylor expansions, for example.

## Main declarations

In the following, we write `D k` for the `k`-th Hasse derivative `hasse_deriv k`.

* `Polynomial.hasseDeriv`: the `k`-th Hasse derivative of a polynomial
* `Polynomial.hasseDeriv_zero`: the `0`th Hasse derivative is the identity
* `Polynomial.hasseDeriv_one`: the `1`st Hasse derivative is the usual derivative
* `Polynomial.factorial_smul_hasseDeriv`: the identity `k! • (D k f) = derivative^[k] f`
* `Polynomial.hasseDeriv_comp`: the identity `(D k).comp (D l) = (k+l).choose k • D (k+l)`
* `Polynomial.hasseDeriv_mul`:
  the "Leibniz rule" `D k (f * g) = ∑ ij ∈ antidiagonal k, D ij.1 f * D ij.2 g`

For the identity principle, see `Polynomial.eq_zero_of_hasseDeriv_eq_zero`
in `Data/Polynomial/Taylor.lean`.

## Reference

https://math.fontein.de/2009/08/12/the-hasse-derivative/

-/


noncomputable section

namespace Polynomial

open Nat Polynomial

open Function

variable {R : Type*} [Semiring R] (k : ℕ) (f : R[X])

/-- The `k`th Hasse derivative of a polynomial `∑ a_i X^i` is `∑ (i.choose k) a_i X^(i-k)`.
It satisfies `k! * (hasse_deriv k f) = derivative^[k] f`. -/
/-- The `k`th Hasse derivative of a polynomial `∑ a_i X^i` is `∑ (i.choose k) a_i X^(i-k)`.
It satisfies `k! * (hasse_deriv k f) = derivative^[k] f`. -/
def hasseDeriv (k : ℕ) : R[X] →ₗ[R] R[X] := by sorry


@[target] theorem hasseDeriv_apply :
    hasseDeriv k f = f.sum fun i r => monomial (i - k) (↑(i.choose k) * r) := by
  sorry


theorem hasseDeriv_coeff (n : ℕ) :
    (hasseDeriv k f).coeff n = (n + k).choose k * f.coeff (n + k) := by
  rw [hasseDeriv_apply, coeff_sum, sum_def, Finset.sum_eq_single (n + k), coeff_monomial]
  · simp only [if_true, add_tsub_cancel_right, eq_self_iff_true]
  · intro i _hi hink
    rw [coeff_monomial]
    by_cases hik : i < k
    · simp only [Nat.choose_eq_zero_of_lt hik, ite_self, Nat.cast_zero, zero_mul]
    · push_neg at hik
      rw [if_neg]
      contrapose! hink
      exact (tsub_eq_iff_eq_add_of_le hik).mp hink
  · intro h
    simp only [not_mem_support_iff.mp h, monomial_zero_right, mul_zero, coeff_zero]

@[target] theorem hasseDeriv_zero : @hasseDeriv R _ 0 = LinearMap.id := by sorry


@[simp]
theorem hasseDeriv_zero : @hasseDeriv R _ 0 = LinearMap.id :=
  LinearMap.ext <| hasseDeriv_zero'

theorem hasseDeriv_eq_zero_of_lt_natDegree (p : R[X]) (n : ℕ) (h : p.natDegree < n) :
    hasseDeriv n p = 0 := by
  rw [hasseDeriv_apply, sum_def]
  refine Finset.sum_eq_zero fun x hx => ?_
  simp [Nat.choose_eq_zero_of_lt ((le_natDegree_of_mem_supp _ hx).trans_lt h)]

@[target] theorem hasseDeriv_one : @hasseDeriv R _ 1 = derivative := by sorry


@[simp]
theorem hasseDeriv_one : @hasseDeriv R _ 1 = derivative :=
  LinearMap.ext <| hasseDeriv_one'

@[simp]
theorem hasseDeriv_monomial (n : ℕ) (r : R) :
    hasseDeriv k (monomial n r) = monomial (n - k) (↑(n.choose k) * r) := by
  ext i
  simp only [hasseDeriv_coeff, coeff_monomial]
  by_cases hnik : n = i + k
  · rw [if_pos hnik, if_pos, ← hnik]
    apply tsub_eq_of_eq_add_rev
    rwa [add_comm]
  · rw [if_neg hnik, mul_zero]
    by_cases hkn : k ≤ n
    · rw [← tsub_eq_iff_eq_add_of_le hkn] at hnik
      rw [if_neg hnik]
    · push_neg at hkn
      rw [Nat.choose_eq_zero_of_lt hkn, Nat.cast_zero, zero_mul, ite_self]

@[target] theorem hasseDeriv_C (r : R) (hk : 0 < k) : hasseDeriv k (C r) = 0 := by
  sorry


@[target] theorem hasseDeriv_apply_one (hk : 0 < k) : hasseDeriv k (1 : R[X]) = 0 := by
  sorry


@[target] theorem hasseDeriv_X (hk : 1 < k) : hasseDeriv k (X : R[X]) = 0 := by
  sorry


@[target] theorem factorial_smul_hasseDeriv : ⇑(k ! • @hasseDeriv R _ k) = (@derivative R _)^[k] := by
  sorry


@[target] theorem hasseDeriv_comp (k l : ℕ) :
    (@hasseDeriv R _ k).comp (hasseDeriv l) = (k + l).choose k • hasseDeriv (k + l) := by
  sorry


@[target] theorem natDegree_hasseDeriv_le (p : R[X]) (n : ℕ) :
    natDegree (hasseDeriv n p) ≤ natDegree p - n := by
  sorry

  classical
    rw [hasseDeriv_apply, sum_def]
    refine (natDegree_sum_le _ _).trans ?_
    simp_rw [Function.comp, natDegree_monomial]
    rw [Finset.fold_ite, Finset.fold_const]
    · simp only [ite_self, max_eq_right, zero_le', Finset.fold_max_le, true_and, and_imp,
        tsub_le_iff_right, mem_support_iff, Ne, Finset.mem_filter]
      intro x hx hx'
      have hxp : x ≤ p.natDegree := le_natDegree_of_ne_zero hx
      have hxn : n ≤ x := by
        contrapose! hx'
        simp [Nat.choose_eq_zero_of_lt hx']
      rwa [tsub_add_cancel_of_le (hxn.trans hxp)]
    · simp

@[target] theorem natDegree_hasseDeriv [NoZeroSMulDivisors ℕ R] (p : R[X]) (n : ℕ) :
    natDegree (hasseDeriv n p) = natDegree p - n := by
  sorry


section

open AddMonoidHom Finset.Nat

open Finset (antidiagonal mem_antidiagonal)

@[target] theorem hasseDeriv_mul (f g : R[X]) :
    hasseDeriv k (f * g) = ∑ ij ∈ antidiagonal k, hasseDeriv ij.1 f * hasseDeriv ij.2 g := by
  sorry


end

end Polynomial
