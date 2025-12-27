import VerifiedAgora.tagger
/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.Algebra.Polynomial.Degree.Operations

/-!
# Degree and support of univariate polynomials

## Main results
* `Polynomial.as_sum_support`: write `p : R[X]` as a sum over its support
* `Polynomial.as_sum_range`: write `p : R[X]` as a sum over `{0, ..., natDegree p}`
* `Polynomial.natDegree_mem_support_of_nonzero`: `natDegree p ∈ support p` if `p ≠ 0`
-/

noncomputable section

open Finsupp Finset

open Polynomial

namespace Polynomial

universe u v

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

section Semiring

variable [Semiring R] {p q r : R[X]}

@[target]
theorem supDegree_eq_natDegree (p : R[X]) : p.toFinsupp.supDegree id = p.natDegree := by sorry

theorem le_natDegree_of_mem_supp (a : ℕ) : a ∈ p.support → a ≤ natDegree p :=
  le_natDegree_of_ne_zero ∘ mem_support_iff.mp

@[target]
theorem supp_subset_range (h : natDegree p < m) : p.support ⊆ Finset.range m := sorry

@[target]
theorem supp_subset_range_natDegree_succ : p.support ⊆ Finset.range (natDegree p + 1) :=
  sorry

@[target]
theorem as_sum_support (p : R[X]) : p = ∑ i ∈ p.support, monomial i (p.coeff i) :=
  sorry

@[target]
theorem as_sum_support_C_mul_X_pow (p : R[X]) : p = ∑ i ∈ p.support, C (p.coeff i) * X ^ i :=
  sorry
theorem sum_over_range' [AddCommMonoid S] (p : R[X]) {f : ℕ → R → S} (h : ∀ n, f n 0 = 0) (n : ℕ)
    (w : p.natDegree < n) : p.sum f = ∑ a ∈ range n, f a (coeff p a) := by
  rcases p with ⟨⟩
  have := supp_subset_range w
  simp only [Polynomial.sum, support, coeff, natDegree, degree] at this ⊢
  exact Finsupp.sum_of_support_subset _ this _ fun n _hn => h n

/-- We can reexpress a sum over `p.support` as a sum over `range (p.natDegree + 1)`.
-/
@[target]
theorem sum_over_range [AddCommMonoid S] (p : R[X]) {f : ℕ → R → S} (h : ∀ n, f n 0 = 0) :
    p.sum f = ∑ a ∈ range (p.natDegree + 1), f a (coeff p a) :=
  sorry

-- TODO this is essentially a duplicate of `sum_over_range`, and should be removed.
theorem sum_fin [AddCommMonoid S] (f : ℕ → R → S) (hf : ∀ i, f i 0 = 0) {n : ℕ} {p : R[X]}
    (hn : p.degree < n) : (∑ i : Fin n, f i (p.coeff i)) = p.sum f := by
  by_cases hp : p = 0
  · rw [hp, sum_zero_index, Finset.sum_eq_zero]
    intro i _
    exact hf i
  rw [sum_over_range' _ hf n ((natDegree_lt_iff_degree_lt hp).mpr hn),
    Fin.sum_univ_eq_sum_range fun i => f i (p.coeff i)]

theorem as_sum_range' (p : R[X]) (n : ℕ) (w : p.natDegree < n) :
    p = ∑ i ∈ range n, monomial i (coeff p i) :=
  p.sum_monomial_eq.symm.trans <| p.sum_over_range' monomial_zero_right _ w

@[target]
theorem as_sum_range (p : R[X]) : p = ∑ i ∈ range (p.natDegree + 1), monomial i (coeff p i) :=
  sorry

@[target]
theorem as_sum_range_C_mul_X_pow (p : R[X]) :
    p = ∑ i ∈ range (p.natDegree + 1), C (coeff p i) * X ^ i :=
  sorry

@[target]
theorem mem_support_C_mul_X_pow {n a : ℕ} {c : R} (h : a ∈ support (C c * X ^ n)) : a = n :=
  sorry

theorem card_support_C_mul_X_pow_le_one {c : R} {n : ℕ} : #(support (C c * X ^ n)) ≤ 1 := by
  rw [← card_singleton n]
  apply card_le_card (support_C_mul_X_pow' n c)

@[target]
theorem card_supp_le_succ_natDegree (p : R[X]) : #p.support ≤ p.natDegree + 1 := by sorry

@[target]
theorem le_degree_of_mem_supp (a : ℕ) : a ∈ p.support → ↑a ≤ degree p :=
  sorry

@[target]
theorem nonempty_support_iff : p.support.Nonempty ↔ p ≠ 0 := by sorry

end Semiring

section Semiring

variable [Semiring R] {p q : R[X]} {ι : Type*}

@[target]
theorem natDegree_mem_support_of_nonzero (H : p ≠ 0) : p.natDegree ∈ p.support := by sorry

theorem natDegree_eq_support_max' (h : p ≠ 0) :
    p.natDegree = p.support.max' (nonempty_support_iff.mpr h) :=
  (le_max' _ _ <| natDegree_mem_support_of_nonzero h).antisymm <|
    max'_le _ _ _ le_natDegree_of_mem_supp

end Semiring

end Polynomial
