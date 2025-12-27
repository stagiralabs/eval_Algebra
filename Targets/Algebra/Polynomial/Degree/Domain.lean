import VerifiedAgora.tagger
/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
import Mathlib.Algebra.Polynomial.Degree.Operations

/-!
# Univariate polynomials form a domain

## Main results

* `Polynomial.instNoZeroDivisors`: `R[X]` has no zero divisors if `R` does not
* `Polynomial.instDomain`: `R[X]` is a domain if `R` is
-/

noncomputable section

open Finsupp Finset

open Polynomial

namespace Polynomial

universe u v

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

section Semiring

variable [Semiring R] [NoZeroDivisors R] {p q : R[X]}

instance : NoZeroDivisors R[X] where
  eq_zero_or_eq_zero_of_mul_eq_zero h := by
    rw [← leadingCoeff_eq_zero, ← leadingCoeff_eq_zero]
    refine eq_zero_or_eq_zero_of_mul_eq_zero ?_
    rw [← leadingCoeff_zero, ← leadingCoeff_mul, h]

lemma natDegree_mul (hp : p ≠ 0) (hq : q ≠ 0) : (p*q).natDegree = p.natDegree + q.natDegree := by
  rw [← Nat.cast_inj (R := WithBot ℕ), ← degree_eq_natDegree (mul_ne_zero hp hq),
    Nat.cast_add, ← degree_eq_natDegree hp, ← degree_eq_natDegree hq, degree_mul]

variable (p) in
lemma natDegree_smul (ha : a ≠ 0) : (a • p).natDegree = p.natDegree := by
  by_cases hp : p = 0
  · simp only [hp, smul_zero]
  · apply natDegree_eq_of_le_of_coeff_ne_zero
    · exact (natDegree_smul_le _ _).trans (le_refl _)
    · simpa only [coeff_smul, coeff_natDegree, smul_eq_mul, ne_eq, mul_eq_zero,
        leadingCoeff_eq_zero, not_or] using ⟨ha, hp⟩

@[target, simp]
lemma natDegree_pow (p : R[X]) (n : ℕ) : natDegree (p ^ n) = n * natDegree p := by sorry

@[target]
lemma natDegree_le_of_dvd (h1 : p ∣ q) (h2 : q ≠ 0) : p.natDegree ≤ q.natDegree := by sorry

@[target]
lemma degree_le_of_dvd (h1 : p ∣ q) (h2 : q ≠ 0) : degree p ≤ degree q := by sorry

@[target]
lemma eq_zero_of_dvd_of_degree_lt (h₁ : p ∣ q) (h₂ : degree q < degree p) : q = 0 := by sorry

@[target]
lemma eq_zero_of_dvd_of_natDegree_lt (h₁ : p ∣ q) (h₂ : natDegree q < natDegree p) :
    q = 0 := by sorry

lemma not_dvd_of_degree_lt (h0 : q ≠ 0) (hl : q.degree < p.degree) : ¬p ∣ q := by
  by_contra hcontra
  exact h0 (eq_zero_of_dvd_of_degree_lt hcontra hl)

@[target]
lemma not_dvd_of_natDegree_lt (h0 : q ≠ 0) (hl : q.natDegree < p.natDegree) :
    ¬p ∣ q := by sorry
@[target]
lemma natDegree_sub_eq_of_prod_eq {p₁ p₂ q₁ q₂ : R[X]} (hp₁ : p₁ ≠ 0) (hq₁ : q₁ ≠ 0)
    (hp₂ : p₂ ≠ 0) (hq₂ : q₂ ≠ 0) (h_eq : p₁ * q₂ = p₂ * q₁) :
    (p₁.natDegree : ℤ) - q₁.natDegree = (p₂.natDegree : ℤ) - q₂.natDegree := by sorry

end Semiring

section Ring

variable [Ring R] [Nontrivial R] [IsDomain R] {p q : R[X]}

instance : IsDomain R[X] := NoZeroDivisors.to_isDomain _

end Ring
end Polynomial
