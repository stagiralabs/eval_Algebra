import VerifiedAgora.tagger
/-
Copyright (c) 2020 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Polynomial.EraseLead

/-!
# Denominators of evaluation of polynomials at ratios

Let `i : R → K` be a homomorphism of semirings.  Assume that `K` is commutative.  If `a` and
`b` are elements of `R` such that `i b ∈ K` is invertible, then for any polynomial
`f ∈ R[X]` the "mathematical" expression `b ^ f.natDegree * f (a / b) ∈ K` is in
the image of the homomorphism `i`.
-/


open Polynomial Finset

open Polynomial

section DenomsClearable

variable {R K : Type*} [Semiring R] [CommSemiring K] {i : R →+* K}
variable {a b : R} {bi : K}

-- TODO: use hypothesis (ub : IsUnit (i b)) to work with localizations.
/-- `denomsClearable` formalizes the property that `b ^ N * f (a / b)`
does not have denominators, if the inequality `f.natDegree ≤ N` holds.

The definition asserts the existence of an element `D` of `R` and an
element `bi = 1 / i b` of `K` such that clearing the denominators of
the fraction equals `i D`.
-/
def DenomsClearable (a b : R) (N : ℕ) (f : R[X]) (i : R →+* K) : Prop :=
  ∃ (D : R) (bi : K), bi * i b = 1 ∧ i D = i b ^ N * eval (i a * bi) (f.map i)

@[target]
theorem denomsClearable_zero (N : ℕ) (a : R) (bu : bi * i b = 1) : DenomsClearable a b N 0 i :=
  sorry

theorem denomsClearable_C_mul_X_pow {N : ℕ} (a : R) (bu : bi * i b = 1) {n : ℕ} (r : R)
    (nN : n ≤ N) : DenomsClearable a b N (C r * X ^ n) i := by
  refine ⟨r * a ^ n * b ^ (N - n), bi, bu, ?_⟩
  rw [C_mul_X_pow_eq_monomial, map_monomial, ← C_mul_X_pow_eq_monomial, eval_mul, eval_pow, eval_C]
  rw [RingHom.map_mul, RingHom.map_mul, RingHom.map_pow, RingHom.map_pow, eval_X, mul_comm]
  rw [← tsub_add_cancel_of_le nN]
  conv_lhs => rw [← mul_one (i a), ← bu]
  simp [mul_assoc, mul_comm, mul_left_comm, pow_add, mul_pow]

theorem DenomsClearable.add {N : ℕ} {f g : R[X]} :
    DenomsClearable a b N f i → DenomsClearable a b N g i → DenomsClearable a b N (f + g) i :=
  fun ⟨Df, bf, bfu, Hf⟩ ⟨Dg, bg, bgu, Hg⟩ =>
  ⟨Df + Dg, bf, bfu, by
    rw [RingHom.map_add, Polynomial.map_add, eval_add, mul_add, Hf, Hg]
    congr
    refine @inv_unique K _ (i b) bg bf ?_ ?_ <;> rwa [mul_comm]⟩

@[target]
theorem denomsClearable_of_natDegree_le (N : ℕ) (a : R) (bu : bi * i b = 1) :
    ∀ f : R[X], f.natDegree ≤ N → DenomsClearable a b N f i :=
  sorry
theorem denomsClearable_natDegree (i : R →+* K) (f : R[X]) (a : R) (bu : bi * i b = 1) :
    DenomsClearable a b f.natDegree f i :=
  denomsClearable_of_natDegree_le f.natDegree a bu f le_rfl

end DenomsClearable

open RingHom

/-- Evaluating a polynomial with integer coefficients at a rational number and clearing
denominators, yields a number greater than or equal to one.  The target can be any
`LinearOrderedField K`.
The assumption on `K` could be weakened to `LinearOrderedCommRing` assuming that the
image of the denominator is invertible in `K`. -/
@[target]
theorem one_le_pow_mul_abs_eval_div {K : Type*} [LinearOrderedField K] {f : ℤ[X]} {a b : ℤ}
    (b0 : 0 < b) (fab : eval ((a : K) / b) (f.map (algebraMap ℤ K)) ≠ 0) :
    (1 : K) ≤ (b : K) ^ f.natDegree * |eval ((a : K) / b) (f.map (algebraMap ℤ K))| := by sorry