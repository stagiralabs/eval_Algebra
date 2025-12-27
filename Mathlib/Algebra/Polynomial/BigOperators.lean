import VerifiedAgora.tagger
/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark
-/
import Mathlib.Algebra.Polynomial.Monic

/-!
# Lemmas for the interaction between polynomials and `∑` and `∏`.

Recall that `∑` and `∏` are notation for `Finset.sum` and `Finset.prod` respectively.

## Main results

- `Polynomial.natDegree_prod_of_monic` : the degree of a product of monic polynomials is the
  product of degrees. We prove this only for `[CommSemiring R]`,
  but it ought to be true for `[Semiring R]` and `List.prod`.
- `Polynomial.natDegree_prod` : for polynomials over an integral domain,
  the degree of the product is the sum of degrees.
- `Polynomial.leadingCoeff_prod` : for polynomials over an integral domain,
  the leading coefficient is the product of leading coefficients.
- `Polynomial.prod_X_sub_C_coeff_card_pred` carries most of the content for computing
  the second coefficient of the characteristic polynomial.
-/


open Finset

open Multiset

open Polynomial

universe u w

variable {R : Type u} {ι : Type w}

namespace Polynomial

variable (s : Finset ι)

section Semiring

variable {S : Type*} [Semiring S]

@[target] theorem natDegree_list_sum_le (l : List S[X]) :
    natDegree l.sum ≤ (l.map natDegree).foldr max 0 := by
  sorry


@[target] theorem natDegree_multiset_sum_le (l : Multiset S[X]) :
    natDegree l.sum ≤ (l.map natDegree).foldr max 0 :=
  Quotient.inductionOn l (by sorry


@[target] theorem natDegree_sum_le (f : ι → S[X]) :
    natDegree (∑ i ∈ s, f i) ≤ s.fold max 0 (natDegree ∘ f) := by
  sorry


@[target] lemma natDegree_sum_le_of_forall_le {n : ℕ} (f : ι → S[X]) (h : ∀ i ∈ s, natDegree (f i) ≤ n) :
    natDegree (∑ i ∈ s, f i) ≤ n :=
  le_trans (natDegree_sum_le s f) <| (Finset.fold_max_le n).mpr <| by sorry


theorem degree_list_sum_le (l : List S[X]) : degree l.sum ≤ (l.map natDegree).maximum := by
  by_cases h : l.sum = 0
  · simp [h]
  · rw [degree_eq_natDegree h]
    suffices (l.map natDegree).maximum = ((l.map natDegree).foldr max 0 : ℕ) by
      rw [this]
      simpa using natDegree_list_sum_le l
    rw [← List.foldr_max_of_ne_nil]
    · congr
    contrapose! h
    rw [List.map_eq_nil_iff] at h
    simp [h]

theorem natDegree_list_prod_le (l : List S[X]) : natDegree l.prod ≤ (l.map natDegree).sum := by
  induction' l with hd tl IH
  · simp
  · simpa using natDegree_mul_le.trans (add_le_add_left IH _)

@[target] theorem degree_list_prod_le (l : List S[X]) : degree l.prod ≤ (l.map degree).sum := by
  sorry


@[target] theorem coeff_list_prod_of_natDegree_le (l : List S[X]) (n : ℕ) (hl : ∀ p ∈ l, natDegree p ≤ n) :
    coeff (List.prod l) (l.length * n) = (l.map fun p => coeff p n).prod := by
  sorry


end Semiring

section CommSemiring

variable [CommSemiring R] (f : ι → R[X]) (t : Multiset R[X])

@[target] theorem natDegree_multiset_prod_le : t.prod.natDegree ≤ (t.map natDegree).sum :=
  Quotient.inductionOn t (by sorry


@[target] theorem natDegree_prod_le : (∏ i ∈ s, f i).natDegree ≤ ∑ i ∈ s, (f i).natDegree := by
  sorry


/-- The degree of a product of polynomials is at most the sum of the degrees,
where the degree of the zero polynomial is ⊥.
-/
/-- The degree of a product of polynomials is at most the sum of the degrees,
where the degree of the zero polynomial is ⊥.
-/
@[target] theorem degree_multiset_prod_le : t.prod.degree ≤ (t.map Polynomial.degree).sum :=
  Quotient.inductionOn t (by sorry


@[target] theorem degree_prod_le : (∏ i ∈ s, f i).degree ≤ ∑ i ∈ s, (f i).degree := by
  sorry


/-- The leading coefficient of a product of polynomials is equal to
the product of the leading coefficients, provided that this product is nonzero.

See `Polynomial.leadingCoeff_multiset_prod` (without the `'`) for a version for integral domains,
where this condition is automatically satisfied.
-/
/-- The leading coefficient of a product of polynomials is equal to
the product of the leading coefficients.

See `Polynomial.leadingCoeff_multiset_prod'` (with a `'`) for a version for commutative semirings,
where additionally, the product of the leading coefficients must be nonzero.
-/
@[target] theorem leadingCoeff_multiset_prod :
    t.prod.leadingCoeff = (t.map fun f => leadingCoeff f).prod := by
  sorry


/-- The leading coefficient of a product of polynomials is equal to
the product of the leading coefficients, provided that this product is nonzero.

See `Polynomial.leadingCoeff_prod` (without the `'`) for a version for integral domains,
where this condition is automatically satisfied.
-/
/-- The leading coefficient of a product of polynomials is equal to
the product of the leading coefficients.

See `Polynomial.leadingCoeff_prod'` (with a `'`) for a version for commutative semirings,
where additionally, the product of the leading coefficients must be nonzero.
-/
@[target] theorem leadingCoeff_prod : (∏ i ∈ s, f i).leadingCoeff = ∏ i ∈ s, (f i).leadingCoeff := by
  sorry


/-- The degree of a product of polynomials is equal to
the sum of the degrees, provided that the product of leading coefficients is nonzero.

See `Polynomial.natDegree_multiset_prod` (without the `'`) for a version for integral domains,
where this condition is automatically satisfied.
-/
@[target] theorem natDegree_multiset_prod (h : (0 : R[X]) ∉ t) :
    natDegree t.prod = (t.map natDegree).sum := by
  sorry


/-- The degree of a product of polynomials is equal to
the sum of the degrees, provided that the product of leading coefficients is nonzero.

See `Polynomial.natDegree_prod` (without the `'`) for a version for integral domains,
where this condition is automatically satisfied.
-/
/-- The degree of a product of polynomials is equal to
the sum of the degrees.

See `Polynomial.natDegree_prod'` (with a `'`) for a version for commutative semirings,
where additionally, the product of the leading coefficients must be nonzero.
-/
@[target] theorem natDegree_prod (h : ∀ i ∈ s, f i ≠ 0) :
    (∏ i ∈ s, f i).natDegree = ∑ i ∈ s, (f i).natDegree := by
  sorry


@[target] theorem natDegree_multiset_prod_of_monic (h : ∀ f ∈ t, Monic f) :
    t.prod.natDegree = (t.map natDegree).sum := by
  sorry


@[target] theorem degree_multiset_prod_of_monic [Nontrivial R] (h : ∀ f ∈ t, Monic f) :
    t.prod.degree = (t.map degree).sum := by
  sorry


@[target] theorem natDegree_prod_of_monic (h : ∀ i ∈ s, (f i).Monic) :
    (∏ i ∈ s, f i).natDegree = ∑ i ∈ s, (f i).natDegree := by
  sorry


@[target] theorem degree_prod_of_monic [Nontrivial R] (h : ∀ i ∈ s, (f i).Monic) :
    (∏ i ∈ s, f i).degree = ∑ i ∈ s, (f i).degree := by
  sorry


theorem coeff_multiset_prod_of_natDegree_le (n : ℕ) (hl : ∀ p ∈ t, natDegree p ≤ n) :
    coeff t.prod ((Multiset.card t) * n) = (t.map fun p => coeff p n).prod := by
  induction t using Quotient.inductionOn
  simpa using coeff_list_prod_of_natDegree_le _ _ hl

@[target] theorem coeff_prod_of_natDegree_le (f : ι → R[X]) (n : ℕ) (h : ∀ p ∈ s, natDegree (f p) ≤ n) :
    coeff (∏ i ∈ s, f i) (#s * n) = ∏ i ∈ s, coeff (f i) n := by
  sorry


@[target] theorem coeff_zero_multiset_prod : t.prod.coeff 0 = (t.map fun f => coeff f 0).prod := by
  sorry


theorem coeff_zero_prod : (∏ i ∈ s, f i).coeff 0 = ∏ i ∈ s, (f i).coeff 0 := by
  simpa using coeff_zero_multiset_prod (s.1.map f)

end CommSemiring

section CommRing

variable [CommRing R]

open Monic

-- Eventually this can be generalized with Vieta's formulas
-- plus the connection between roots and factorization.
@[target] theorem multiset_prod_X_sub_C_nextCoeff (t : Multiset R) :
    nextCoeff (t.map fun x => X - C x).prod = -t.sum := by
  sorry


@[target] theorem prod_X_sub_C_nextCoeff {s : Finset ι} (f : ι → R) :
    nextCoeff (∏ i ∈ s, (X - C (f i))) = -∑ i ∈ s, f i := by
  sorry


@[target] theorem multiset_prod_X_sub_C_coeff_card_pred (t : Multiset R) (ht : 0 < Multiset.card t) :
    (t.map fun x => X - C x).prod.coeff ((Multiset.card t) - 1) = -t.sum := by
  sorry


@[target] theorem prod_X_sub_C_coeff_card_pred (s : Finset ι) (f : ι → R) (hs : 0 < #s) :
    (∏ i ∈ s, (X - C (f i))).coeff (#s - 1) = -∑ i ∈ s, f i := by
  sorry


variable [IsDomain R]

@[target] lemma natDegree_multiset_prod_X_sub_C_eq_card (s : Multiset R) :
    (s.map (X - C ·)).prod.natDegree = Multiset.card s := by
  sorry


end CommRing

section NoZeroDivisors

section Semiring

variable [Semiring R] [NoZeroDivisors R]

/-- The degree of a product of polynomials is equal to
the sum of the degrees, where the degree of the zero polynomial is ⊥.
`[Nontrivial R]` is needed, otherwise for `l = []` we have `⊥` in the LHS and `0` in the RHS.
-/
/-- The degree of a product of polynomials is equal to
the sum of the degrees, where the degree of the zero polynomial is ⊥.
`[Nontrivial R]` is needed, otherwise for `l = []` we have `⊥` in the LHS and `0` in the RHS.
-/
@[target] theorem degree_list_prod [Nontrivial R] (l : List R[X]) : l.prod.degree = (l.map degree).sum := by sorry


end Semiring

section CommSemiring

variable [CommSemiring R] [NoZeroDivisors R] (f : ι → R[X]) (t : Multiset R[X])

/-- The degree of a product of polynomials is equal to
the sum of the degrees.

See `Polynomial.natDegree_prod'` (with a `'`) for a version for commutative semirings,
where additionally, the product of the leading coefficients must be nonzero.
-/
theorem natDegree_prod (h : ∀ i ∈ s, f i ≠ 0) :
    (∏ i ∈ s, f i).natDegree = ∑ i ∈ s, (f i).natDegree := by
  nontriviality R
  apply natDegree_prod'
  rw [prod_ne_zero_iff]
  intro x hx; simp [h x hx]

theorem natDegree_multiset_prod (h : (0 : R[X]) ∉ t) :
    natDegree t.prod = (t.map natDegree).sum := by
  nontriviality R
  rw [natDegree_multiset_prod']
  simp_rw [Ne, Multiset.prod_eq_zero_iff, Multiset.mem_map, leadingCoeff_eq_zero]
  rintro ⟨_, h, rfl⟩
  contradiction

/-- The degree of a product of polynomials is equal to
the sum of the degrees, where the degree of the zero polynomial is ⊥.
-/
/-- The degree of a product of polynomials is equal to
the sum of the degrees, where the degree of the zero polynomial is ⊥.
-/
@[target] theorem degree_multiset_prod [Nontrivial R] : t.prod.degree = (t.map fun f => degree f).sum := by sorry


/-- The degree of a product of polynomials is equal to
the sum of the degrees, where the degree of the zero polynomial is ⊥.
-/
/-- The degree of a product of polynomials is equal to
the sum of the degrees, where the degree of the zero polynomial is ⊥.
-/
@[target] theorem degree_prod [Nontrivial R] : (∏ i ∈ s, f i).degree = ∑ i ∈ s, (f i).degree := by sorry


/-- The leading coefficient of a product of polynomials is equal to
the product of the leading coefficients.

See `Polynomial.leadingCoeff_multiset_prod'` (with a `'`) for a version for commutative semirings,
where additionally, the product of the leading coefficients must be nonzero.
-/
theorem leadingCoeff_multiset_prod :
    t.prod.leadingCoeff = (t.map fun f => leadingCoeff f).prod := by
  rw [← leadingCoeffHom_apply, MonoidHom.map_multiset_prod]
  simp only [leadingCoeffHom_apply]

/-- The leading coefficient of a product of polynomials is equal to
the product of the leading coefficients.

See `Polynomial.leadingCoeff_prod'` (with a `'`) for a version for commutative semirings,
where additionally, the product of the leading coefficients must be nonzero.
-/
theorem leadingCoeff_prod : (∏ i ∈ s, f i).leadingCoeff = ∏ i ∈ s, (f i).leadingCoeff := by
  simpa using leadingCoeff_multiset_prod (s.1.map f)

end CommSemiring

end NoZeroDivisors

end Polynomial
