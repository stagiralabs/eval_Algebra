import VerifiedAgora.tagger
/-
Copyright (c) 2020 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Eval.Subring
import Mathlib.Algebra.Polynomial.Monic

/-!
# Polynomials that lift

Given semirings `R` and `S` with a morphism `f : R →+* S`, we define a subsemiring `lifts` of
`S[X]` by the image of `RingHom.of (map f)`.
Then, we prove that a polynomial that lifts can always be lifted to a polynomial of the same degree
and that a monic polynomial that lifts can be lifted to a monic polynomial (of the same degree).

## Main definition

* `lifts (f : R →+* S)` : the subsemiring of polynomials that lift.

## Main results

* `lifts_and_degree_eq` : A polynomial lifts if and only if it can be lifted to a polynomial
of the same degree.
* `lifts_and_degree_eq_and_monic` : A monic polynomial lifts if and only if it can be lifted to a
monic polynomial of the same degree.
* `lifts_iff_alg` : if `R` is commutative, a polynomial lifts if and only if it is in the image of
`mapAlg`, where `mapAlg : R[X] →ₐ[R] S[X]` is the only `R`-algebra map
that sends `X` to `X`.

## Implementation details

In general `R` and `S` are semiring, so `lifts` is a semiring. In the case of rings, see
`lifts_iff_lifts_ring`.

Since we do not assume `R` to be commutative, we cannot say in general that the set of polynomials
that lift is a subalgebra. (By `lift_iff` this is true if `R` is commutative.)

-/


open Polynomial

noncomputable section

namespace Polynomial

universe u v w

section Semiring

variable {R : Type u} [Semiring R] {S : Type v} [Semiring S] {f : R →+* S}

/-- We define the subsemiring of polynomials that lifts as the image of `RingHom.of (map f)`. -/
/-- We define the subsemiring of polynomials that lifts as the image of `RingHom.of (map f)`. -/
def lifts (f : R →+* S) : Subsemiring S[X] := by sorry


@[target] theorem mem_lifts (p : S[X]) : p ∈ lifts f ↔ ∃ q : R[X], map f q = p := by
  sorry


@[target] theorem lifts_iff_set_range (p : S[X]) : p ∈ lifts f ↔ p ∈ Set.range (map f) := by
  sorry


theorem lifts_iff_ringHom_rangeS (p : S[X]) : p ∈ lifts f ↔ p ∈ (mapRingHom f).rangeS := by
  simp only [coe_mapRingHom, lifts, Set.mem_range, RingHom.mem_rangeS]

@[target] theorem lifts_iff_coeff_lifts (p : S[X]) : p ∈ lifts f ↔ ∀ n : ℕ, p.coeff n ∈ Set.range f := by
  sorry


@[target] theorem lifts_iff_coeffs_subset_range (p : S[X]) :
    p ∈ lifts f ↔ (p.coeffs : Set S) ⊆ Set.range f := by
  sorry


/-- If `(r : R)`, then `C (f r)` lifts. -/
/-- If `(r : R)`, then `C (f r)` lifts. -/
@[target] theorem C_mem_lifts (f : R →+* S) (r : R) : C (f r) ∈ lifts f :=
  ⟨C r, by
    sorry


/-- If `(s : S)` is in the image of `f`, then `C s` lifts. -/
/-- The ring homomorphism `C`, including `R` into the ring of Laurent polynomials over `R` as
the constant Laurent polynomials. -/
def C : R →+* R[T;T⁻¹] := by sorry


/-- The polynomial `X` lifts. -/
/-- The polynomial `X` lifts. -/
@[target] theorem X_mem_lifts (f : R →+* S) : (X : S[X]) ∈ lifts f :=
  ⟨X, by
    sorry


/-- The polynomial `X ^ n` lifts. -/
/-- The polynomial `X ^ n` lifts. -/
@[target] theorem X_pow_mem_lifts (f : R →+* S) (n : ℕ) : (X ^ n : S[X]) ∈ lifts f :=
  ⟨X ^ n, by
    sorry


/-- If `p` lifts and `(r : R)` then `r * p` lifts. -/
/-- If `p` lifts and `(r : R)` then `r * p` lifts. -/
@[target] theorem base_mul_mem_lifts {p : S[X]} (r : R) (hp : p ∈ lifts f) : C (f r) * p ∈ lifts f := by
  sorry


/-- If `(s : S)` is in the image of `f`, then `monomial n s` lifts. -/
/-- If `(s : S)` is in the image of `f`, then `monomial n s` lifts. -/
@[target] theorem monomial_mem_lifts {s : S} (n : ℕ) (h : s ∈ Set.range f) : monomial n s ∈ lifts f := by
  sorry


/-- If `p` lifts then `p.erase n` lifts. -/
/-- If `p` lifts then `p.erase n` lifts. -/
@[target] theorem erase_mem_lifts {p : S[X]} (n : ℕ) (h : p ∈ lifts f) : p.erase n ∈ lifts f := by
  sorry


section LiftDeg

@[target] theorem monomial_mem_lifts_and_degree_eq {s : S} {n : ℕ} (hl : monomial n s ∈ lifts f) :
    ∃ q : R[X], map f q = monomial n s ∧ q.degree = (monomial n s).degree := by
  sorry


/-- A polynomial lifts if and only if it can be lifted to a polynomial of the same degree. -/
/-- A polynomial lifts if and only if it can be lifted to a polynomial of the same degree. -/
@[target] theorem mem_lifts_and_degree_eq {p : S[X]} (hlifts : p ∈ lifts f) :
    ∃ q : R[X], map f q = p ∧ q.degree = p.degree := by
  sorry


end LiftDeg

section Monic

/-- A monic polynomial lifts if and only if it can be lifted to a monic polynomial
of the same degree. -/
theorem lifts_and_degree_eq_and_monic [Nontrivial S] {p : S[X]} (hlifts : p ∈ lifts f)
    (hp : p.Monic) : ∃ q : R[X], map f q = p ∧ q.degree = p.degree ∧ q.Monic := by
  rw [lifts_iff_coeff_lifts] at hlifts
  let g : ℕ → R := fun k ↦ (hlifts k).choose
  have hg k : f (g k) = p.coeff k := (hlifts k).choose_spec
  let q : R[X] := X ^ p.natDegree + ∑ k ∈ Finset.range p.natDegree, C (g k) * X ^ k
  have hq : map f q = p := by
    simp_rw [q, Polynomial.map_add, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow,
      map_X, map_C, hg, ← hp.as_sum]
  have h : q.Monic := monic_X_pow_add (by simp_rw [← Fin.sum_univ_eq_sum_range, degree_sum_fin_lt])
  exact ⟨q, hq, hq ▸ (h.degree_map f).symm, h⟩

@[target] theorem lifts_and_natDegree_eq_and_monic {p : S[X]} (hlifts : p ∈ lifts f) (hp : p.Monic) :
    ∃ q : R[X], map f q = p ∧ q.natDegree = p.natDegree ∧ q.Monic := by
  sorry


end Monic

end Semiring

section Ring

variable {R : Type u} [Ring R] {S : Type v} [Ring S] (f : R →+* S)

/-- The subring of polynomials that lift. -/
/-- The subring of polynomials that lift. -/
def liftsRing (f : R →+* S) : Subring S[X] := by sorry


/-- If `R` and `S` are rings, `p` is in the subring of polynomials that lift if and only if it is in
the subsemiring of polynomials that lift. -/
theorem lifts_iff_liftsRing (p : S[X]) : p ∈ lifts f ↔ p ∈ liftsRing f := by
  simp only [lifts, liftsRing, RingHom.mem_range, RingHom.mem_rangeS]

end Ring

section Algebra

variable {R : Type u} [CommSemiring R] {S : Type v} [Semiring S] [Algebra R S]

/-- The map `R[X] → S[X]` as an algebra homomorphism. -/
/-- The map `R[X] → S[X]` as an algebra homomorphism. -/
def mapAlg (R : Type u) [CommSemiring R] (S : Type v) [Semiring S] [Algebra R S] :
    R[X] →ₐ[R] S[X] := by sorry


/-- `mapAlg` is the morphism induced by `R → S`. -/
/-- `mapAlg` is the morphism induced by `R → S`. -/
@[target] theorem mapAlg_eq_map (p : R[X]) : mapAlg R S p = map (algebraMap R S) p := by
  sorry


/-- A polynomial `p` lifts if and only if it is in the image of `mapAlg`. -/
/-- A polynomial `p` lifts if and only if it is in the image of `mapAlg`. -/
@[target] theorem mem_lifts_iff_mem_alg (R : Type u) [CommSemiring R] {S : Type v} [Semiring S] [Algebra R S]
    (p : S[X]) : p ∈ lifts (algebraMap R S) ↔ p ∈ AlgHom.range (@mapAlg R _ S _ _) := by
  sorry


/-- If `p` lifts and `(r : R)` then `r • p` lifts. -/
/-- If `p` lifts and `(r : R)` then `r • p` lifts. -/
@[target] theorem smul_mem_lifts {p : S[X]} (r : R) (hp : p ∈ lifts (algebraMap R S)) :
    r • p ∈ lifts (algebraMap R S) := by
  sorry


end Algebra

end Polynomial
