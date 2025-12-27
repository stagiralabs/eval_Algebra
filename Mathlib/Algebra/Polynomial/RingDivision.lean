import VerifiedAgora.tagger
/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker, Johan Commelin
-/
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.Coprime.Basic

/-!
# Theory of univariate polynomials

We prove basic results about univariate polynomials.

-/

assert_not_exists Ideal.map

noncomputable section

open Polynomial

open Finset

namespace Polynomial

universe u v w z

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

section CommRing

variable [CommRing R] {p q : R[X]}

section

variable [Semiring S]

@[target] theorem natDegree_pos_of_aeval_root [Algebra R S] {p : R[X]} (hp : p ≠ 0) {z : S}
    (hz : aeval z p = 0) (inj : ∀ x : R, algebraMap R S x = 0 → x = 0) : 0 < p.natDegree := by sorry


@[target] theorem degree_pos_of_aeval_root [Algebra R S] {p : R[X]} (hp : p ≠ 0) {z : S} (hz : aeval z p = 0)
    (inj : ∀ x : R, algebraMap R S x = 0 → x = 0) : 0 < p.degree := by sorry


end

@[target] theorem smul_modByMonic (c : R) (p : R[X]) : c • p %ₘ q = c • (p %ₘ q) := by
  sorry


/-- `_ %ₘ q` as an `R`-linear map. -/
/-- `_ %ₘ q` as an `R`-linear map. -/
@[simps]
def modByMonicHom (q : R[X]) : R[X] →ₗ[R] R[X] where
  toFun p := by sorry


@[target] theorem mem_ker_modByMonic (hq : q.Monic) {p : R[X]} :
    p ∈ LinearMap.ker (modByMonicHom q) ↔ q ∣ p := by sorry


section

variable [Ring S]

@[target] theorem aeval_modByMonic_eq_self_of_root [Algebra R S] {p q : R[X]} (hq : q.Monic) {x : S}
    (hx : aeval x q = 0) : aeval x (p %ₘ q) = aeval x p := by
    --`eval₂_modByMonic_eq_self_of_root` doesn't work here as it needs commutativity
  sorry


end

end CommRing

section NoZeroDivisors

variable [Semiring R] [NoZeroDivisors R] {p q : R[X]}

@[target] theorem trailingDegree_mul : (p * q).trailingDegree = p.trailingDegree + q.trailingDegree := by
  sorry


end NoZeroDivisors


section CommRing

variable [CommRing R]

theorem rootMultiplicity_eq_rootMultiplicity {p : R[X]} {t : R} :
    p.rootMultiplicity t = (p.comp (X + C t)).rootMultiplicity 0 := by
  classical
  simp_rw [rootMultiplicity_eq_multiplicity, comp_X_add_C_eq_zero_iff]
  congr 1
  rw [C_0, sub_zero]
  convert (multiplicity_map_eq <| algEquivAevalXAddC t).symm using 2
  simp [C_eq_algebraMap]

/-- See `Polynomial.rootMultiplicity_eq_natTrailingDegree'` for the special case of `t = 0`. -/
/-- See `Polynomial.rootMultiplicity_eq_natTrailingDegree'` for the special case of `t = 0`. -/
@[target] theorem rootMultiplicity_eq_natTrailingDegree {p : R[X]} {t : R} :
    p.rootMultiplicity t = (p.comp (X + C t)).natTrailingDegree := by sorry


section nonZeroDivisors

open scoped nonZeroDivisors

theorem Monic.mem_nonZeroDivisors {p : R[X]} (h : p.Monic) : p ∈ R[X]⁰ :=
  mem_nonZeroDivisors_iff.2 fun _ hx ↦ (mul_left_eq_zero_iff h).1 hx

@[target] theorem mem_nonZeroDivisors_of_leadingCoeff {p : R[X]} (h : p.leadingCoeff ∈ R⁰) : p ∈ R[X]⁰ := by
  sorry


end nonZeroDivisors

@[target] theorem rootMultiplicity_mul_X_sub_C_pow {p : R[X]} {a : R} {n : ℕ} (h : p ≠ 0) :
    (p * (X - C a) ^ n).rootMultiplicity a = p.rootMultiplicity a + n := by
  sorry


/-- The multiplicity of `a` as root of `(X - a) ^ n` is `n`. -/
theorem rootMultiplicity_X_sub_C_pow [Nontrivial R] (a : R) (n : ℕ) :
    rootMultiplicity a ((X - C a) ^ n) = n := by
  have := rootMultiplicity_mul_X_sub_C_pow (a := a) (n := n) C.map_one_ne_zero
  rwa [rootMultiplicity_C, map_one, one_mul, zero_add] at this

@[target] theorem rootMultiplicity_X_sub_C_self [Nontrivial R] {x : R} :
    rootMultiplicity x (X - C x) = 1 := by sorry

@[target] theorem rootMultiplicity_X_sub_C [Nontrivial R] [DecidableEq R] {x y : R} :
    rootMultiplicity x (X - C y) = if x = y then 1 else 0 := by
  sorry


@[target] theorem rootMultiplicity_mul {p q : R[X]} {x : R} (hpq : p * q ≠ 0) :
    rootMultiplicity x (p * q) = rootMultiplicity x p + rootMultiplicity x q := by
  sorry


theorem Monic.neg_one_pow_natDegree_mul_comp_neg_X {p : R[X]} (hp : p.Monic) :
    ((-1) ^ p.natDegree * p.comp (-X)).Monic := by
  simp only [Monic]
  calc
    ((-1) ^ p.natDegree * p.comp (-X)).leadingCoeff =
        (p.comp (-X) * C ((-1) ^ p.natDegree)).leadingCoeff := by
      simp [mul_comm]
    _ = 1 := by
      apply monic_mul_C_of_leadingCoeff_mul_eq_one
      simp [← pow_add, hp]

variable [IsDomain R] {p q : R[X]}

@[target] theorem degree_eq_degree_of_associated (h : Associated p q) : degree p = degree q := by
  sorry


@[target] theorem prime_X_sub_C (r : R) : Prime (X - C r) :=
  ⟨X_sub_C_ne_zero r, not_isUnit_X_sub_C r, fun _ _ => by
    sorry


@[target] theorem prime_X : Prime (X : R[X]) := by
  sorry


theorem Monic.prime_of_degree_eq_one (hp1 : degree p = 1) (hm : Monic p) : Prime p :=
  have : p = X - C (-p.coeff 0) := by simpa [hm.leadingCoeff] using eq_X_add_C_of_degree_eq_one hp1
  this.symm ▸ prime_X_sub_C _

@[target] theorem irreducible_X_sub_C (r : R) : Irreducible (X - C r) := by sorry


@[target] theorem irreducible_X : Irreducible (X : R[X]) := by sorry


theorem Monic.irreducible_of_degree_eq_one (hp1 : degree p = 1) (hm : Monic p) : Irreducible p :=
  (hm.prime_of_degree_eq_one hp1).irreducible

lemma aeval_ne_zero_of_isCoprime {R} [CommSemiring R] [Nontrivial S] [Semiring S] [Algebra R S]
    {p q : R[X]} (h : IsCoprime p q) (s : S) : aeval s p ≠ 0 ∨ aeval s q ≠ 0 := by
  by_contra! hpq
  rcases h with ⟨_, _, h⟩
  apply_fun aeval s at h
  simp only [map_add, map_mul, map_one, hpq.left, hpq.right, mul_zero, add_zero, zero_ne_one] at h

@[target] theorem isCoprime_X_sub_C_of_isUnit_sub {R} [CommRing R] {a b : R} (h : IsUnit (a - b)) :
    IsCoprime (X - C a) (X - C b) :=
  ⟨-C h.unit⁻¹.val, C h.unit⁻¹.val, by
    sorry


open scoped Function in -- required for scoped `on` notation
open scoped Function in -- required for scoped `on` notation
@[target] theorem pairwise_coprime_X_sub_C {K} [Field K] {I : Type v} {s : I → K} (H : Function.Injective s) :
    Pairwise (IsCoprime on fun i : I => X - C (s i)) := by sorry


theorem rootMultiplicity_mul {p q : R[X]} {x : R} (hpq : p * q ≠ 0) :
    rootMultiplicity x (p * q) = rootMultiplicity x p + rootMultiplicity x q := by
  classical
  have hp : p ≠ 0 := left_ne_zero_of_mul hpq
  have hq : q ≠ 0 := right_ne_zero_of_mul hpq
  rw [rootMultiplicity_eq_multiplicity (p * q), if_neg hpq, rootMultiplicity_eq_multiplicity p,
    if_neg hp, rootMultiplicity_eq_multiplicity q, if_neg hq,
    multiplicity_mul (prime_X_sub_C x) (finiteMultiplicity_X_sub_C _ hpq)]

open Multiset in
open Multiset in
@[target] theorem exists_multiset_roots [DecidableEq R] :
    ∀ {p : R[X]} (_ : p ≠ 0), ∃ s : Multiset R,
      (Multiset.card s : WithBot ℕ) ≤ degree p ∧ ∀ a, s.count a = rootMultiplicity a p
  | p, hp =>
    haveI := Classical.propDecidable (∃ x, IsRoot p x)
    if h : ∃ x, IsRoot p x then
      let ⟨x, hx⟩ := h
      have hpd : 0 < degree p := degree_pos_of_root hp hx
      have hd0 : p /ₘ (X - C x) ≠ 0 := fun h => by
        sorry


end CommRing

end Polynomial
