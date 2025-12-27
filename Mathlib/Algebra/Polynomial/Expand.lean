import VerifiedAgora.tagger
/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Expand a polynomial by a factor of p, so `∑ aₙ xⁿ` becomes `∑ aₙ xⁿᵖ`.

## Main definitions

* `Polynomial.expand R p f`: expand the polynomial `f` with coefficients in a
  commutative semiring `R` by a factor of p, so `expand R p (∑ aₙ xⁿ)` is `∑ aₙ xⁿᵖ`.
* `Polynomial.contract p f`: the opposite of `expand`, so it sends `∑ aₙ xⁿᵖ` to `∑ aₙ xⁿ`.

-/


universe u v w

open Polynomial

open Finset

namespace Polynomial

section CommSemiring

variable (R : Type u) [CommSemiring R] {S : Type v} [CommSemiring S] (p q : ℕ)

/-- Expand the polynomial by a factor of p, so `∑ aₙ xⁿ` becomes `∑ aₙ xⁿᵖ`. -/
noncomputable def expand : R[X] →ₐ[R] R[X] :=
  { (eval₂RingHom C (X ^ p) : R[X] →+* R[X]) with commutes' := fun _ => eval₂_C _ _ }

@[target] theorem coe_expand : (expand R p : R[X] → R[X]) = eval₂ C (X ^ p) := by sorry


variable {R}

@[target] theorem expand_eq_comp_X_pow {f : R[X]} : expand R p f = f.comp (X ^ p) := by sorry


@[target] theorem expand_eq_sum {f : R[X]} : expand R p f = f.sum fun e a => C a * (X ^ p) ^ e := by
  sorry


@[target] theorem expand_C (p : ℕ) (r : R) : expand p (C r : MvPolynomial σ R) = C r := by sorry


@[simp]
theorem expand_X : expand R p X = X ^ p :=
  eval₂_X _ _

@[target] theorem expand_monomial (p : ℕ) (d : σ →₀ ℕ) (r : R) :
    expand p (monomial d r) = C r * ∏ i ∈ d.support, (X i ^ p) ^ d i := by sorry


@[target] theorem expand_expand (f : R[X]) : expand R p (expand R q f) = expand R (p * q) f :=
  Polynomial.induction_on f (fun r => by sorry


@[target] theorem expand_mul (f : R[X]) : expand R (p * q) f = expand R p (expand R q f) := by sorry


@[target] theorem expand_zero (f : R[X]) : expand R 0 f = C (eval 1 f) := by sorry


@[simp]
theorem expand_one (f : R[X]) : expand R 1 f = f :=
  Polynomial.induction_on f (fun r => by rw [expand_C])
    (fun f g ihf ihg => by rw [map_add, ihf, ihg]) fun n r _ => by
    rw [map_mul, expand_C, map_pow, expand_X, pow_one]

theorem expand_pow (f : R[X]) : expand R (p ^ q) f = (expand R p)^[q] f :=
  Nat.recOn q (by rw [pow_zero, expand_one, Function.iterate_zero, id]) fun n ih => by
    rw [Function.iterate_succ_apply', pow_succ', expand_mul, ih]

@[target] theorem derivative_expand (f : R[X]) : Polynomial.derivative (expand R p f) =
    expand R p (Polynomial.derivative f) * (p * (X ^ (p - 1) : R[X])) := by
  sorry


@[target] theorem coeff_expand {p : ℕ} (hp : 0 < p) (f : R[X]) (n : ℕ) :
    (expand R p f).coeff n = if p ∣ n then f.coeff (n / p) else 0 := by
  sorry


@[target] theorem coeff_expand_mul {p : ℕ} (hp : 0 < p) (f : R[X]) (n : ℕ) :
    (expand R p f).coeff (n * p) = f.coeff n := by
  sorry


@[simp]
theorem coeff_expand_mul' {p : ℕ} (hp : 0 < p) (f : R[X]) (n : ℕ) :
    (expand R p f).coeff (p * n) = f.coeff n := by rw [mul_comm, coeff_expand_mul hp]

/-- Expansion is injective. -/
/-- Expansion is injective. -/
@[target] theorem expand_injective {n : ℕ} (hn : 0 < n) : Function.Injective (expand R n) := fun g g' H =>
  ext fun k => by sorry


@[target] theorem expand_inj {p : ℕ} (hp : 0 < p) {f g : R[X]} : expand R p f = expand R p g ↔ f = g := by sorry


@[target] theorem expand_eq_zero {p : ℕ} (hp : 0 < p) {f : R[X]} : expand R p f = 0 ↔ f = 0 := by sorry


@[target] theorem expand_ne_zero {p : ℕ} (hp : 0 < p) {f : R[X]} : expand R p f ≠ 0 ↔ f ≠ 0 := by sorry


@[target] theorem expand_eq_C {p : ℕ} (hp : 0 < p) {f : R[X]} {r : R} : expand R p f = C r ↔ f = C r := by
  sorry


@[target] theorem natDegree_expand (p : ℕ) (f : R[X]) : (expand R p f).natDegree = f.natDegree * p := by
  sorry


@[target] theorem leadingCoeff_expand {p : ℕ} {f : R[X]} (hp : 0 < p) :
    (expand R p f).leadingCoeff = f.leadingCoeff := by
  sorry


@[target] theorem monic_expand_iff {p : ℕ} {f : R[X]} (hp : 0 < p) : (expand R p f).Monic ↔ f.Monic := by
  sorry


@[target] theorem map_expand (f : R →+* S) (p : ℕ) (φ : MvPolynomial σ R) :
    map f (expand p φ) = expand p (map f φ) := by sorry


@[target] theorem expand_eval (p : ℕ) (P : R[X]) (r : R) : eval r (expand R p P) = eval (r ^ p) P := by
  sorry


@[target] theorem expand_aeval {A : Type*} [Semiring A] [Algebra R A] (p : ℕ) (P : R[X]) (r : A) :
    aeval r (expand R p P) = aeval (r ^ p) P := by
  sorry


/-- The opposite of `expand`: sends `∑ aₙ xⁿᵖ` to `∑ aₙ xⁿ`. -/
noncomputable def contract (p : ℕ) (f : R[X]) : R[X] :=
  ∑ n ∈ range (f.natDegree + 1), monomial n (f.coeff (n * p))

theorem coeff_contract {p : ℕ} (hp : p ≠ 0) (f : R[X]) (n : ℕ) :
    (contract p f).coeff n = f.coeff (n * p) := by
  simp only [contract, coeff_monomial, sum_ite_eq', finset_sum_coeff, mem_range, not_lt,
    ite_eq_left_iff]
  intro hn
  apply (coeff_eq_zero_of_natDegree_lt _).symm
  calc
    f.natDegree < f.natDegree + 1 := Nat.lt_succ_self _
    _ ≤ n * 1 := by simpa only [mul_one] using hn
    _ ≤ n * p := mul_le_mul_of_nonneg_left (show 1 ≤ p from hp.bot_lt) (zero_le n)

theorem map_contract {p : ℕ} (hp : p ≠ 0) {f : R →+* S} {q : R[X]} :
    (q.contract p).map f = (q.map f).contract p := ext fun n ↦ by
  simp only [coeff_map, coeff_contract hp]

theorem contract_expand {f : R[X]} (hp : p ≠ 0) : contract p (expand R p f) = f := by
  ext
  simp [coeff_contract hp, coeff_expand hp.bot_lt, Nat.mul_div_cancel _ hp.bot_lt]

@[target] theorem contract_one {f : R[X]} : contract 1 f = f :=
  ext fun n ↦ by sorry


@[simp] theorem contract_C (r : R) : contract p (C r) = C r := by simp [contract]

@[target] theorem contract_add {p : ℕ} (hp : p ≠ 0) (f g : R[X]) :
    contract p (f + g) = contract p f + contract p g := by
  sorry


@[target] theorem contract_mul_expand {p : ℕ} (hp : p ≠ 0) (f g : R[X]) :
    contract p (f * expand R p g) = contract p f * g := by
  sorry


@[target] theorem isCoprime_expand {f g : R[X]} {p : ℕ} (hp : p ≠ 0) :
    IsCoprime (expand R p f) (expand R p g) ↔ IsCoprime f g :=
  ⟨fun ⟨a, b, eq⟩ ↦ ⟨contract p a, contract p b, by
    sorry


section ExpChar

@[target] theorem expand_contract [CharP R p] [NoZeroDivisors R] {f : R[X]} (hf : Polynomial.derivative f = 0)
    (hp : p ≠ 0) : expand R p (contract p f) = f := by
  sorry


variable [ExpChar R p]

theorem expand_contract' [NoZeroDivisors R] {f : R[X]} (hf : Polynomial.derivative f = 0) :
    expand R p (contract p f) = f := by
  obtain _ | @⟨_, hprime, hchar⟩ := ‹ExpChar R p›
  · rw [expand_one, contract_one]
  · haveI := Fact.mk hchar; exact expand_contract p hf hprime.ne_zero

@[target] theorem expand_char (f : R[X]) : map (frobenius R p) (expand R p f) = f ^ p := by
  sorry


@[target] theorem map_expand_pow_char (f : R[X]) (n : ℕ) :
    map (frobenius R p ^ n) (expand R (p ^ n) f) = f ^ p ^ n := by
  sorry


end ExpChar

end CommSemiring

section rootMultiplicity

variable {R : Type u} [CommRing R] {p n : ℕ} [ExpChar R p] {f : R[X]} {r : R}

@[target] theorem rootMultiplicity_expand_pow :
    (expand R (p ^ n) f).rootMultiplicity r = p ^ n * f.rootMultiplicity (r ^ p ^ n) := by
  sorry


theorem rootMultiplicity_expand :
    (expand R p f).rootMultiplicity r = p * f.rootMultiplicity (r ^ p) := by
  rw [← pow_one p, rootMultiplicity_expand_pow]

end rootMultiplicity

section IsDomain

variable (R : Type u) [CommRing R] [IsDomain R]

theorem isLocalHom_expand {p : ℕ} (hp : 0 < p) : IsLocalHom (expand R p) := by
  refine ⟨fun f hf1 => ?_⟩
  have hf2 := eq_C_of_degree_eq_zero (degree_eq_zero_of_isUnit hf1)
  rw [coeff_expand hp, if_pos (dvd_zero _), p.zero_div] at hf2
  rw [hf2, isUnit_C] at hf1; rw [expand_eq_C hp] at hf2; rwa [hf2, isUnit_C]

@[deprecated (since := "2024-10-10")]
alias isLocalRingHom_expand := isLocalHom_expand

variable {R}

@[target] theorem of_irreducible_expand {p : ℕ} (hp : p ≠ 0) {f : R[X]} (hf : Irreducible (expand R p f)) :
    Irreducible f := by sorry


@[target] theorem of_irreducible_expand_pow {p : ℕ} (hp : p ≠ 0) {f : R[X]} {n : ℕ} :
    Irreducible (expand R (p ^ n) f) → Irreducible f :=
  Nat.recOn n (fun hf => by sorry


end IsDomain

end Polynomial
