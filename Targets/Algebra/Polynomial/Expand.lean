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

theorem coe_expand : (expand R p : R[X] → R[X]) = eval₂ C (X ^ p) :=
  rfl

variable {R}

@[target]
theorem expand_eq_comp_X_pow {f : R[X]} : expand R p f = f.comp (X ^ p) := sorry

@[target]
theorem expand_eq_sum {f : R[X]} : expand R p f = f.sum fun e a => C a * (X ^ p) ^ e := by sorry

@[target, simp]
theorem expand_C (r : R) : expand R p (C r) = C r :=
  sorry

@[target, simp]
theorem expand_X : expand R p X = X ^ p :=
  sorry

@[simp]
theorem expand_monomial (r : R) : expand R p (monomial q r) = monomial (q * p) r := by
  simp_rw [← smul_X_eq_monomial, map_smul, map_pow, expand_X, mul_comm, pow_mul]

@[target]
theorem expand_expand (f : R[X]) : expand R p (expand R q f) = expand R (p * q) f :=
  sorry

theorem expand_mul (f : R[X]) : expand R (p * q) f = expand R p (expand R q f) :=
  (expand_expand p q f).symm

@[target, simp]
theorem expand_zero (f : R[X]) : expand R 0 f = C (eval 1 f) := by sorry

@[target, simp]
theorem expand_one (f : R[X]) : expand R 1 f = f :=
  sorry

@[target]
theorem expand_pow (f : R[X]) : expand R (p ^ q) f = (expand R p)^[q] f :=
  sorry

@[target]
theorem derivative_expand (f : R[X]) : Polynomial.derivative (expand R p f) =
    expand R p (Polynomial.derivative f) * (p * (X ^ (p - 1) : R[X])) := by sorry

@[target]
theorem coeff_expand {p : ℕ} (hp : 0 < p) (f : R[X]) (n : ℕ) :
    (expand R p f).coeff n = if p ∣ n then f.coeff (n / p) else 0 := by sorry

@[simp]
theorem coeff_expand_mul {p : ℕ} (hp : 0 < p) (f : R[X]) (n : ℕ) :
    (expand R p f).coeff (n * p) = f.coeff n := by
  rw [coeff_expand hp, if_pos (dvd_mul_left _ _), Nat.mul_div_cancel _ hp]

@[target, simp]
theorem coeff_expand_mul' {p : ℕ} (hp : 0 < p) (f : R[X]) (n : ℕ) :
    (expand R p f).coeff (p * n) = f.coeff n := by sorry
@[target]
theorem expand_injective {n : ℕ} (hn : 0 < n) : Function.Injective (expand R n) := sorry

@[target]
theorem expand_inj {p : ℕ} (hp : 0 < p) {f g : R[X]} : expand R p f = expand R p g ↔ f = g :=
  sorry

theorem expand_eq_zero {p : ℕ} (hp : 0 < p) {f : R[X]} : expand R p f = 0 ↔ f = 0 :=
  (expand_injective hp).eq_iff' (map_zero _)

@[target]
theorem expand_ne_zero {p : ℕ} (hp : 0 < p) {f : R[X]} : expand R p f ≠ 0 ↔ f ≠ 0 :=
  sorry

theorem expand_eq_C {p : ℕ} (hp : 0 < p) {f : R[X]} {r : R} : expand R p f = C r ↔ f = C r := by
  rw [← expand_C, expand_inj hp, expand_C]

@[target]
theorem natDegree_expand (p : ℕ) (f : R[X]) : (expand R p f).natDegree = f.natDegree * p := by sorry

@[target]
theorem leadingCoeff_expand {p : ℕ} {f : R[X]} (hp : 0 < p) :
    (expand R p f).leadingCoeff = f.leadingCoeff := by sorry

@[target]
theorem monic_expand_iff {p : ℕ} {f : R[X]} (hp : 0 < p) : (expand R p f).Monic ↔ f.Monic := by sorry

@[target]
theorem map_expand {p : ℕ} {f : R →+* S} {q : R[X]} :
    map f (expand R p q) = expand S p (map f q) := by sorry

@[simp]
theorem expand_eval (p : ℕ) (P : R[X]) (r : R) : eval r (expand R p P) = eval (r ^ p) P := by
  refine Polynomial.induction_on P (fun a => by simp) (fun f g hf hg => ?_) fun n a _ => by simp
  rw [map_add, eval_add, eval_add, hf, hg]

@[target, simp]
theorem expand_aeval {A : Type*} [Semiring A] [Algebra R A] (p : ℕ) (P : R[X]) (r : A) :
    aeval r (expand R p P) = aeval (r ^ p) P := by sorry

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

@[target]
theorem contract_expand {f : R[X]} (hp : p ≠ 0) : contract p (expand R p f) = f := by sorry

theorem contract_one {f : R[X]} : contract 1 f = f :=
  ext fun n ↦ by rw [coeff_contract one_ne_zero, mul_one]

@[simp] theorem contract_C (r : R) : contract p (C r) = C r := by simp [contract]

@[target]
theorem contract_add {p : ℕ} (hp : p ≠ 0) (f g : R[X]) :
    contract p (f + g) = contract p f + contract p g := by sorry

@[target]
theorem contract_mul_expand {p : ℕ} (hp : p ≠ 0) (f g : R[X]) :
    contract p (f * expand R p g) = contract p f * g := by sorry

@[simp] theorem isCoprime_expand {f g : R[X]} {p : ℕ} (hp : p ≠ 0) :
    IsCoprime (expand R p f) (expand R p g) ↔ IsCoprime f g :=
  ⟨fun ⟨a, b, eq⟩ ↦ ⟨contract p a, contract p b, by
    simp_rw [← contract_mul_expand hp, ← contract_add hp, eq, ← C_1, contract_C]⟩, (·.map _)⟩

section ExpChar

theorem expand_contract [CharP R p] [NoZeroDivisors R] {f : R[X]} (hf : Polynomial.derivative f = 0)
    (hp : p ≠ 0) : expand R p (contract p f) = f := by
  ext n
  rw [coeff_expand hp.bot_lt, coeff_contract hp]
  split_ifs with h
  · rw [Nat.div_mul_cancel h]
  · rcases n with - | n
    · exact absurd (dvd_zero p) h
    have := coeff_derivative f n
    rw [hf, coeff_zero, zero_eq_mul] at this
    rcases this with h' | _
    · rw [h']
    rename_i _ _ _ h'
    rw [← Nat.cast_succ, CharP.cast_eq_zero_iff R p] at h'
    exact absurd h' h

variable [ExpChar R p]

@[target]
theorem expand_contract' [NoZeroDivisors R] {f : R[X]} (hf : Polynomial.derivative f = 0) :
    expand R p (contract p f) = f := by sorry

@[target]
theorem expand_char (f : R[X]) : map (frobenius R p) (expand R p f) = f ^ p := by sorry

@[target]
theorem map_expand_pow_char (f : R[X]) (n : ℕ) :
    map (frobenius R p ^ n) (expand R (p ^ n) f) = f ^ p ^ n := by sorry

end ExpChar

end CommSemiring

section rootMultiplicity

variable {R : Type u} [CommRing R] {p n : ℕ} [ExpChar R p] {f : R[X]} {r : R}

theorem rootMultiplicity_expand_pow :
    (expand R (p ^ n) f).rootMultiplicity r = p ^ n * f.rootMultiplicity (r ^ p ^ n) := by
  obtain rfl | h0 := eq_or_ne f 0; · simp
  obtain ⟨g, hg, ndvd⟩ := f.exists_eq_pow_rootMultiplicity_mul_and_not_dvd h0 (r ^ p ^ n)
  rw [dvd_iff_isRoot, ← eval_X (x := r), ← eval_pow, ← isRoot_comp, ← expand_eq_comp_X_pow] at ndvd
  conv_lhs => rw [hg, map_mul, map_pow, map_sub, expand_X, expand_C, map_pow, ← sub_pow_expChar_pow,
    ← pow_mul, mul_comm, rootMultiplicity_mul_X_sub_C_pow (expand_ne_zero (expChar_pow_pos R p n)
      |>.mpr <| right_ne_zero_of_mul <| hg ▸ h0), rootMultiplicity_eq_zero ndvd, zero_add]

theorem rootMultiplicity_expand :
    (expand R p f).rootMultiplicity r = p * f.rootMultiplicity (r ^ p) := by
  rw [← pow_one p, rootMultiplicity_expand_pow]

end rootMultiplicity

section IsDomain

variable (R : Type u) [CommRing R] [IsDomain R]

@[target]
theorem isLocalHom_expand {p : ℕ} (hp : 0 < p) : IsLocalHom (expand R p) := by sorry

@[deprecated (since := "2024-10-10")]
alias isLocalRingHom_expand := isLocalHom_expand

variable {R}

@[target]
theorem of_irreducible_expand {p : ℕ} (hp : p ≠ 0) {f : R[X]} (hf : Irreducible (expand R p f)) :
    Irreducible f :=
  sorry

theorem of_irreducible_expand_pow {p : ℕ} (hp : p ≠ 0) {f : R[X]} {n : ℕ} :
    Irreducible (expand R (p ^ n) f) → Irreducible f :=
  Nat.recOn n (fun hf => by rwa [pow_zero, expand_one] at hf) fun n ih hf =>
    ih <| of_irreducible_expand hp <| by
      rw [pow_succ'] at hf
      rwa [expand_expand]

end IsDomain

end Polynomial
