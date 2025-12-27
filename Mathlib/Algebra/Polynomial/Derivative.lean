import VerifiedAgora.tagger
/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.GroupTheory.GroupAction.Ring

/-!
# The derivative map on polynomials

## Main definitions
 * `Polynomial.derivative`: The formal derivative of polynomials, expressed as a linear map.
 * `Polynomial.derivativeFinsupp`: Iterated derivatives as a finite support function.

-/


noncomputable section

open Finset

open Polynomial

open scoped Nat

namespace Polynomial

universe u v w y z

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

section Derivative

section Semiring

variable [Semiring R]

/-- `derivative p` is the formal derivative of the polynomial `p` -/
/-- `derivative p` is the formal derivative of the polynomial `p` -/
def derivative : R[X] →ₗ[R] R[X] where
  toFun p := p.sum fun n a => C (a * n) * X ^ (n - 1)
  map_add' p q := by
    sorry


theorem derivative_apply (p : R[X]) : derivative p = p.sum fun n a => C (a * n) * X ^ (n - 1) :=
  rfl

theorem coeff_derivative (p : R[X]) (n : ℕ) :
    coeff (derivative p) n = coeff p (n + 1) * (n + 1) := by
  rw [derivative_apply]
  simp only [coeff_X_pow, coeff_sum, coeff_C_mul]
  rw [sum, Finset.sum_eq_single (n + 1)]
  · simp only [Nat.add_succ_sub_one, add_zero, mul_one, if_true, eq_self_iff_true]; norm_cast
  · intro b
    cases b
    · intros
      rw [Nat.cast_zero, mul_zero, zero_mul]
    · intro _ H
      rw [Nat.add_one_sub_one, if_neg (mt (congr_arg Nat.succ) H.symm), mul_zero]
  · rw [if_pos (add_tsub_cancel_right n 1).symm, mul_one, Nat.cast_add, Nat.cast_one,
      mem_support_iff]
    intro h
    push_neg at h
    simp [h]

@[target] theorem derivative_zero : derivative (0 : R[X]) = 0 := by sorry


@[target] theorem iterate_derivative_zero {k : ℕ} : derivative^[k] (0 : R[X]) = 0 := by sorry


@[target] theorem derivative_monomial (a : R) (n : ℕ) :
    derivative (monomial n a) = monomial (n - 1) (a * n) := by
  sorry


@[simp]
theorem derivative_monomial_succ (a : R) (n : ℕ) :
    derivative (monomial (n + 1) a) = monomial n (a * (n + 1)) := by
  rw [derivative_monomial, add_tsub_cancel_right, Nat.cast_add, Nat.cast_one]

@[target] theorem derivative_C_mul_X (a : R) : derivative (C a * X) = C a := by
  sorry


theorem derivative_C_mul_X_pow (a : R) (n : ℕ) :
    derivative (C a * X ^ n) = C (a * n) * X ^ (n - 1) := by
  rw [C_mul_X_pow_eq_monomial, C_mul_X_pow_eq_monomial, derivative_monomial]

@[target] theorem derivative_C_mul_X_sq (a : R) : derivative (C a * X ^ 2) = C (a * 2) * X := by
  sorry


theorem derivative_X_pow (n : ℕ) : derivative (X ^ n : R[X]) = C (n : R) * X ^ (n - 1) := by
  convert derivative_C_mul_X_pow (1 : R) n <;> simp

@[target] theorem derivative_X_pow_succ (n : ℕ) :
    derivative (X ^ (n + 1) : R[X]) = C (n + 1 : R) * X ^ n := by
  sorry


@[target] theorem derivative_X_sq : derivative (X ^ 2 : R[X]) = C 2 * X := by
  sorry


@[target] theorem derivative_C {a : R} : derivative (C a) = 0 := by sorry


@[target] theorem derivative_of_natDegree_zero {p : R[X]} (hp : p.natDegree = 0) : derivative p = 0 := by
  sorry


@[target] theorem derivative_X : derivative (X : R[X]) = 1 :=
  (derivative_monomial _ _).trans <| by sorry


@[simp]
theorem derivative_one : derivative (1 : R[X]) = 0 :=
  derivative_C

@[target] theorem derivative_add {f g : R[X]} : derivative (f + g) = derivative f + derivative g := by sorry


@[target] theorem derivative_X_add_C (c : R) : derivative (X + C c) = 1 := by
  sorry


@[target] theorem derivative_sum {s : Finset ι} {f : ι → R[X]} :
    derivative (∑ b ∈ s, f b) = ∑ b ∈ s, derivative (f b) := by sorry


@[target] theorem iterate_derivative_sum (k : ℕ) (s : Finset ι) (f : ι → R[X]) :
    derivative^[k] (∑ b ∈ s, f b) = ∑ b ∈ s, derivative^[k] (f b) := by
  sorry


@[target] theorem derivative_smul {S : Type*} [Monoid S] [DistribMulAction S R] [IsScalarTower S R R] (s : S)
    (p : R[X]) : derivative (s • p) = s • derivative p := by sorry


@[target] theorem iterate_derivative_smul {S : Type*} [Monoid S] [DistribMulAction S R] [IsScalarTower S R R]
    (s : S) (p : R[X]) (k : ℕ) : derivative^[k] (s • p) = s • derivative^[k] p := by
  sorry


@[target] theorem iterate_derivative_C_mul (a : R) (p : R[X]) (k : ℕ) :
    derivative^[k] (C a * p) = C a * derivative^[k] p := by
  sorry


@[target] theorem derivative_C_mul (a : R) (p : R[X]) :
    derivative (C a * p) = C a * derivative p := by sorry


@[target] theorem of_mem_support_derivative {p : R[X]} {n : ℕ} (h : n ∈ p.derivative.support) :
    n + 1 ∈ p.support :=
  mem_support_iff.2 fun h1 : p.coeff (n + 1) = 0 =>
    mem_support_iff.1 h <| show p.derivative.coeff n = 0 by sorry


@[target] theorem degree_derivative_lt {p : R[X]} (hp : p ≠ 0) : p.derivative.degree < p.degree := by sorry


@[target] theorem degree_derivative_le {p : R[X]} : p.derivative.degree ≤ p.degree :=
  letI := Classical.decEq R
  if H : p = 0 then le_of_eq <| by sorry


@[target] theorem natDegree_derivative_lt {p : R[X]} (hp : p.natDegree ≠ 0) :
    p.derivative.natDegree < p.natDegree := by
  sorry


@[target] theorem natDegree_derivative_le (p : R[X]) : p.derivative.natDegree ≤ p.natDegree - 1 := by
  sorry


@[target] theorem natDegree_iterate_derivative (p : R[X]) (k : ℕ) :
    (derivative^[k] p).natDegree ≤ p.natDegree - k := by
  sorry


@[target] theorem derivative_natCast {n : ℕ} : derivative (n : R[X]) = 0 := by
  sorry


@[target] theorem derivative_ofNat (n : ℕ) [n.AtLeastTwo] :
    derivative (ofNat(n) : R[X]) = 0 := by sorry


@[target] theorem iterate_derivative_eq_zero {p : R[X]} {x : ℕ} (hx : p.natDegree < x) :
    Polynomial.derivative^[x] p = 0 := by
  sorry


@[target] theorem iterate_derivative_C {k} (h : 0 < k) : derivative^[k] (C a : R[X]) = 0 := by sorry


@[simp]
theorem iterate_derivative_one {k} (h : 0 < k) : derivative^[k] (1 : R[X]) = 0 :=
  iterate_derivative_C h

@[simp]
theorem iterate_derivative_X {k} (h : 1 < k) : derivative^[k] (X : R[X]) = 0 :=
  iterate_derivative_eq_zero <| natDegree_X_le.trans_lt h

@[target] theorem natDegree_eq_zero_of_derivative_eq_zero [NoZeroSMulDivisors ℕ R] {f : R[X]}
    (h : derivative f = 0) : f.natDegree = 0 := by
  sorry


theorem eq_C_of_derivative_eq_zero [NoZeroSMulDivisors ℕ R] {f : R[X]} (h : derivative f = 0) :
    f = C (f.coeff 0) :=
  eq_C_of_natDegree_eq_zero <| natDegree_eq_zero_of_derivative_eq_zero h

@[target] theorem derivative_mul {f g : R[X]} : derivative (f * g) = derivative f * g + f * derivative g := by
  sorry


@[target] theorem derivative_eval (p : R[X]) (x : R) :
    p.derivative.eval x = p.sum fun n a => a * n * x ^ (n - 1) := by
  sorry


@[target] theorem derivative_map [Semiring S] (p : R[X]) (f : R →+* S) :
    derivative (p.map f) = p.derivative.map f := by
  sorry


@[target] theorem iterate_derivative_map [Semiring S] (p : R[X]) (f : R →+* S) (k : ℕ) :
    Polynomial.derivative^[k] (p.map f) = (Polynomial.derivative^[k] p).map f := by
  sorry


@[target] theorem derivative_natCast_mul {n : ℕ} {f : R[X]} :
    derivative ((n : R[X]) * f) = n * derivative f := by
  sorry


@[target] theorem iterate_derivative_natCast_mul {n k : ℕ} {f : R[X]} :
    derivative^[k] ((n : R[X]) * f) = n * derivative^[k] f := by
  sorry


@[target] theorem mem_support_derivative [NoZeroSMulDivisors ℕ R] (p : R[X]) (n : ℕ) :
    n ∈ (derivative p).support ↔ n + 1 ∈ p.support := by
  sorry


@[simp]
theorem degree_derivative_eq [NoZeroSMulDivisors ℕ R] (p : R[X]) (hp : 0 < natDegree p) :
    degree (derivative p) = (natDegree p - 1 : ℕ) := by
  apply le_antisymm
  · rw [derivative_apply]
    apply le_trans (degree_sum_le _ _) (Finset.sup_le _)
    intro n hn
    apply le_trans (degree_C_mul_X_pow_le _ _) (WithBot.coe_le_coe.2 (tsub_le_tsub_right _ _))
    apply le_natDegree_of_mem_supp _ hn
  · refine le_sup ?_
    rw [mem_support_derivative, tsub_add_cancel_of_le, mem_support_iff]
    · rw [coeff_natDegree, Ne, leadingCoeff_eq_zero]
      intro h
      rw [h, natDegree_zero] at hp
      exact hp.false
    exact hp

theorem coeff_iterate_derivative {k} (p : R[X]) (m : ℕ) :
    (derivative^[k] p).coeff m = (m + k).descFactorial k • p.coeff (m + k) := by
  induction k generalizing m with
  | zero => simp
  | succ k ih =>
      calc
        (derivative^[k + 1] p).coeff m
        _ = Nat.descFactorial (Nat.succ (m + k)) k • p.coeff (m + k.succ) * (m + 1) := by
          rw [Function.iterate_succ_apply', coeff_derivative, ih m.succ, Nat.succ_add, Nat.add_succ]
        _ = ((m + 1) * Nat.descFactorial (Nat.succ (m + k)) k) • p.coeff (m + k.succ) := by
          rw [← Nat.cast_add_one, ← nsmul_eq_mul', smul_smul]
        _ = Nat.descFactorial (m.succ + k) k.succ • p.coeff (m + k.succ) := by
          rw [← Nat.succ_add, Nat.descFactorial_succ, add_tsub_cancel_right]
        _ = Nat.descFactorial (m + k.succ) k.succ • p.coeff (m + k.succ) := by
          rw [Nat.succ_add_eq_add_succ]

@[target] theorem iterate_derivative_eq_sum (p : R[X]) (k : ℕ) :
    derivative^[k] p =
      ∑ x ∈ (derivative^[k] p).support, C ((x + k).descFactorial k • p.coeff (x + k)) * X ^ x := by
  sorry


theorem iterate_derivative_eq_factorial_smul_sum (p : R[X]) (k : ℕ) :
    derivative^[k] p = k ! •
      ∑ x ∈ (derivative^[k] p).support, C ((x + k).choose k • p.coeff (x + k)) * X ^ x := by
  conv_lhs => rw [iterate_derivative_eq_sum]
  rw [smul_sum]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [← smul_mul_assoc, smul_C, smul_smul, Nat.descFactorial_eq_factorial_mul_choose]

@[target] theorem iterate_derivative_mul {n} (p q : R[X]) :
    derivative^[n] (p * q) =
      ∑ k ∈ range n.succ, (n.choose k • (derivative^[n - k] p * derivative^[k] q)) := by
  sorry


/--
Iterated derivatives as a finite support function.
-/
@[simps! apply_toFun]
noncomputable def derivativeFinsupp : R[X] →ₗ[R] ℕ →₀ R[X] where
  toFun p := .onFinset (range (p.natDegree + 1)) (derivative^[·] p) fun i ↦ by
    contrapose; simp_all [iterate_derivative_eq_zero, Nat.succ_le]
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

@[simp]
theorem support_derivativeFinsupp_subset_range {p : R[X]} {n : ℕ} (h : p.natDegree < n) :
    (derivativeFinsupp p).support ⊆ range n := by
  dsimp [derivativeFinsupp]
  exact Finsupp.support_onFinset_subset.trans (Finset.range_subset.mpr h)

@[simp]
theorem derivativeFinsupp_C (r : R) : derivativeFinsupp (C r : R[X]) = .single 0 (C r) := by
  ext i : 1
  match i with
  | 0 => simp
  | i + 1 => simp

@[simp]
theorem derivativeFinsupp_one : derivativeFinsupp (1 : R[X]) = .single 0 1 := by
  simpa using derivativeFinsupp_C (1 : R)

@[target] theorem derivativeFinsupp_X : derivativeFinsupp (X : R[X]) = .single 0 X + .single 1 1 := by
  sorry


theorem derivativeFinsupp_map [Semiring S] (p : R[X]) (f : R →+* S) :
    derivativeFinsupp (p.map f) = (derivativeFinsupp p).mapRange (·.map f) (by simp) := by
  ext i : 1
  simp

@[target] theorem derivativeFinsupp_derivative (p : R[X]) :
    derivativeFinsupp (derivative p) =
      (derivativeFinsupp p).comapDomain Nat.succ Nat.succ_injective.injOn := by
  sorry


end Semiring

section CommSemiring

variable [CommSemiring R]

@[target] theorem derivative_pow_succ (p : R[X]) (n : ℕ) :
    derivative (p ^ (n + 1)) = C (n + 1 : R) * p ^ n * derivative p :=
  Nat.recOn n (by sorry


theorem derivative_pow (p : R[X]) (n : ℕ) :
    derivative (p ^ n) = C (n : R) * p ^ (n - 1) * derivative p :=
  Nat.casesOn n (by rw [pow_zero, derivative_one, Nat.cast_zero, C_0, zero_mul, zero_mul]) fun n =>
    by rw [p.derivative_pow_succ n, Nat.add_one_sub_one, n.cast_succ]

theorem derivative_sq (p : R[X]) : derivative (p ^ 2) = C 2 * p * derivative p := by
  rw [derivative_pow_succ, Nat.cast_one, one_add_one_eq_two, pow_one]

@[target] theorem pow_sub_one_dvd_derivative_of_pow_dvd {p q : R[X]} {n : ℕ}
    (dvd : q ^ n ∣ p) : q ^ (n - 1) ∣ derivative p := by
  sorry


@[target] theorem pow_sub_dvd_iterate_derivative_of_pow_dvd {p q : R[X]} {n : ℕ} (m : ℕ)
    (dvd : q ^ n ∣ p) : q ^ (n - m) ∣ derivative^[m] p := by
  sorry


theorem pow_sub_dvd_iterate_derivative_pow (p : R[X]) (n m : ℕ) :
    p ^ (n - m) ∣ derivative^[m] (p ^ n) := pow_sub_dvd_iterate_derivative_of_pow_dvd m dvd_rfl

@[target] theorem dvd_iterate_derivative_pow (f : R[X]) (n : ℕ) {m : ℕ} (c : R) (hm : m ≠ 0) :
    (n : R) ∣ eval c (derivative^[m] (f ^ n)) := by
  sorry


@[target] theorem iterate_derivative_X_pow_eq_natCast_mul (n k : ℕ) :
    derivative^[k] (X ^ n : R[X]) = ↑(Nat.descFactorial n k : R[X]) * X ^ (n - k) := by
  sorry


@[target] theorem iterate_derivative_X_pow_eq_C_mul (n k : ℕ) :
    derivative^[k] (X ^ n : R[X]) = C (Nat.descFactorial n k : R) * X ^ (n - k) := by
  sorry


theorem iterate_derivative_X_pow_eq_smul (n : ℕ) (k : ℕ) :
    derivative^[k] (X ^ n : R[X]) = (Nat.descFactorial n k : R) • X ^ (n - k) := by
  rw [iterate_derivative_X_pow_eq_C_mul n k, smul_eq_C_mul]

@[target] theorem derivative_X_add_C_pow (c : R) (m : ℕ) :
    derivative ((X + C c) ^ m) = C (m : R) * (X + C c) ^ (m - 1) := by
  sorry


@[target] theorem derivative_X_add_C_sq (c : R) : derivative ((X + C c) ^ 2) = C 2 * (X + C c) := by
  sorry


theorem iterate_derivative_X_add_pow (n k : ℕ) (c : R) :
    derivative^[k] ((X + C c) ^ n) = Nat.descFactorial n k • (X + C c) ^ (n - k) := by
  induction k with
  | zero => simp
  | succ k IH =>
      rw [Nat.sub_succ', Function.iterate_succ_apply', IH, derivative_smul,
        derivative_X_add_C_pow, map_natCast, Nat.descFactorial_succ, nsmul_eq_mul, nsmul_eq_mul,
        Nat.cast_mul]
      ring

@[target] theorem derivative_comp (p q : R[X]) :
    derivative (p.comp q) = derivative q * p.derivative.comp q := by
  sorry


/-- Chain rule for formal derivative of polynomials. -/
theorem derivative_eval₂_C (p q : R[X]) :
    derivative (p.eval₂ C q) = p.derivative.eval₂ C q * derivative q :=
  Polynomial.induction_on p (fun r => by rw [eval₂_C, derivative_C, eval₂_zero, zero_mul])
    (fun p₁ p₂ ih₁ ih₂ => by
      rw [eval₂_add, derivative_add, ih₁, ih₂, derivative_add, eval₂_add, add_mul])
    fun n r ih => by
    rw [pow_succ, ← mul_assoc, eval₂_mul, eval₂_X, derivative_mul, ih, @derivative_mul _ _ _ X,
      derivative_X, mul_one, eval₂_add, @eval₂_mul _ _ _ _ X, eval₂_X, add_mul, mul_right_comm]

@[target] theorem derivative_prod [DecidableEq ι] {s : Multiset ι} {f : ι → R[X]} :
    derivative (Multiset.map f s).prod =
      (Multiset.map (fun i => (Multiset.map f (s.erase i)).prod * derivative (f i)) s).sum := by
  sorry


end CommSemiring

section Ring

variable [Ring R]

@[simp]
theorem derivative_neg (f : R[X]) : derivative (-f) = -derivative f :=
  LinearMap.map_neg derivative f

theorem iterate_derivative_neg {f : R[X]} {k : ℕ} : derivative^[k] (-f) = -derivative^[k] f :=
  iterate_map_neg derivative k f

@[target] theorem derivative_sub {f g : R[X]} : derivative (f - g) = derivative f - derivative g := by sorry


@[target] theorem derivative_X_sub_C (c : R) : derivative (X - C c) = 1 := by
  sorry


@[target] theorem iterate_derivative_sub {k : ℕ} {f g : R[X]} :
    derivative^[k] (f - g) = derivative^[k] f - derivative^[k] g := by sorry


@[target] theorem derivative_intCast {n : ℤ} : derivative (n : R[X]) = 0 := by
  sorry


theorem derivative_intCast_mul {n : ℤ} {f : R[X]} : derivative ((n : R[X]) * f) =
    n * derivative f := by
  simp

@[target] theorem iterate_derivative_intCast_mul {n : ℤ} {k : ℕ} {f : R[X]} :
    derivative^[k] ((n : R[X]) * f) = n * derivative^[k] f := by
  sorry


end Ring

section CommRing

variable [CommRing R]

@[target] theorem derivative_comp_one_sub_X (p : R[X]) :
    derivative (p.comp (1 - X)) = -p.derivative.comp (1 - X) := by sorry


@[simp]
theorem iterate_derivative_comp_one_sub_X (p : R[X]) (k : ℕ) :
    derivative^[k] (p.comp (1 - X)) = (-1) ^ k * (derivative^[k] p).comp (1 - X) := by
  induction' k with k ih generalizing p
  · simp
  · simp [ih (derivative p), iterate_derivative_neg, derivative_comp, pow_succ]

@[target] theorem eval_multiset_prod_X_sub_C_derivative [DecidableEq R]
    {S : Multiset R} {r : R} (hr : r ∈ S) :
    eval r (derivative (Multiset.map (fun a => X - C a) S).prod) =
      (Multiset.map (fun a => r - a) (S.erase r)).prod := by
  sorry


theorem derivative_X_sub_C_pow (c : R) (m : ℕ) :
    derivative ((X - C c) ^ m) = C (m : R) * (X - C c) ^ (m - 1) := by
  rw [derivative_pow, derivative_X_sub_C, mul_one]

@[target] theorem derivative_X_sub_C_sq (c : R) : derivative ((X - C c) ^ 2) = C 2 * (X - C c) := by
  sorry


theorem iterate_derivative_X_sub_pow (n k : ℕ) (c : R) :
    derivative^[k] ((X - C c) ^ n) = n.descFactorial k • (X - C c) ^ (n - k) := by
  rw [sub_eq_add_neg, ← C_neg, iterate_derivative_X_add_pow]

@[target] theorem iterate_derivative_X_sub_pow_self (n : ℕ) (c : R) :
    derivative^[n] ((X - C c) ^ n) = n.factorial := by
  sorry


end CommRing

section NoZeroDivisors

variable [Semiring R] [NoZeroDivisors R]

@[simp]
theorem dvd_derivative_iff {P : R[X]} : P ∣ derivative P ↔ derivative P = 0 where
  mp h := by
    by_cases hP : P = 0
    · simp only [hP, derivative_zero]
    exact eq_zero_of_dvd_of_degree_lt h (degree_derivative_lt hP)
  mpr h := by simp [h]

end NoZeroDivisors

section CommSemiringNoZeroDivisors

variable [CommSemiring R] [NoZeroDivisors R]

@[target] theorem derivative_pow_eq_zero {n : ℕ} (chn : (n : R) ≠ 0) {a : R[X]} :
    derivative (a ^ n) = 0 ↔ derivative a = 0 := by
  sorry


end CommSemiringNoZeroDivisors

end Derivative

end Polynomial
