import VerifiedAgora.tagger
/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
import Mathlib.Algebra.MonoidAlgebra.Degree
import Mathlib.Algebra.Order.Ring.WithTop
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Nat.Cast.WithTop

/-!
# Degree of univariate polynomials

## Main definitions

* `Polynomial.degree`: the degree of a polynomial, where `0` has degree `⊥`
* `Polynomial.natDegree`: the degree of a polynomial, where `0` has degree `0`
* `Polynomial.leadingCoeff`: the leading coefficient of a polynomial
* `Polynomial.Monic`: a polynomial is monic if its leading coefficient is 0
* `Polynomial.nextCoeff`: the next coefficient after the leading coefficient

## Main results

* `Polynomial.degree_eq_natDegree`: the degree and natDegree coincide for nonzero polynomials
-/

noncomputable section

open Finsupp Finset

open Polynomial

namespace Polynomial

universe u v

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

section Semiring

variable [Semiring R] {p q r : R[X]}

/-- `degree p` is the degree of the polynomial `p`, i.e. the largest `X`-exponent in `p`.
`degree p = some n` when `p ≠ 0` and `n` is the highest power of `X` that appears in `p`, otherwise
`degree 0 = ⊥`. -/
def degree (p : R[X]) : WithBot ℕ :=
  p.support.max

/-- `natDegree p` forces `degree p` to ℕ, by defining `natDegree 0 = 0`. -/
def natDegree (p : R[X]) : ℕ :=
  (degree p).unbotD 0

/-- `leadingCoeff p` gives the coefficient of the highest power of `X` in `p`. -/
def leadingCoeff (p : R[X]) : R :=
  coeff p (natDegree p)

/-- a polynomial is `Monic` if its leading coefficient is 1 -/
def Monic (p : R[X]) :=
  leadingCoeff p = (1 : R)

theorem Monic.def : Monic p ↔ leadingCoeff p = 1 :=
  Iff.rfl

instance Monic.decidable [DecidableEq R] : Decidable (Monic p) := by unfold Monic; infer_instance

@[simp]
theorem Monic.leadingCoeff {p : R[X]} (hp : p.Monic) : leadingCoeff p = 1 :=
  hp

theorem Monic.coeff_natDegree {p : R[X]} (hp : p.Monic) : p.coeff p.natDegree = 1 :=
  hp

@[simp]
theorem degree_zero : degree (0 : R[X]) = ⊥ :=
  rfl

@[simp]
theorem natDegree_zero : natDegree (0 : R[X]) = 0 :=
  rfl

@[simp]
theorem coeff_natDegree : coeff p (natDegree p) = leadingCoeff p :=
  rfl

@[target, simp]
theorem degree_eq_bot : degree p = ⊥ ↔ p = 0 :=
  sorry

@[target]
theorem degree_ne_bot : degree p ≠ ⊥ ↔ p ≠ 0 := sorry

@[target]
theorem degree_eq_natDegree (hp : p ≠ 0) : degree p = (natDegree p : WithBot ℕ) := by sorry

@[target]
theorem degree_eq_iff_natDegree_eq {p : R[X]} {n : ℕ} (hp : p ≠ 0) :
    p.degree = n ↔ p.natDegree = n := by sorry

theorem degree_eq_iff_natDegree_eq_of_pos {p : R[X]} {n : ℕ} (hn : 0 < n) :
    p.degree = n ↔ p.natDegree = n := by
  obtain rfl|h := eq_or_ne p 0
  · simp [hn.ne]
  · exact degree_eq_iff_natDegree_eq h

theorem natDegree_eq_of_degree_eq_some {p : R[X]} {n : ℕ} (h : degree p = n) : natDegree p = n := by
  rw [natDegree, h, Nat.cast_withBot, WithBot.unbotD_coe]

@[target]
theorem degree_ne_of_natDegree_ne {n : ℕ} : p.natDegree ≠ n → degree p ≠ n :=
  sorry

@[simp]
theorem degree_le_natDegree : degree p ≤ natDegree p :=
  WithBot.giUnbotDBot.gc.le_u_l _

@[target]
theorem natDegree_eq_of_degree_eq [Semiring S] {q : S[X]} (h : degree p = degree q) :
    natDegree p = natDegree q := by sorry

@[target]
theorem le_degree_of_ne_zero (h : coeff p n ≠ 0) : (n : WithBot ℕ) ≤ degree p := by sorry

theorem degree_mono [Semiring S] {f : R[X]} {g : S[X]} (h : f.support ⊆ g.support) :
    f.degree ≤ g.degree :=
  Finset.sup_mono h

@[target]
theorem degree_le_degree (h : coeff q (natDegree p) ≠ 0) : degree p ≤ degree q := by sorry

@[target]
theorem natDegree_le_iff_degree_le {n : ℕ} : natDegree p ≤ n ↔ degree p ≤ n :=
  sorry

@[target]
theorem natDegree_lt_iff_degree_lt (hp : p ≠ 0) : p.natDegree < n ↔ p.degree < ↑n :=
  sorry

@[target]
theorem natDegree_le_natDegree [Semiring S] {q : S[X]} (hpq : p.degree ≤ q.degree) :
    p.natDegree ≤ q.natDegree :=
  sorry

@[simp]
theorem degree_C (ha : a ≠ 0) : degree (C a) = (0 : WithBot ℕ) := by
  rw [degree, ← monomial_zero_left, support_monomial 0 ha, max_eq_sup_coe, sup_singleton,
    WithBot.coe_zero]

@[target]
theorem degree_C_le : degree (C a) ≤ 0 := by sorry

@[target]
theorem degree_C_lt : degree (C a) < 1 :=
  sorry

@[target]
theorem degree_one_le : degree (1 : R[X]) ≤ (0 : WithBot ℕ) := by sorry

@[target, simp]
theorem natDegree_C (a : R) : natDegree (C a) = 0 := by sorry

@[simp]
theorem natDegree_one : natDegree (1 : R[X]) = 0 :=
  natDegree_C 1

@[target, simp]
theorem natDegree_natCast (n : ℕ) : natDegree (n : R[X]) = 0 := by sorry

@[target, simp]
theorem natDegree_ofNat (n : ℕ) [Nat.AtLeastTwo n] :
    natDegree (ofNat(n) : R[X]) = 0 :=
  sorry

theorem degree_natCast_le (n : ℕ) : degree (n : R[X]) ≤ 0 := degree_le_of_natDegree_le (by simp)

@[target, simp]
theorem degree_monomial (n : ℕ) (ha : a ≠ 0) : degree (monomial n a) = n := by sorry

@[simp]
theorem degree_C_mul_X_pow (n : ℕ) (ha : a ≠ 0) : degree (C a * X ^ n) = n := by
  rw [C_mul_X_pow_eq_monomial, degree_monomial n ha]

theorem degree_C_mul_X (ha : a ≠ 0) : degree (C a * X) = 1 := by
  simpa only [pow_one] using degree_C_mul_X_pow 1 ha

@[target]
theorem degree_monomial_le (n : ℕ) (a : R) : degree (monomial n a) ≤ n :=
  sorry

@[target]
theorem degree_C_mul_X_pow_le (n : ℕ) (a : R) : degree (C a * X ^ n) ≤ n := by sorry

@[target]
theorem degree_C_mul_X_le (a : R) : degree (C a * X) ≤ 1 := by sorry

@[simp]
theorem natDegree_C_mul_X_pow (n : ℕ) (a : R) (ha : a ≠ 0) : natDegree (C a * X ^ n) = n :=
  natDegree_eq_of_degree_eq_some (degree_C_mul_X_pow n ha)

@[target, simp]
theorem natDegree_C_mul_X (a : R) (ha : a ≠ 0) : natDegree (C a * X) = 1 := by sorry

@[simp]
theorem natDegree_monomial [DecidableEq R] (i : ℕ) (r : R) :
    natDegree (monomial i r) = if r = 0 then 0 else i := by
  split_ifs with hr
  · simp [hr]
  · rw [← C_mul_X_pow_eq_monomial, natDegree_C_mul_X_pow i r hr]

@[target]
theorem natDegree_monomial_le (a : R) {m : ℕ} : (monomial m a).natDegree ≤ m := by sorry

@[target]
theorem natDegree_monomial_eq (i : ℕ) {r : R} (r0 : r ≠ 0) : (monomial i r).natDegree = i :=
  sorry

@[target]
theorem coeff_ne_zero_of_eq_degree (hn : degree p = n) : coeff p n ≠ 0 := sorry

@[target]
theorem degree_X_pow_le (n : ℕ) : degree (X ^ n : R[X]) ≤ n := by sorry

@[target]
theorem degree_X_le : degree (X : R[X]) ≤ 1 :=
  sorry

@[target]
theorem natDegree_X_le : (X : R[X]).natDegree ≤ 1 :=
  sorry

end Semiring

section NonzeroSemiring

variable [Semiring R] [Nontrivial R] {p q : R[X]}

@[target, simp]
theorem degree_one : degree (1 : R[X]) = (0 : WithBot ℕ) :=
  sorry

@[simp]
theorem degree_X : degree (X : R[X]) = 1 :=
  degree_monomial _ one_ne_zero

@[target, simp]
theorem natDegree_X : (X : R[X]).natDegree = 1 :=
  sorry

end NonzeroSemiring

section Ring

variable [Ring R]

@[target, simp]
theorem degree_neg (p : R[X]) : degree (-p) = degree p := by sorry

@[target]
theorem degree_neg_le_of_le {a : WithBot ℕ} {p : R[X]} (hp : degree p ≤ a) : degree (-p) ≤ a :=
  sorry

@[target, simp]
theorem natDegree_neg (p : R[X]) : natDegree (-p) = natDegree p := by sorry

@[target]
theorem natDegree_neg_le_of_le {p : R[X]} (hp : natDegree p ≤ m) : natDegree (-p) ≤ m :=
  sorry

@[target, simp]
theorem natDegree_intCast (n : ℤ) : natDegree (n : R[X]) = 0 := by sorry

theorem degree_intCast_le (n : ℤ) : degree (n : R[X]) ≤ 0 := degree_le_of_natDegree_le (by simp)

@[target, simp]
theorem leadingCoeff_neg (p : R[X]) : (-p).leadingCoeff = -p.leadingCoeff := by sorry

end Ring

section Semiring

variable [Semiring R] {p : R[X]}

/-- The second-highest coefficient, or 0 for constants -/
def nextCoeff (p : R[X]) : R :=
  if p.natDegree = 0 then 0 else p.coeff (p.natDegree - 1)

lemma nextCoeff_eq_zero :
    p.nextCoeff = 0 ↔ p.natDegree = 0 ∨ 0 < p.natDegree ∧ p.coeff (p.natDegree - 1) = 0 := by
  simp [nextCoeff, or_iff_not_imp_left, pos_iff_ne_zero]; aesop

lemma nextCoeff_ne_zero : p.nextCoeff ≠ 0 ↔ p.natDegree ≠ 0 ∧ p.coeff (p.natDegree - 1) ≠ 0 := by
  simp [nextCoeff]

@[simp]
theorem nextCoeff_C_eq_zero (c : R) : nextCoeff (C c) = 0 := by
  rw [nextCoeff]
  simp

@[target]
theorem nextCoeff_of_natDegree_pos (hp : 0 < p.natDegree) :
    nextCoeff p = p.coeff (p.natDegree - 1) := by sorry

variable {p q : R[X]} {ι : Type*}

theorem degree_add_le (p q : R[X]) : degree (p + q) ≤ max (degree p) (degree q) := by
  simpa only [degree, ← support_toFinsupp, toFinsupp_add]
    using AddMonoidAlgebra.sup_support_add_le _ _ _

theorem degree_add_le_of_degree_le {p q : R[X]} {n : ℕ} (hp : degree p ≤ n) (hq : degree q ≤ n) :
    degree (p + q) ≤ n :=
  (degree_add_le p q).trans <| max_le hp hq

@[target]
theorem degree_add_le_of_le {a b : WithBot ℕ} (hp : degree p ≤ a) (hq : degree q ≤ b) :
    degree (p + q) ≤ max a b :=
  sorry

@[target]
theorem natDegree_add_le (p q : R[X]) : natDegree (p + q) ≤ max (natDegree p) (natDegree q) := by sorry

@[target]
theorem natDegree_add_le_of_degree_le {p q : R[X]} {n : ℕ} (hp : natDegree p ≤ n)
    (hq : natDegree q ≤ n) : natDegree (p + q) ≤ n :=
  sorry

@[target]
theorem natDegree_add_le_of_le (hp : natDegree p ≤ m) (hq : natDegree q ≤ n) :
    natDegree (p + q) ≤ max m n :=
  sorry

@[simp]
theorem leadingCoeff_zero : leadingCoeff (0 : R[X]) = 0 :=
  rfl

@[target, simp]
theorem leadingCoeff_eq_zero : leadingCoeff p = 0 ↔ p = 0 :=
  sorry

@[target]
theorem leadingCoeff_ne_zero : leadingCoeff p ≠ 0 ↔ p ≠ 0 := by sorry

theorem leadingCoeff_eq_zero_iff_deg_eq_bot : leadingCoeff p = 0 ↔ degree p = ⊥ := by
  rw [leadingCoeff_eq_zero, degree_eq_bot]

@[target]
theorem natDegree_C_mul_X_pow_le (a : R) (n : ℕ) : natDegree (C a * X ^ n) ≤ n :=
  sorry

@[target]
theorem degree_erase_le (p : R[X]) (n : ℕ) : degree (p.erase n) ≤ degree p := by sorry

theorem degree_erase_lt (hp : p ≠ 0) : degree (p.erase (natDegree p)) < degree p := by
  apply lt_of_le_of_ne (degree_erase_le _ _)
  rw [degree_eq_natDegree hp, degree, support_erase]
  exact fun h => not_mem_erase _ _ (mem_of_max h)

theorem degree_update_le (p : R[X]) (n : ℕ) (a : R) : degree (p.update n a) ≤ max (degree p) n := by
  classical
  rw [degree, support_update]
  split_ifs
  · exact (Finset.max_mono (erase_subset _ _)).trans (le_max_left _ _)
  · rw [max_insert, max_comm]
    exact le_rfl

@[target]
theorem degree_sum_le (s : Finset ι) (f : ι → R[X]) :
    degree (∑ i ∈ s, f i) ≤ s.sup fun b => degree (f b) :=
  sorry

@[target]
theorem degree_mul_le (p q : R[X]) : degree (p * q) ≤ degree p + degree q := by sorry

@[target]
theorem degree_mul_le_of_le {a b : WithBot ℕ} (hp : degree p ≤ a) (hq : degree q ≤ b) :
    degree (p * q) ≤ a + b :=
  sorry

theorem degree_pow_le (p : R[X]) : ∀ n : ℕ, degree (p ^ n) ≤ n • degree p
  | 0 => by rw [pow_zero, zero_nsmul]; exact degree_one_le
  | n + 1 =>
    calc
      degree (p ^ (n + 1)) ≤ degree (p ^ n) + degree p := by
        rw [pow_succ]; exact degree_mul_le _ _
      _ ≤ _ := by rw [succ_nsmul]; exact add_le_add_right (degree_pow_le _ _) _

theorem degree_pow_le_of_le {a : WithBot ℕ} (b : ℕ) (hp : degree p ≤ a) :
    degree (p ^ b) ≤ b * a := by
  induction b with
  | zero => simp [degree_one_le]
  | succ n hn =>
      rw [Nat.cast_succ, add_mul, one_mul, pow_succ]
      exact degree_mul_le_of_le hn hp

@[simp]
theorem leadingCoeff_monomial (a : R) (n : ℕ) : leadingCoeff (monomial n a) = a := by
  classical
  by_cases ha : a = 0
  · simp only [ha, (monomial n).map_zero, leadingCoeff_zero]
  · rw [leadingCoeff, natDegree_monomial, if_neg ha, coeff_monomial]
    simp

theorem leadingCoeff_C_mul_X_pow (a : R) (n : ℕ) : leadingCoeff (C a * X ^ n) = a := by
  rw [C_mul_X_pow_eq_monomial, leadingCoeff_monomial]

@[target]
theorem leadingCoeff_C_mul_X (a : R) : leadingCoeff (C a * X) = a := by sorry

@[target, simp]
theorem leadingCoeff_C (a : R) : leadingCoeff (C a) = a :=
  sorry

@[target]
theorem leadingCoeff_X_pow (n : ℕ) : leadingCoeff ((X : R[X]) ^ n) = 1 := by sorry

@[target]
theorem leadingCoeff_X : leadingCoeff (X : R[X]) = 1 := by sorry

@[target, simp]
theorem monic_X_pow (n : ℕ) : Monic (X ^ n : R[X]) :=
  sorry

@[target, simp]
theorem monic_X : Monic (X : R[X]) :=
  sorry

@[target]
theorem leadingCoeff_one : leadingCoeff (1 : R[X]) = 1 :=
  sorry

@[simp]
theorem monic_one : Monic (1 : R[X]) :=
  leadingCoeff_C _

theorem Monic.ne_zero {R : Type*} [Semiring R] [Nontrivial R] {p : R[X]} (hp : p.Monic) :
    p ≠ 0 := by
  rintro rfl
  simp [Monic] at hp

theorem Monic.ne_zero_of_ne (h : (0 : R) ≠ 1) {p : R[X]} (hp : p.Monic) : p ≠ 0 := by
  nontriviality R
  exact hp.ne_zero

@[target]
theorem Monic.ne_zero_of_polynomial_ne {r} (hp : Monic p) (hne : q ≠ r) : p ≠ 0 :=
  sorry

@[target]
theorem natDegree_mul_le {p q : R[X]} : natDegree (p * q) ≤ natDegree p + natDegree q := by sorry

@[target]
theorem natDegree_mul_le_of_le (hp : natDegree p ≤ m) (hg : natDegree q ≤ n) :
    natDegree (p * q) ≤ m + n :=
sorry

theorem natDegree_pow_le {p : R[X]} {n : ℕ} : (p ^ n).natDegree ≤ n * p.natDegree := by
  induction n with
  | zero => simp
  | succ i hi =>
    rw [pow_succ, Nat.succ_mul]
    apply le_trans natDegree_mul_le (add_le_add_right hi _)

theorem natDegree_pow_le_of_le (n : ℕ) (hp : natDegree p ≤ m) :
    natDegree (p ^ n) ≤ n * m :=
  natDegree_pow_le.trans (Nat.mul_le_mul le_rfl ‹_›)

@[target]
theorem natDegree_eq_zero_iff_degree_le_zero : p.natDegree = 0 ↔ p.degree ≤ 0 := by sorry

@[target]
theorem degree_zero_le : degree (0 : R[X]) ≤ 0 := sorry

@[target]
theorem degree_le_iff_coeff_zero (f : R[X]) (n : WithBot ℕ) :
    degree f ≤ n ↔ ∀ m : ℕ, n < m → coeff f m = 0 := by sorry

@[target]
theorem degree_lt_iff_coeff_zero (f : R[X]) (n : ℕ) :
    degree f < n ↔ ∀ m : ℕ, n ≤ m → coeff f m = 0 := by sorry

theorem natDegree_pos_iff_degree_pos : 0 < natDegree p ↔ 0 < degree p :=
  lt_iff_lt_of_le_iff_le natDegree_le_iff_degree_le

end Semiring

section NontrivialSemiring

variable [Semiring R] [Nontrivial R] {p q : R[X]} (n : ℕ)

@[target, simp]
theorem degree_X_pow : degree ((X : R[X]) ^ n) = n := by sorry

@[simp]
theorem natDegree_X_pow : natDegree ((X : R[X]) ^ n) = n :=
  natDegree_eq_of_degree_eq_some (degree_X_pow n)

end NontrivialSemiring

section Ring

variable [Ring R] {p q : R[X]}

theorem degree_sub_le (p q : R[X]) : degree (p - q) ≤ max (degree p) (degree q) := by
  simpa only [degree_neg q] using degree_add_le p (-q)

@[target]
theorem degree_sub_le_of_le {a b : WithBot ℕ} (hp : degree p ≤ a) (hq : degree q ≤ b) :
    degree (p - q) ≤ max a b :=
  sorry

theorem natDegree_sub_le (p q : R[X]) : natDegree (p - q) ≤ max (natDegree p) (natDegree q) := by
  simpa only [← natDegree_neg q] using natDegree_add_le p (-q)

@[target]
theorem natDegree_sub_le_of_le (hp : natDegree p ≤ m) (hq : natDegree q ≤ n) :
    natDegree (p - q) ≤ max m n :=
  sorry

theorem degree_sub_lt (hd : degree p = degree q) (hp0 : p ≠ 0)
    (hlc : leadingCoeff p = leadingCoeff q) : degree (p - q) < degree p :=
  have hp : monomial (natDegree p) (leadingCoeff p) + p.erase (natDegree p) = p :=
    monomial_add_erase _ _
  have hq : monomial (natDegree q) (leadingCoeff q) + q.erase (natDegree q) = q :=
    monomial_add_erase _ _
  have hd' : natDegree p = natDegree q := by unfold natDegree; rw [hd]
  have hq0 : q ≠ 0 := mt degree_eq_bot.2 (hd ▸ mt degree_eq_bot.1 hp0)
  calc
    degree (p - q) = degree (erase (natDegree q) p + -erase (natDegree q) q) := by
      conv =>
        lhs
        rw [← hp, ← hq, hlc, hd', add_sub_add_left_eq_sub, sub_eq_add_neg]
    _ ≤ max (degree (erase (natDegree q) p)) (degree (erase (natDegree q) q)) :=
      (degree_neg (erase (natDegree q) q) ▸ degree_add_le _ _)
    _ < degree p := max_lt_iff.2 ⟨hd' ▸ degree_erase_lt hp0, hd.symm ▸ degree_erase_lt hq0⟩

theorem degree_X_sub_C_le (r : R) : (X - C r).degree ≤ 1 :=
  (degree_sub_le _ _).trans (max_le degree_X_le (degree_C_le.trans zero_le_one))

@[target]
theorem natDegree_X_sub_C_le (r : R) : (X - C r).natDegree ≤ 1 :=
  sorry

end Ring

end Polynomial
