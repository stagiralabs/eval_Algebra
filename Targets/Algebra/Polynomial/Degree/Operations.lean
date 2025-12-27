import VerifiedAgora.tagger
/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Definitions

/-!
# Lemmas for calculating the degree of univariate polynomials

## Main results
- `degree_mul` : The degree of the product is the sum of degrees
- `leadingCoeff_add_of_degree_eq` and `leadingCoeff_add_of_degree_lt` :
    The leading coefficient of a sum is determined by the leading coefficients and degrees
-/

noncomputable section

open Finsupp Finset

open Polynomial

namespace Polynomial

universe u v

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

section Semiring

variable [Semiring R] [Semiring S] {p q r : R[X]}

theorem supDegree_eq_degree (p : R[X]) : p.toFinsupp.supDegree WithBot.some = p.degree :=
  max_eq_sup_coe

@[target]
theorem degree_lt_wf : WellFounded fun p q : R[X] => degree p < degree q :=
  sorry

instance : WellFoundedRelation R[X] :=
  ⟨_, degree_lt_wf⟩

@[nontriviality]
theorem monic_of_subsingleton [Subsingleton R] (p : R[X]) : Monic p :=
  Subsingleton.elim _ _

@[nontriviality]
theorem degree_of_subsingleton [Subsingleton R] : degree p = ⊥ := by
  rw [Subsingleton.elim p 0, degree_zero]

@[nontriviality]
theorem natDegree_of_subsingleton [Subsingleton R] : natDegree p = 0 := by
  rw [Subsingleton.elim p 0, natDegree_zero]

@[target]
theorem le_natDegree_of_ne_zero (h : coeff p n ≠ 0) : n ≤ natDegree p := by sorry

@[target]
theorem degree_eq_of_le_of_coeff_ne_zero (pn : p.degree ≤ n) (p1 : p.coeff n ≠ 0) : p.degree = n :=
  sorry

theorem natDegree_eq_of_le_of_coeff_ne_zero (pn : p.natDegree ≤ n) (p1 : p.coeff n ≠ 0) :
    p.natDegree = n :=
  pn.antisymm (le_natDegree_of_ne_zero p1)

@[target]
theorem natDegree_lt_natDegree {q : S[X]} (hp : p ≠ 0) (hpq : p.degree < q.degree) :
    p.natDegree < q.natDegree := by sorry

@[target]
lemma natDegree_eq_natDegree {q : S[X]} (hpq : p.degree = q.degree) :
    p.natDegree = q.natDegree := by sorry

theorem coeff_eq_zero_of_degree_lt (h : degree p < n) : coeff p n = 0 :=
  Classical.not_not.1 (mt le_degree_of_ne_zero (not_le_of_gt h))

@[target]
theorem coeff_eq_zero_of_natDegree_lt {p : R[X]} {n : ℕ} (h : p.natDegree < n) :
    p.coeff n = 0 := by sorry

@[target]
theorem ext_iff_natDegree_le {p q : R[X]} {n : ℕ} (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n) :
    p = q ↔ ∀ i ≤ n, p.coeff i = q.coeff i := by sorry

theorem ext_iff_degree_le {p q : R[X]} {n : ℕ} (hp : p.degree ≤ n) (hq : q.degree ≤ n) :
    p = q ↔ ∀ i ≤ n, p.coeff i = q.coeff i :=
  ext_iff_natDegree_le (natDegree_le_of_degree_le hp) (natDegree_le_of_degree_le hq)

@[simp]
theorem coeff_natDegree_succ_eq_zero {p : R[X]} : p.coeff (p.natDegree + 1) = 0 :=
  coeff_eq_zero_of_natDegree_lt (lt_add_one _)

-- We need the explicit `Decidable` argument here because an exotic one shows up in a moment!
@[target]
theorem ite_le_natDegree_coeff (p : R[X]) (n : ℕ) (I : Decidable (n < 1 + natDegree p)) :
    @ite _ (n < 1 + natDegree p) I (coeff p n) 0 = coeff p n := by sorry

end Semiring

section Ring

variable [Ring R]

theorem coeff_mul_X_sub_C {p : R[X]} {r : R} {a : ℕ} :
    coeff (p * (X - C r)) (a + 1) = coeff p a - coeff p (a + 1) * r := by simp [mul_sub]

end Ring

section Semiring

variable [Semiring R] {p q : R[X]} {ι : Type*}

@[target]
theorem coeff_natDegree_eq_zero_of_degree_lt (h : degree p < degree q) :
    coeff p (natDegree q) = 0 :=
  sorry

@[target]
theorem ne_zero_of_degree_gt {n : WithBot ℕ} (h : n < degree p) : p ≠ 0 :=
  sorry

theorem ne_zero_of_degree_ge_degree (hpq : p.degree ≤ q.degree) (hp : p ≠ 0) : q ≠ 0 :=
  Polynomial.ne_zero_of_degree_gt
    (lt_of_lt_of_le (bot_lt_iff_ne_bot.mpr (by rwa [Ne, Polynomial.degree_eq_bot])) hpq :
      q.degree > ⊥)

@[target]
theorem ne_zero_of_natDegree_gt {n : ℕ} (h : n < natDegree p) : p ≠ 0 := sorry

@[target]
theorem degree_lt_degree (h : natDegree p < natDegree q) : degree p < degree q := by sorry

@[target]
theorem natDegree_lt_natDegree_iff (hp : p ≠ 0) : natDegree p < natDegree q ↔ degree p < degree q :=
  sorry

theorem eq_C_of_degree_le_zero (h : degree p ≤ 0) : p = C (coeff p 0) := by
  ext (_ | n)
  · simp
  rw [coeff_C, if_neg (Nat.succ_ne_zero _), coeff_eq_zero_of_degree_lt]
  exact h.trans_lt (WithBot.coe_lt_coe.2 n.succ_pos)

@[target]
theorem eq_C_of_degree_eq_zero (h : degree p = 0) : p = C (coeff p 0) :=
  sorry

theorem degree_le_zero_iff : degree p ≤ 0 ↔ p = C (coeff p 0) :=
  ⟨eq_C_of_degree_le_zero, fun h => h.symm ▸ degree_C_le⟩

@[target]
theorem degree_add_eq_left_of_degree_lt (h : degree q < degree p) : degree (p + q) = degree p :=
  sorry

theorem degree_add_eq_right_of_degree_lt (h : degree p < degree q) : degree (p + q) = degree q := by
  rw [add_comm, degree_add_eq_left_of_degree_lt h]

theorem natDegree_add_eq_left_of_degree_lt (h : degree q < degree p) :
    natDegree (p + q) = natDegree p :=
  natDegree_eq_of_degree_eq (degree_add_eq_left_of_degree_lt h)

@[target]
theorem natDegree_add_eq_left_of_natDegree_lt (h : natDegree q < natDegree p) :
    natDegree (p + q) = natDegree p :=
  sorry

@[target]
theorem natDegree_add_eq_right_of_degree_lt (h : degree p < degree q) :
    natDegree (p + q) = natDegree q :=
  sorry

theorem natDegree_add_eq_right_of_natDegree_lt (h : natDegree p < natDegree q) :
    natDegree (p + q) = natDegree q :=
  natDegree_add_eq_right_of_degree_lt (degree_lt_degree h)

theorem degree_add_C (hp : 0 < degree p) : degree (p + C a) = degree p :=
  add_comm (C a) p ▸ degree_add_eq_right_of_degree_lt <| lt_of_le_of_lt degree_C_le hp

@[simp] theorem natDegree_add_C {a : R} : (p + C a).natDegree = p.natDegree := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  by_cases hpd : p.degree ≤ 0
  · rw [eq_C_of_degree_le_zero hpd, ← C_add, natDegree_C, natDegree_C]
  · rw [not_le, degree_eq_natDegree hp, Nat.cast_pos, ← natDegree_C a] at hpd
    exact natDegree_add_eq_left_of_natDegree_lt hpd

@[simp] theorem natDegree_C_add {a : R} : (C a + p).natDegree = p.natDegree := by
  simp [add_comm _ p]

theorem degree_add_eq_of_leadingCoeff_add_ne_zero (h : leadingCoeff p + leadingCoeff q ≠ 0) :
    degree (p + q) = max p.degree q.degree :=
  le_antisymm (degree_add_le _ _) <|
    match lt_trichotomy (degree p) (degree q) with
    | Or.inl hlt => by
      rw [degree_add_eq_right_of_degree_lt hlt, max_eq_right_of_lt hlt]
    | Or.inr (Or.inl HEq) =>
      le_of_not_gt fun hlt : max (degree p) (degree q) > degree (p + q) =>
        h <|
          show leadingCoeff p + leadingCoeff q = 0 by
            rw [HEq, max_self] at hlt
            rw [leadingCoeff, leadingCoeff, natDegree_eq_of_degree_eq HEq, ← coeff_add]
            exact coeff_natDegree_eq_zero_of_degree_lt hlt
    | Or.inr (Or.inr hlt) => by
      rw [degree_add_eq_left_of_degree_lt hlt, max_eq_left_of_lt hlt]

@[target]
lemma natDegree_eq_of_natDegree_add_lt_left (p q : R[X])
    (H : natDegree (p + q) < natDegree p) : natDegree p = natDegree q := by sorry

@[target]
lemma natDegree_eq_of_natDegree_add_lt_right (p q : R[X])
    (H : natDegree (p + q) < natDegree q) : natDegree p = natDegree q :=
  sorry

lemma natDegree_eq_of_natDegree_add_eq_zero (p q : R[X])
    (H : natDegree (p + q) = 0) : natDegree p = natDegree q := by
  by_cases h₁ : natDegree p = 0; on_goal 1 => by_cases h₂ : natDegree q = 0
  · exact h₁.trans h₂.symm
  · apply natDegree_eq_of_natDegree_add_lt_right; rwa [H, Nat.pos_iff_ne_zero]
  · apply natDegree_eq_of_natDegree_add_lt_left; rwa [H, Nat.pos_iff_ne_zero]

theorem monic_of_natDegree_le_of_coeff_eq_one (n : ℕ) (pn : p.natDegree ≤ n) (p1 : p.coeff n = 1) :
    Monic p := by
  unfold Monic
  nontriviality
  refine (congr_arg _ <| natDegree_eq_of_le_of_coeff_ne_zero pn ?_).trans p1
  exact ne_of_eq_of_ne p1 one_ne_zero

theorem monic_of_degree_le_of_coeff_eq_one (n : ℕ) (pn : p.degree ≤ n) (p1 : p.coeff n = 1) :
    Monic p :=
  monic_of_natDegree_le_of_coeff_eq_one n (natDegree_le_of_degree_le pn) p1

theorem leadingCoeff_add_of_degree_lt (h : degree p < degree q) :
    leadingCoeff (p + q) = leadingCoeff q := by
  have : coeff p (natDegree q) = 0 := coeff_natDegree_eq_zero_of_degree_lt h
  simp only [leadingCoeff, natDegree_eq_of_degree_eq (degree_add_eq_right_of_degree_lt h), this,
    coeff_add, zero_add]

@[target]
theorem leadingCoeff_add_of_degree_lt' (h : degree q < degree p) :
    leadingCoeff (p + q) = leadingCoeff p := by sorry

theorem leadingCoeff_add_of_degree_eq (h : degree p = degree q)
    (hlc : leadingCoeff p + leadingCoeff q ≠ 0) :
    leadingCoeff (p + q) = leadingCoeff p + leadingCoeff q := by
  have : natDegree (p + q) = natDegree p := by
    apply natDegree_eq_of_degree_eq
    rw [degree_add_eq_of_leadingCoeff_add_ne_zero hlc, h, max_self]
  simp only [leadingCoeff, this, natDegree_eq_of_degree_eq h, coeff_add]

@[target, simp]
theorem coeff_mul_degree_add_degree (p q : R[X]) :
    coeff (p * q) (natDegree p + natDegree q) = leadingCoeff p * leadingCoeff q :=
  sorry

theorem degree_mul' (h : leadingCoeff p * leadingCoeff q ≠ 0) :
    degree (p * q) = degree p + degree q :=
  have hp : p ≠ 0 := by refine mt ?_ h; exact fun hp => by rw [hp, leadingCoeff_zero, zero_mul]
  have hq : q ≠ 0 := by refine mt ?_ h; exact fun hq => by rw [hq, leadingCoeff_zero, mul_zero]
  le_antisymm (degree_mul_le _ _)
    (by
      rw [degree_eq_natDegree hp, degree_eq_natDegree hq]
      refine le_degree_of_ne_zero (n := natDegree p + natDegree q) ?_
      rwa [coeff_mul_degree_add_degree])

theorem Monic.degree_mul (hq : Monic q) : degree (p * q) = degree p + degree q :=
  letI := Classical.decEq R
  if hp : p = 0 then by simp [hp]
  else degree_mul' <| by rwa [hq.leadingCoeff, mul_one, Ne, leadingCoeff_eq_zero]

theorem natDegree_mul' (h : leadingCoeff p * leadingCoeff q ≠ 0) :
    natDegree (p * q) = natDegree p + natDegree q :=
  have hp : p ≠ 0 := mt leadingCoeff_eq_zero.2 fun h₁ => h <| by rw [h₁, zero_mul]
  have hq : q ≠ 0 := mt leadingCoeff_eq_zero.2 fun h₁ => h <| by rw [h₁, mul_zero]
  natDegree_eq_of_degree_eq_some <| by
    rw [degree_mul' h, Nat.cast_add, degree_eq_natDegree hp, degree_eq_natDegree hq]

theorem leadingCoeff_mul' (h : leadingCoeff p * leadingCoeff q ≠ 0) :
    leadingCoeff (p * q) = leadingCoeff p * leadingCoeff q := by
  unfold leadingCoeff
  rw [natDegree_mul' h, coeff_mul_degree_add_degree]
  rfl

theorem leadingCoeff_pow' : leadingCoeff p ^ n ≠ 0 → leadingCoeff (p ^ n) = leadingCoeff p ^ n :=
  Nat.recOn n (by simp) fun n ih h => by
    have h₁ : leadingCoeff p ^ n ≠ 0 := fun h₁ => h <| by rw [pow_succ, h₁, zero_mul]
    have h₂ : leadingCoeff p * leadingCoeff (p ^ n) ≠ 0 := by rwa [pow_succ', ← ih h₁] at h
    rw [pow_succ', pow_succ', leadingCoeff_mul' h₂, ih h₁]

theorem degree_pow' : ∀ {n : ℕ}, leadingCoeff p ^ n ≠ 0 → degree (p ^ n) = n • degree p
  | 0 => fun h => by rw [pow_zero, ← C_1] at *; rw [degree_C h, zero_nsmul]
  | n + 1 => fun h => by
    have h₁ : leadingCoeff p ^ n ≠ 0 := fun h₁ => h <| by rw [pow_succ, h₁, zero_mul]
    have h₂ : leadingCoeff (p ^ n) * leadingCoeff p ≠ 0 := by
      rwa [pow_succ, ← leadingCoeff_pow' h₁] at h
    rw [pow_succ, degree_mul' h₂, succ_nsmul, degree_pow' h₁]

theorem natDegree_pow' {n : ℕ} (h : leadingCoeff p ^ n ≠ 0) : natDegree (p ^ n) = n * natDegree p :=
  letI := Classical.decEq R
  if hp0 : p = 0 then
    if hn0 : n = 0 then by simp [*] else by rw [hp0, zero_pow hn0]; simp
  else
    have hpn : p ^ n ≠ 0 := fun hpn0 => by
      have h1 := h
      rw [← leadingCoeff_pow' h1, hpn0, leadingCoeff_zero] at h; exact h rfl
    Option.some_inj.1 <|
      show (natDegree (p ^ n) : WithBot ℕ) = (n * natDegree p : ℕ) by
        rw [← degree_eq_natDegree hpn, degree_pow' h, degree_eq_natDegree hp0]; simp

@[target]
theorem leadingCoeff_monic_mul {p q : R[X]} (hp : Monic p) :
    leadingCoeff (p * q) = leadingCoeff q := by sorry

@[target]
theorem leadingCoeff_mul_monic {p q : R[X]} (hq : Monic q) :
    leadingCoeff (p * q) = leadingCoeff p :=
  sorry

@[target]
lemma degree_C_mul_of_isUnit (ha : IsUnit a) (p : R[X]) : (C a * p).degree = p.degree := by sorry

@[target]
lemma degree_mul_C_of_isUnit (ha : IsUnit a) (p : R[X]) : (p * C a).degree = p.degree := by sorry

@[target]
lemma natDegree_C_mul_of_isUnit (ha : IsUnit a) (p : R[X]) : (C a * p).natDegree = p.natDegree := by sorry

@[target]
lemma natDegree_mul_C_of_isUnit (ha : IsUnit a) (p : R[X]) : (p * C a).natDegree = p.natDegree := by sorry

lemma leadingCoeff_C_mul_of_isUnit (ha : IsUnit a) (p : R[X]) :
    (C a * p).leadingCoeff = a * p.leadingCoeff := by
  rwa [leadingCoeff, coeff_C_mul, natDegree_C_mul_of_isUnit, leadingCoeff]

@[target]
lemma leadingCoeff_mul_C_of_isUnit (ha : IsUnit a) (p : R[X]) :
    (p * C a).leadingCoeff = p.leadingCoeff * a := by sorry

@[target, simp]
theorem leadingCoeff_mul_X_pow {p : R[X]} {n : ℕ} : leadingCoeff (p * X ^ n) = leadingCoeff p :=
  sorry

@[simp]
theorem leadingCoeff_mul_X {p : R[X]} : leadingCoeff (p * X) = leadingCoeff p :=
  leadingCoeff_mul_monic monic_X

@[simp]
theorem coeff_pow_mul_natDegree (p : R[X]) (n : ℕ) :
    (p ^ n).coeff (n * p.natDegree) = p.leadingCoeff ^ n := by
  induction n with
  | zero => simp
  | succ i hi =>
    rw [pow_succ, pow_succ, Nat.succ_mul]
    by_cases hp1 : p.leadingCoeff ^ i = 0
    · rw [hp1, zero_mul]
      by_cases hp2 : p ^ i = 0
      · rw [hp2, zero_mul, coeff_zero]
      · apply coeff_eq_zero_of_natDegree_lt
        have h1 : (p ^ i).natDegree < i * p.natDegree := by
          refine lt_of_le_of_ne natDegree_pow_le fun h => hp2 ?_
          rw [← h, hp1] at hi
          exact leadingCoeff_eq_zero.mp hi
        calc
          (p ^ i * p).natDegree ≤ (p ^ i).natDegree + p.natDegree := natDegree_mul_le
          _ < i * p.natDegree + p.natDegree := add_lt_add_right h1 _

    · rw [← natDegree_pow' hp1, ← leadingCoeff_pow' hp1]
      exact coeff_mul_degree_add_degree _ _

@[target]
theorem coeff_mul_add_eq_of_natDegree_le {df dg : ℕ} {f g : R[X]}
    (hdf : natDegree f ≤ df) (hdg : natDegree g ≤ dg) :
    (f * g).coeff (df + dg) = f.coeff df * g.coeff dg := by sorry

theorem degree_smul_le (a : R) (p : R[X]) : degree (a • p) ≤ degree p := by
  refine (degree_le_iff_coeff_zero _ _).2 fun m hm => ?_
  rw [degree_lt_iff_coeff_zero] at hm
  simp [hm m le_rfl]

@[target]
theorem natDegree_smul_le (a : R) (p : R[X]) : natDegree (a • p) ≤ natDegree p :=
  sorry

@[target]
theorem degree_smul_of_isRightRegular_leadingCoeff (ha : a ≠ 0)
    (hp : IsRightRegular p.leadingCoeff) : (a • p).degree = p.degree := by sorry

@[target]
theorem degree_lt_degree_mul_X (hp : p ≠ 0) : p.degree < (p * X).degree := by sorry

theorem eq_C_of_natDegree_le_zero (h : natDegree p ≤ 0) : p = C (coeff p 0) :=
  eq_C_of_degree_le_zero <| degree_le_of_natDegree_le h

@[target]
theorem eq_C_of_natDegree_eq_zero (h : natDegree p = 0) : p = C (coeff p 0) :=
  sorry

@[target]
lemma natDegree_eq_zero {p : R[X]} : p.natDegree = 0 ↔ ∃ x, C x = p :=
  sorry

@[target]
theorem eq_C_coeff_zero_iff_natDegree_eq_zero : p = C (p.coeff 0) ↔ p.natDegree = 0 :=
  sorry

theorem eq_one_of_monic_natDegree_zero (hf : p.Monic) (hfd : p.natDegree = 0) : p = 1 := by
  rw [Monic.def, leadingCoeff, hfd] at hf
  rw [eq_C_of_natDegree_eq_zero hfd, hf, map_one]

theorem Monic.natDegree_eq_zero (hf : p.Monic) : p.natDegree = 0 ↔ p = 1 :=
  ⟨eq_one_of_monic_natDegree_zero hf, by rintro rfl; simp⟩

theorem degree_sum_fin_lt {n : ℕ} (f : Fin n → R) :
    degree (∑ i : Fin n, C (f i) * X ^ (i : ℕ)) < n :=
  (degree_sum_le _ _).trans_lt <|
    (Finset.sup_lt_iff <| WithBot.bot_lt_coe n).2 fun k _hk =>
      (degree_C_mul_X_pow_le _ _).trans_lt <| WithBot.coe_lt_coe.2 k.is_lt

@[target]
theorem degree_C_lt_degree_C_mul_X (ha : a ≠ 0) : degree (C b) < degree (C a * X) := by sorry

end Semiring

section NontrivialSemiring

variable [Semiring R] [Nontrivial R] {p q : R[X]} (n : ℕ)

@[simp] lemma natDegree_mul_X (hp : p ≠ 0) : natDegree (p * X) = natDegree p + 1 := by
  rw [natDegree_mul' (by simpa), natDegree_X]

@[simp] lemma natDegree_X_mul (hp : p ≠ 0) : natDegree (X * p) = natDegree p + 1 := by
  rw [commute_X p, natDegree_mul_X hp]

@[simp] lemma natDegree_mul_X_pow (hp : p ≠ 0) : natDegree (p * X ^ n) = natDegree p + n := by
  rw [natDegree_mul' (by simpa), natDegree_X_pow]

@[simp] lemma natDegree_X_pow_mul (hp : p ≠ 0) : natDegree (X ^ n * p) = natDegree p + n := by
  rw [commute_X_pow, natDegree_mul_X_pow n hp]

--  This lemma explicitly does not require the `Nontrivial R` assumption.
@[target]
theorem natDegree_X_pow_le {R : Type*} [Semiring R] (n : ℕ) : (X ^ n : R[X]).natDegree ≤ n := by sorry

@[target]
theorem not_isUnit_X : ¬IsUnit (X : R[X]) := sorry

@[simp]
theorem degree_mul_X : degree (p * X) = degree p + 1 := by simp [monic_X.degree_mul]

@[target, simp]
theorem degree_mul_X_pow : degree (p * X ^ n) = degree p + n := by sorry

end NontrivialSemiring

section Ring

variable [Ring R] {p q : R[X]}

@[target]
theorem degree_sub_C (hp : 0 < degree p) : degree (p - C a) = degree p := by sorry

@[simp]
theorem natDegree_sub_C {a : R} : natDegree (p - C a) = natDegree p := by
  rw [sub_eq_add_neg, ← C_neg, natDegree_add_C]

theorem leadingCoeff_sub_of_degree_lt (h : Polynomial.degree q < Polynomial.degree p) :
    (p - q).leadingCoeff = p.leadingCoeff := by
  rw [← q.degree_neg] at h
  rw [sub_eq_add_neg, leadingCoeff_add_of_degree_lt' h]

@[target]
theorem leadingCoeff_sub_of_degree_lt' (h : Polynomial.degree p < Polynomial.degree q) :
    (p - q).leadingCoeff = -q.leadingCoeff := by sorry

@[target]
theorem leadingCoeff_sub_of_degree_eq (h : degree p = degree q)
    (hlc : leadingCoeff p ≠ leadingCoeff q) :
    leadingCoeff (p - q) = leadingCoeff p - leadingCoeff q := by sorry

@[target]
theorem degree_sub_eq_left_of_degree_lt (h : degree q < degree p) : degree (p - q) = degree p := by sorry

@[target]
theorem degree_sub_eq_right_of_degree_lt (h : degree p < degree q) : degree (p - q) = degree q := by sorry

theorem natDegree_sub_eq_left_of_natDegree_lt (h : natDegree q < natDegree p) :
    natDegree (p - q) = natDegree p :=
  natDegree_eq_of_degree_eq (degree_sub_eq_left_of_degree_lt (degree_lt_degree h))

@[target]
theorem natDegree_sub_eq_right_of_natDegree_lt (h : natDegree p < natDegree q) :
    natDegree (p - q) = natDegree q :=
  sorry

end Ring

section NonzeroRing

variable [Nontrivial R]

section Semiring

variable [Semiring R]

@[simp]
theorem degree_X_add_C (a : R) : degree (X + C a) = 1 := by
  have : degree (C a) < degree (X : R[X]) :=
    calc
      degree (C a) ≤ 0 := degree_C_le
      _ < 1 := WithBot.coe_lt_coe.mpr zero_lt_one
      _ = degree X := degree_X.symm
  rw [degree_add_eq_left_of_degree_lt this, degree_X]

theorem natDegree_X_add_C (x : R) : (X + C x).natDegree = 1 :=
  natDegree_eq_of_degree_eq_some <| degree_X_add_C x

@[target, simp]
theorem nextCoeff_X_add_C [Semiring S] (c : S) : nextCoeff (X + C c) = c := by sorry

theorem degree_X_pow_add_C {n : ℕ} (hn : 0 < n) (a : R) : degree ((X : R[X]) ^ n + C a) = n := by
  have : degree (C a) < degree ((X : R[X]) ^ n) := degree_C_le.trans_lt <| by
    rwa [degree_X_pow, Nat.cast_pos]
  rw [degree_add_eq_left_of_degree_lt this, degree_X_pow]

theorem X_pow_add_C_ne_zero {n : ℕ} (hn : 0 < n) (a : R) : (X : R[X]) ^ n + C a ≠ 0 :=
  mt degree_eq_bot.2
    (show degree ((X : R[X]) ^ n + C a) ≠ ⊥ by
      rw [degree_X_pow_add_C hn a]; exact WithBot.coe_ne_bot)

theorem X_add_C_ne_zero (r : R) : X + C r ≠ 0 :=
  pow_one (X : R[X]) ▸ X_pow_add_C_ne_zero zero_lt_one r

@[target]
theorem zero_nmem_multiset_map_X_add_C {α : Type*} (m : Multiset α) (f : α → R) :
    (0 : R[X]) ∉ m.map fun a => X + C (f a) := sorry

theorem natDegree_X_pow_add_C {n : ℕ} {r : R} : (X ^ n + C r).natDegree = n := by
  by_cases hn : n = 0
  · rw [hn, pow_zero, ← C_1, ← RingHom.map_add, natDegree_C]
  · exact natDegree_eq_of_degree_eq_some (degree_X_pow_add_C (pos_iff_ne_zero.mpr hn) r)

@[target]
theorem X_pow_add_C_ne_one {n : ℕ} (hn : 0 < n) (a : R) : (X : R[X]) ^ n + C a ≠ 1 := sorry

@[target]
theorem X_add_C_ne_one (r : R) : X + C r ≠ 1 :=
  sorry

end Semiring

end NonzeroRing

section Semiring

variable [Semiring R]

@[simp]
theorem leadingCoeff_X_pow_add_C {n : ℕ} (hn : 0 < n) {r : R} :
    (X ^ n + C r).leadingCoeff = 1 := by
  nontriviality R
  rw [leadingCoeff, natDegree_X_pow_add_C, coeff_add, coeff_X_pow_self, coeff_C,
    if_neg (pos_iff_ne_zero.mp hn), add_zero]

@[target, simp]
theorem leadingCoeff_X_add_C [Semiring S] (r : S) : (X + C r).leadingCoeff = 1 := by sorry

@[target, simp]
theorem leadingCoeff_X_pow_add_one {n : ℕ} (hn : 0 < n) : (X ^ n + 1 : R[X]).leadingCoeff = 1 :=
  sorry

@[simp]
theorem leadingCoeff_pow_X_add_C (r : R) (i : ℕ) : leadingCoeff ((X + C r) ^ i) = 1 := by
  nontriviality
  rw [leadingCoeff_pow'] <;> simp

variable [NoZeroDivisors R] {p q : R[X]}

@[simp]
lemma degree_mul : degree (p * q) = degree p + degree q :=
  letI := Classical.decEq R
  if hp0 : p = 0 then by simp only [hp0, degree_zero, zero_mul, WithBot.bot_add]
  else
    if hq0 : q = 0 then by simp only [hq0, degree_zero, mul_zero, WithBot.add_bot]
    else degree_mul' <| mul_ne_zero (mt leadingCoeff_eq_zero.1 hp0) (mt leadingCoeff_eq_zero.1 hq0)

/-- `degree` as a monoid homomorphism between `R[X]` and `Multiplicative (WithBot ℕ)`.
  This is useful to prove results about multiplication and degree. -/
def degreeMonoidHom [Nontrivial R] : R[X] →* Multiplicative (WithBot ℕ) where
  toFun := degree
  map_one' := degree_one
  map_mul' _ _ := degree_mul

@[target, simp]
lemma degree_pow [Nontrivial R] (p : R[X]) (n : ℕ) : degree (p ^ n) = n • degree p :=
  sorry

@[target, simp]
lemma leadingCoeff_mul (p q : R[X]) : leadingCoeff (p * q) = leadingCoeff p * leadingCoeff q := by sorry
def leadingCoeffHom : R[X] →* R where
  toFun := leadingCoeff
  map_one' := by simp
  map_mul' := leadingCoeff_mul

@[target, simp]
lemma leadingCoeffHom_apply (p : R[X]) : leadingCoeffHom p = leadingCoeff p :=
  sorry

@[target, simp]
lemma leadingCoeff_pow (p : R[X]) (n : ℕ) : leadingCoeff (p ^ n) = leadingCoeff p ^ n :=
  sorry

lemma leadingCoeff_dvd_leadingCoeff {a p : R[X]} (hap : a ∣ p) :
    a.leadingCoeff ∣ p.leadingCoeff :=
  map_dvd leadingCoeffHom hap

lemma degree_le_mul_left (p : R[X]) (hq : q ≠ 0) : degree p ≤ degree (p * q) := by
  classical
  obtain rfl | hp := eq_or_ne p 0
  · simp
  · rw [degree_mul, degree_eq_natDegree hp, degree_eq_natDegree hq]
    exact WithBot.coe_le_coe.2 (Nat.le_add_right _ _)

end Semiring

section CommSemiring
variable [CommSemiring R] {a p : R[X]} (hp : p.Monic)
include hp

lemma Monic.natDegree_pos : 0 < natDegree p ↔ p ≠ 1 :=
  Nat.pos_iff_ne_zero.trans hp.natDegree_eq_zero.not

@[target]
lemma Monic.degree_pos : 0 < degree p ↔ p ≠ 1 :=
  sorry

end CommSemiring

section Ring

variable [Ring R]

@[target, simp]
theorem leadingCoeff_X_pow_sub_C {n : ℕ} (hn : 0 < n) {r : R} :
    (X ^ n - C r).leadingCoeff = 1 := by sorry

@[simp]
theorem leadingCoeff_X_pow_sub_one {n : ℕ} (hn : 0 < n) : (X ^ n - 1 : R[X]).leadingCoeff = 1 :=
  leadingCoeff_X_pow_sub_C hn

variable [Nontrivial R]

@[simp]
theorem degree_X_sub_C (a : R) : degree (X - C a) = 1 := by
  rw [sub_eq_add_neg, ← map_neg C a, degree_X_add_C]

@[target]
theorem natDegree_X_sub_C (x : R) : (X - C x).natDegree = 1 := by sorry

@[simp]
theorem nextCoeff_X_sub_C [Ring S] (c : S) : nextCoeff (X - C c) = -c := by
  rw [sub_eq_add_neg, ← map_neg C c, nextCoeff_X_add_C]

theorem degree_X_pow_sub_C {n : ℕ} (hn : 0 < n) (a : R) : degree ((X : R[X]) ^ n - C a) = n := by
  rw [sub_eq_add_neg, ← map_neg C a, degree_X_pow_add_C hn]

@[target]
theorem X_pow_sub_C_ne_zero {n : ℕ} (hn : 0 < n) (a : R) : (X : R[X]) ^ n - C a ≠ 0 := by sorry

@[target]
theorem X_sub_C_ne_zero (r : R) : X - C r ≠ 0 :=
  sorry

@[target]
theorem zero_nmem_multiset_map_X_sub_C {α : Type*} (m : Multiset α) (f : α → R) :
    (0 : R[X]) ∉ m.map fun a => X - C (f a) := sorry

@[target]
theorem natDegree_X_pow_sub_C {n : ℕ} {r : R} : (X ^ n - C r).natDegree = n := by sorry

@[target, simp]
theorem leadingCoeff_X_sub_C [Ring S] (r : S) : (X - C r).leadingCoeff = 1 := by sorry

end Ring
end Polynomial
