import VerifiedAgora.tagger
/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
import Mathlib.Algebra.Field.IsField
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Ring.Regular
import Mathlib.RingTheory.Multiplicity
import Mathlib.Data.Nat.Lattice

/-!
# Division of univariate polynomials

The main defs are `divByMonic` and `modByMonic`.
The compatibility between these is given by `modByMonic_add_div`.
We also define `rootMultiplicity`.
-/

noncomputable section

open Polynomial

open Finset

namespace Polynomial

universe u v w z

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

section Semiring

variable [Semiring R]

@[target]
theorem X_dvd_iff {f : R[X]} : X ∣ f ↔ f.coeff 0 = 0 :=
  sorry

theorem X_pow_dvd_iff {f : R[X]} {n : ℕ} : X ^ n ∣ f ↔ ∀ d < n, f.coeff d = 0 :=
  ⟨fun ⟨g, hgf⟩ d hd => by
    simp only [hgf, coeff_X_pow_mul', ite_eq_right_iff, not_le_of_lt hd, IsEmpty.forall_iff],
    fun hd => by
    induction n with
    | zero => simp [pow_zero, one_dvd]
    | succ n hn =>
      obtain ⟨g, hgf⟩ := hn fun d : ℕ => fun H : d < n => hd _ (Nat.lt_succ_of_lt H)
      have := coeff_X_pow_mul g n 0
      rw [zero_add, ← hgf, hd n (Nat.lt_succ_self n)] at this
      obtain ⟨k, hgk⟩ := Polynomial.X_dvd_iff.mpr this.symm
      use k
      rwa [pow_succ, mul_assoc, ← hgk]⟩

variable {p q : R[X]}

theorem finiteMultiplicity_of_degree_pos_of_monic (hp : (0 : WithBot ℕ) < degree p) (hmp : Monic p)
    (hq : q ≠ 0) : FiniteMultiplicity p q :=
  have zn0 : (0 : R) ≠ 1 :=
    haveI := Nontrivial.of_polynomial_ne hq
    zero_ne_one
  ⟨natDegree q, fun ⟨r, hr⟩ => by
    have hp0 : p ≠ 0 := fun hp0 => by simp [hp0] at hp
    have hr0 : r ≠ 0 := fun hr0 => by subst hr0; simp [hq] at hr
    have hpn1 : leadingCoeff p ^ (natDegree q + 1) = 1 := by simp [show _ = _ from hmp]
    have hpn0' : leadingCoeff p ^ (natDegree q + 1) ≠ 0 := hpn1.symm ▸ zn0.symm
    have hpnr0 : leadingCoeff (p ^ (natDegree q + 1)) * leadingCoeff r ≠ 0 := by
      simp only [leadingCoeff_pow' hpn0', leadingCoeff_eq_zero, hpn1, one_pow, one_mul, Ne,
          hr0, not_false_eq_true]
    have hnp : 0 < natDegree p := Nat.cast_lt.1 <| by
      rw [← degree_eq_natDegree hp0]; exact hp
    have := congr_arg natDegree hr
    rw [natDegree_mul' hpnr0, natDegree_pow' hpn0', add_mul, add_assoc] at this
    exact
      ne_of_lt
        (lt_add_of_le_of_pos (le_mul_of_one_le_right (Nat.zero_le _) hnp)
          (add_pos_of_pos_of_nonneg (by rwa [one_mul]) (Nat.zero_le _)))
        this⟩

@[deprecated (since := "2024-11-30")]
alias multiplicity_finite_of_degree_pos_of_monic := finiteMultiplicity_of_degree_pos_of_monic

end Semiring

section Ring

variable [Ring R] {p q : R[X]}

theorem div_wf_lemma (h : degree q ≤ degree p ∧ p ≠ 0) (hq : Monic q) :
    degree (p - q * (C (leadingCoeff p) * X ^ (natDegree p - natDegree q))) < degree p :=
  have hp : leadingCoeff p ≠ 0 := mt leadingCoeff_eq_zero.1 h.2
  have hq0 : q ≠ 0 := hq.ne_zero_of_polynomial_ne h.2
  have hlt : natDegree q ≤ natDegree p :=
    (Nat.cast_le (α := WithBot ℕ)).1
      (by rw [← degree_eq_natDegree h.2, ← degree_eq_natDegree hq0]; exact h.1)
  degree_sub_lt
    (by
      rw [hq.degree_mul_comm, hq.degree_mul, degree_C_mul_X_pow _ hp, degree_eq_natDegree h.2,
        degree_eq_natDegree hq0, ← Nat.cast_add, tsub_add_cancel_of_le hlt])
    h.2 (by rw [leadingCoeff_monic_mul hq, leadingCoeff_mul_X_pow, leadingCoeff_C])

/-- See `divByMonic`. -/
noncomputable def divModByMonicAux : ∀ (_p : R[X]) {q : R[X]}, Monic q → R[X] × R[X]
  | p, q, hq =>
    letI := Classical.decEq R
    if h : degree q ≤ degree p ∧ p ≠ 0 then
      let z := C (leadingCoeff p) * X ^ (natDegree p - natDegree q)
      have _wf := div_wf_lemma h hq
      let dm := divModByMonicAux (p - q * z) hq
      ⟨z + dm.1, dm.2⟩
    else ⟨0, p⟩
  termination_by p => p

/-- `divByMonic`, denoted as `p /ₘ q`, gives the quotient of `p` by a monic polynomial `q`. -/
def divByMonic (p q : R[X]) : R[X] :=
  letI := Classical.decEq R
  if hq : Monic q then (divModByMonicAux p hq).1 else 0

/-- `modByMonic`, denoted as `p  %ₘ q`, gives the remainder of `p` by a monic polynomial `q`. -/
def modByMonic (p q : R[X]) : R[X] :=
  letI := Classical.decEq R
  if hq : Monic q then (divModByMonicAux p hq).2 else p

@[inherit_doc]
infixl:70 " /ₘ " => divByMonic

@[inherit_doc]
infixl:70 " %ₘ " => modByMonic

@[target]
theorem degree_modByMonic_lt [Nontrivial R] :
    ∀ (p : R[X]) {q : R[X]} (_hq : Monic q), degree (p %ₘ q) < degree q
  | p, q, hq =>
    letI := sorry

@[target]
theorem natDegree_modByMonic_lt (p : R[X]) {q : R[X]} (hmq : Monic q) (hq : q ≠ 1) :
    natDegree (p %ₘ q) < q.natDegree := by sorry

@[simp]
theorem zero_modByMonic (p : R[X]) : 0 %ₘ p = 0 := by
  classical
  unfold modByMonic divModByMonicAux
  dsimp
  by_cases hp : Monic p
  · rw [dif_pos hp, if_neg (mt And.right (not_not_intro rfl)), Prod.snd_zero]
  · rw [dif_neg hp]

@[target, simp]
theorem zero_divByMonic (p : R[X]) : 0 /ₘ p = 0 := by sorry

@[target, simp]
theorem modByMonic_zero (p : R[X]) : p %ₘ 0 = p :=
  sorry

@[target, simp]
theorem divByMonic_zero (p : R[X]) : p /ₘ 0 = 0 :=
  sorry

@[target]
theorem divByMonic_eq_of_not_monic (p : R[X]) (hq : ¬Monic q) : p /ₘ q = 0 :=
  sorry

@[target]
theorem modByMonic_eq_of_not_monic (p : R[X]) (hq : ¬Monic q) : p %ₘ q = p :=
  sorry

@[target]
theorem modByMonic_eq_self_iff [Nontrivial R] (hq : Monic q) : p %ₘ q = p ↔ degree p < degree q :=
  sorry

@[target]
theorem degree_modByMonic_le (p : R[X]) {q : R[X]} (hq : Monic q) : degree (p %ₘ q) ≤ degree q := by sorry

theorem degree_modByMonic_le_left : degree (p %ₘ q) ≤ degree p := by
  nontriviality R
  by_cases hq : q.Monic
  · cases lt_or_ge (degree p) (degree q)
    · rw [(modByMonic_eq_self_iff hq).mpr ‹_›]
    · exact (degree_modByMonic_le p hq).trans ‹_›
  · rw [modByMonic_eq_of_not_monic p hq]

theorem natDegree_modByMonic_le (p : Polynomial R) {g : Polynomial R} (hg : g.Monic) :
    natDegree (p %ₘ g) ≤ g.natDegree :=
  natDegree_le_natDegree (degree_modByMonic_le p hg)

@[target]
theorem natDegree_modByMonic_le_left : natDegree (p %ₘ q) ≤ natDegree p :=
  sorry

theorem X_dvd_sub_C : X ∣ p - C (p.coeff 0) := by
  simp [X_dvd_iff, coeff_C]

@[target]
theorem modByMonic_eq_sub_mul_div :
    ∀ (p : R[X]) {q : R[X]} (_hq : Monic q), p %ₘ q = p - q * (p /ₘ q)
  | p, q, hq =>
    letI := sorry

theorem modByMonic_add_div (p : R[X]) {q : R[X]} (hq : Monic q) : p %ₘ q + q * (p /ₘ q) = p :=
  eq_sub_iff_add_eq.1 (modByMonic_eq_sub_mul_div p hq)

@[target]
theorem divByMonic_eq_zero_iff [Nontrivial R] (hq : Monic q) : p /ₘ q = 0 ↔ degree p < degree q :=
  sorry

@[target]
theorem degree_add_divByMonic (hq : Monic q) (h : degree q ≤ degree p) :
    degree q + degree (p /ₘ q) = degree p := by sorry

theorem degree_divByMonic_le (p q : R[X]) : degree (p /ₘ q) ≤ degree p :=
  letI := Classical.decEq R
  if hp0 : p = 0 then by simp only [hp0, zero_divByMonic, le_refl]
  else
    if hq : Monic q then
      if h : degree q ≤ degree p then by
        haveI := Nontrivial.of_polynomial_ne hp0
        rw [← degree_add_divByMonic hq h, degree_eq_natDegree hq.ne_zero,
          degree_eq_natDegree (mt (divByMonic_eq_zero_iff hq).1 (not_lt.2 h))]
        exact WithBot.coe_le_coe.2 (Nat.le_add_left _ _)
      else by
        unfold divByMonic divModByMonicAux
        simp [dif_pos hq, h, if_false, degree_zero, bot_le]
    else (divByMonic_eq_of_not_monic p hq).symm ▸ bot_le

@[target]
theorem degree_divByMonic_lt (p : R[X]) {q : R[X]} (hq : Monic q) (hp0 : p ≠ 0)
    (h0q : 0 < degree q) : degree (p /ₘ q) < degree p :=
  sorry

theorem natDegree_divByMonic (f : R[X]) {g : R[X]} (hg : g.Monic) :
    natDegree (f /ₘ g) = natDegree f - natDegree g := by
  nontriviality R
  by_cases hfg : f /ₘ g = 0
  · rw [hfg, natDegree_zero]
    rw [divByMonic_eq_zero_iff hg] at hfg
    rw [tsub_eq_zero_iff_le.mpr (natDegree_le_natDegree <| le_of_lt hfg)]
  have hgf := hfg
  rw [divByMonic_eq_zero_iff hg] at hgf
  push_neg at hgf
  have := degree_add_divByMonic hg hgf
  have hf : f ≠ 0 := by
    intro hf
    apply hfg
    rw [hf, zero_divByMonic]
  rw [degree_eq_natDegree hf, degree_eq_natDegree hg.ne_zero, degree_eq_natDegree hfg,
    ← Nat.cast_add, Nat.cast_inj] at this
  rw [← this, add_tsub_cancel_left]

theorem div_modByMonic_unique {f g} (q r : R[X]) (hg : Monic g)
    (h : r + g * q = f ∧ degree r < degree g) : f /ₘ g = q ∧ f %ₘ g = r := by
  nontriviality R
  have h₁ : r - f %ₘ g = -g * (q - f /ₘ g) :=
    eq_of_sub_eq_zero
      (by
        rw [← sub_eq_zero_of_eq (h.1.trans (modByMonic_add_div f hg).symm)]
        simp [mul_add, mul_comm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc])
  have h₂ : degree (r - f %ₘ g) = degree (g * (q - f /ₘ g)) := by simp [h₁]
  have h₄ : degree (r - f %ₘ g) < degree g :=
    calc
      degree (r - f %ₘ g) ≤ max (degree r) (degree (f %ₘ g)) := degree_sub_le _ _
      _ < degree g := max_lt_iff.2 ⟨h.2, degree_modByMonic_lt _ hg⟩
  have h₅ : q - f /ₘ g = 0 :=
    _root_.by_contradiction fun hqf =>
      not_le_of_gt h₄ <|
        calc
          degree g ≤ degree g + degree (q - f /ₘ g) := by
            rw [degree_eq_natDegree hg.ne_zero, degree_eq_natDegree hqf]
            norm_cast
            exact Nat.le_add_right _ _
          _ = degree (r - f %ₘ g) := by rw [h₂, degree_mul']; simpa [Monic.def.1 hg]
  exact ⟨Eq.symm <| eq_of_sub_eq_zero h₅, Eq.symm <| eq_of_sub_eq_zero <| by simpa [h₅] using h₁⟩

@[target]
theorem map_mod_divByMonic [Ring S] (f : R →+* S) (hq : Monic q) :
    (p /ₘ q).map f = p.map f /ₘ q.map f ∧ (p %ₘ q).map f = p.map f %ₘ q.map f := by sorry

@[target]
theorem map_divByMonic [Ring S] (f : R →+* S) (hq : Monic q) :
    (p /ₘ q).map f = p.map f /ₘ q.map f :=
  sorry

theorem map_modByMonic [Ring S] (f : R →+* S) (hq : Monic q) :
    (p %ₘ q).map f = p.map f %ₘ q.map f :=
  (map_mod_divByMonic f hq).2

theorem modByMonic_eq_zero_iff_dvd (hq : Monic q) : p %ₘ q = 0 ↔ q ∣ p :=
  ⟨fun h => by rw [← modByMonic_add_div p hq, h, zero_add]; exact dvd_mul_right _ _, fun h => by
    nontriviality R
    obtain ⟨r, hr⟩ := exists_eq_mul_right_of_dvd h
    by_contra hpq0
    have hmod : p %ₘ q = q * (r - p /ₘ q) := by rw [modByMonic_eq_sub_mul_div _ hq, mul_sub, ← hr]
    have : degree (q * (r - p /ₘ q)) < degree q := hmod ▸ degree_modByMonic_lt _ hq
    have hrpq0 : leadingCoeff (r - p /ₘ q) ≠ 0 := fun h =>
      hpq0 <|
        leadingCoeff_eq_zero.1
          (by rw [hmod, leadingCoeff_eq_zero.1 h, mul_zero, leadingCoeff_zero])
    have hlc : leadingCoeff q * leadingCoeff (r - p /ₘ q) ≠ 0 := by rwa [Monic.def.1 hq, one_mul]
    rw [degree_mul' hlc, degree_eq_natDegree hq.ne_zero,
      degree_eq_natDegree (mt leadingCoeff_eq_zero.2 hrpq0)] at this
    exact not_lt_of_ge (Nat.le_add_right _ _) (WithBot.coe_lt_coe.1 this)⟩


/-- See `Polynomial.mul_self_modByMonic` for the other multiplication order. That version, unlike
this one, requires commutativity. -/
@[target, simp]
lemma self_mul_modByMonic (hq : q.Monic) : (q * p) %ₘ q = 0 := by sorry

theorem map_dvd_map [Ring S] (f : R →+* S) (hf : Function.Injective f) {x y : R[X]}
    (hx : x.Monic) : x.map f ∣ y.map f ↔ x ∣ y := by
  rw [← modByMonic_eq_zero_iff_dvd hx, ← modByMonic_eq_zero_iff_dvd (hx.map f), ←
    map_modByMonic f hx]
  exact
    ⟨fun H => map_injective f hf <| by rw [H, Polynomial.map_zero], fun H => by
      rw [H, Polynomial.map_zero]⟩

@[target, simp]
theorem modByMonic_one (p : R[X]) : p %ₘ 1 = 0 :=
  sorry

@[target, simp]
theorem divByMonic_one (p : R[X]) : p /ₘ 1 = p := by sorry

@[target]
theorem sum_modByMonic_coeff (hq : q.Monic) {n : ℕ} (hn : q.degree ≤ n) :
    (∑ i : Fin n, monomial i ((p %ₘ q).coeff i)) = p %ₘ q := by sorry

@[target]
theorem mul_divByMonic_cancel_left (p : R[X]) {q : R[X]} (hmo : q.Monic) :
    q * p /ₘ q = p := by sorry

@[target]
lemma coeff_divByMonic_X_sub_C_rec (p : R[X]) (a : R) (n : ℕ) :
    (p /ₘ (X - C a)).coeff n = coeff p (n + 1) + a * (p /ₘ (X - C a)).coeff (n + 1) := by sorry

@[target]
theorem coeff_divByMonic_X_sub_C (p : R[X]) (a : R) (n : ℕ) :
    (p /ₘ (X - C a)).coeff n = ∑ i ∈ Icc (n + 1) p.natDegree, a ^ (i - (n + 1)) * p.coeff i := by sorry

variable (R) in
@[target]
theorem not_isField : ¬IsField R[X] := by sorry

section multiplicity

/-- An algorithm for deciding polynomial divisibility.
The algorithm is "compute `p %ₘ q` and compare to `0`".
See `Polynomial.modByMonic` for the algorithm that computes `%ₘ`.
-/
def decidableDvdMonic [DecidableEq R] (p : R[X]) (hq : Monic q) : Decidable (q ∣ p) :=
  decidable_of_iff (p %ₘ q = 0) (modByMonic_eq_zero_iff_dvd hq)

theorem finiteMultiplicity_X_sub_C (a : R) (h0 : p ≠ 0) : FiniteMultiplicity (X - C a) p := by
  haveI := Nontrivial.of_polynomial_ne h0
  refine finiteMultiplicity_of_degree_pos_of_monic ?_ (monic_X_sub_C _) h0
  rw [degree_X_sub_C]
  decide

@[deprecated (since := "2024-11-30")]
alias multiplicity_X_sub_C_finite := finiteMultiplicity_X_sub_C

/- Porting note: stripping out classical for decidability instance parameter might
make for better ergonomics -/
/-- The largest power of `X - C a` which divides `p`.
This *could be* computable via the divisibility algorithm `Polynomial.decidableDvdMonic`,
as shown by `Polynomial.rootMultiplicity_eq_nat_find_of_nonzero` which has a computable RHS. -/
def rootMultiplicity (a : R) (p : R[X]) : ℕ :=
  letI := Classical.decEq R
  if h0 : p = 0 then 0
  else
    let _ : DecidablePred fun n : ℕ => ¬(X - C a) ^ (n + 1) ∣ p := fun n =>
      have := decidableDvdMonic p ((monic_X_sub_C a).pow (n + 1))
      inferInstanceAs (Decidable ¬_)
    Nat.find (finiteMultiplicity_X_sub_C a h0)

/- Porting note: added the following due to diamond with decidableProp and
decidableDvdMonic see also [Zulip]
(https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/non-defeq.20aliased.20instance) -/
@[target]
theorem rootMultiplicity_eq_nat_find_of_nonzero [DecidableEq R] {p : R[X]} (p0 : p ≠ 0) {a : R} :
    letI : DecidablePred fun n : ℕ => ¬(X - C a) ^ (n + 1) ∣ p := sorry

theorem rootMultiplicity_eq_multiplicity [DecidableEq R]
    (p : R[X]) (a : R) :
    rootMultiplicity a p =
      if p = 0 then 0 else multiplicity (X - C a) p := by
  simp only [rootMultiplicity, multiplicity, emultiplicity]
  split
  · rfl
  rename_i h
  simp only [finiteMultiplicity_X_sub_C a h, ↓reduceDIte]
  rw [← ENat.some_eq_coe, WithTop.untopD_coe]
  congr

@[target, simp]
theorem rootMultiplicity_zero {x : R} : rootMultiplicity x 0 = 0 :=
  sorry

@[target, simp]
theorem rootMultiplicity_C (r a : R) : rootMultiplicity a (C r) = 0 := by sorry

theorem pow_rootMultiplicity_dvd (p : R[X]) (a : R) : (X - C a) ^ rootMultiplicity a p ∣ p :=
  letI := Classical.decEq R
  if h : p = 0 then by simp [h]
  else by
    classical
    rw [rootMultiplicity_eq_multiplicity, if_neg h]; apply pow_multiplicity_dvd

@[target]
theorem pow_mul_divByMonic_rootMultiplicity_eq (p : R[X]) (a : R) :
    (X - C a) ^ rootMultiplicity a p * (p /ₘ (X - C a) ^ rootMultiplicity a p) = p := by sorry

@[target]
theorem exists_eq_pow_rootMultiplicity_mul_and_not_dvd (p : R[X]) (hp : p ≠ 0) (a : R) :
    ∃ q : R[X], p = (X - C a) ^ p.rootMultiplicity a * q ∧ ¬ (X - C a) ∣ q := by sorry

end multiplicity

end Ring

section CommRing

variable [CommRing R] {p p₁ p₂ q : R[X]}

@[simp]
theorem modByMonic_X_sub_C_eq_C_eval (p : R[X]) (a : R) : p %ₘ (X - C a) = C (p.eval a) := by
  nontriviality R
  have h : (p %ₘ (X - C a)).eval a = p.eval a := by
    rw [modByMonic_eq_sub_mul_div _ (monic_X_sub_C a), eval_sub, eval_mul, eval_sub, eval_X,
      eval_C, sub_self, zero_mul, sub_zero]
  have : degree (p %ₘ (X - C a)) < 1 :=
    degree_X_sub_C a ▸ degree_modByMonic_lt p (monic_X_sub_C a)
  have : degree (p %ₘ (X - C a)) ≤ 0 := by
    revert this
    cases degree (p %ₘ (X - C a))
    · exact fun _ => bot_le
    · exact fun h => WithBot.coe_le_coe.2 (Nat.le_of_lt_succ (WithBot.coe_lt_coe.1 h))
  rw [eq_C_of_degree_le_zero this, eval_C] at h
  rw [eq_C_of_degree_le_zero this, h]

theorem mul_divByMonic_eq_iff_isRoot : (X - C a) * (p /ₘ (X - C a)) = p ↔ IsRoot p a :=
  .trans
    ⟨fun h => by rw [← h, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul],
    fun h => by
      conv_rhs =>
        rw [← modByMonic_add_div p (monic_X_sub_C a)]
        rw [modByMonic_X_sub_C_eq_C_eval, h, C_0, zero_add]⟩
    IsRoot.def.symm

theorem dvd_iff_isRoot : X - C a ∣ p ↔ IsRoot p a :=
  ⟨fun h => by
    rwa [← modByMonic_eq_zero_iff_dvd (monic_X_sub_C _), modByMonic_X_sub_C_eq_C_eval, ← C_0,
      C_inj] at h,
    fun h => ⟨p /ₘ (X - C a), by rw [mul_divByMonic_eq_iff_isRoot.2 h]⟩⟩

theorem X_sub_C_dvd_sub_C_eval : X - C a ∣ p - C (p.eval a) := by
  rw [dvd_iff_isRoot, IsRoot, eval_sub, eval_C, sub_self]

-- TODO: generalize this to Ring. In general, 0 can be replaced by any element in the center of R.
@[target]
theorem modByMonic_X (p : R[X]) : p %ₘ X = C (p.eval 0) := by sorry

theorem eval₂_modByMonic_eq_self_of_root [CommRing S] {f : R →+* S} {p q : R[X]} (hq : q.Monic)
    {x : S} (hx : q.eval₂ f x = 0) : (p %ₘ q).eval₂ f x = p.eval₂ f x := by
  rw [modByMonic_eq_sub_mul_div p hq, eval₂_sub, eval₂_mul, hx, zero_mul, sub_zero]

@[target]
theorem sub_dvd_eval_sub (a b : R) (p : R[X]) : a - b ∣ p.eval a - p.eval b := by sorry

@[target, simp]
theorem rootMultiplicity_eq_zero_iff {p : R[X]} {x : R} :
    rootMultiplicity x p = 0 ↔ IsRoot p x → p = 0 := by sorry

@[target]
theorem rootMultiplicity_eq_zero {p : R[X]} {x : R} (h : ¬IsRoot p x) : rootMultiplicity x p = 0 :=
  sorry

@[simp]
theorem rootMultiplicity_pos' {p : R[X]} {x : R} :
    0 < rootMultiplicity x p ↔ p ≠ 0 ∧ IsRoot p x := by
  rw [pos_iff_ne_zero, Ne, rootMultiplicity_eq_zero_iff, Classical.not_imp, and_comm]

@[target]
theorem rootMultiplicity_pos {p : R[X]} (hp : p ≠ 0) {x : R} :
    0 < rootMultiplicity x p ↔ IsRoot p x :=
  sorry

@[target]
theorem eval_divByMonic_pow_rootMultiplicity_ne_zero {p : R[X]} (a : R) (hp : p ≠ 0) :
    eval a (p /ₘ (X - C a) ^ rootMultiplicity a p) ≠ 0 := by sorry
@[simp]
lemma mul_self_modByMonic (hq : q.Monic) : (p * q) %ₘ q = 0 := by
  rw [modByMonic_eq_zero_iff_dvd hq]
  exact dvd_mul_left q p

lemma modByMonic_eq_of_dvd_sub (hq : q.Monic) (h : q ∣ p₁ - p₂) : p₁ %ₘ q = p₂ %ₘ q := by
  nontriviality R
  obtain ⟨f, sub_eq⟩ := h
  refine (div_modByMonic_unique (p₂ /ₘ q + f) _ hq ⟨?_, degree_modByMonic_lt _ hq⟩).2
  rw [sub_eq_iff_eq_add.mp sub_eq, mul_add, ← add_assoc, modByMonic_add_div _ hq, add_comm]

lemma add_modByMonic (p₁ p₂ : R[X]) : (p₁ + p₂) %ₘ q = p₁ %ₘ q + p₂ %ₘ q := by
  by_cases hq : q.Monic
  · rcases subsingleton_or_nontrivial R with hR | hR
    · simp only [eq_iff_true_of_subsingleton]
    · exact
      (div_modByMonic_unique (p₁ /ₘ q + p₂ /ₘ q) _ hq
          ⟨by
            rw [mul_add, add_left_comm, add_assoc, modByMonic_add_div _ hq, ← add_assoc,
              add_comm (q * _), modByMonic_add_div _ hq],
            (degree_add_le _ _).trans_lt
              (max_lt (degree_modByMonic_lt _ hq) (degree_modByMonic_lt _ hq))⟩).2
  · simp_rw [modByMonic_eq_of_not_monic _ hq]

@[target]
lemma neg_modByMonic (p q : R[X]) : (-p) %ₘ q = - (p %ₘ q) := by sorry

@[target]
lemma sub_modByMonic (p₁ p₂ q : R[X]) : (p₁ - p₂) %ₘ q = p₁ %ₘ q - p₂ %ₘ q := by sorry

lemma eval_divByMonic_eq_trailingCoeff_comp {p : R[X]} {t : R} :
    (p /ₘ (X - C t) ^ p.rootMultiplicity t).eval t = (p.comp (X + C t)).trailingCoeff := by
  obtain rfl | hp := eq_or_ne p 0
  · rw [zero_divByMonic, eval_zero, zero_comp, trailingCoeff_zero]
  have mul_eq := p.pow_mul_divByMonic_rootMultiplicity_eq t
  set m := p.rootMultiplicity t
  set g := p /ₘ (X - C t) ^ m
  have : (g.comp (X + C t)).coeff 0 = g.eval t := by
    rw [coeff_zero_eq_eval_zero, eval_comp, eval_add, eval_X, eval_C, zero_add]
  rw [← congr_arg (comp · <| X + C t) mul_eq, mul_comp, pow_comp, sub_comp, X_comp, C_comp,
    add_sub_cancel_right, ← reverse_leadingCoeff, reverse_X_pow_mul, reverse_leadingCoeff,
    trailingCoeff, Nat.le_zero.1 (natTrailingDegree_le_of_ne_zero <|
      this ▸ eval_divByMonic_pow_rootMultiplicity_ne_zero t hp), this]

/- Porting note: the ML3 proof no longer worked because of a conflict in the
inferred type and synthesized type for `DecidableRel` when using `Nat.le_find_iff` from
`Mathlib.Algebra.Polynomial.Div` After some discussion on [Zulip]
(https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/decidability.20leakage)
introduced `Polynomial.rootMultiplicity_eq_nat_find_of_nonzero` to contain the issue
-/
/-- The multiplicity of `a` as root of a nonzero polynomial `p` is at least `n` iff
`(X - a) ^ n` divides `p`. -/
@[target]
lemma le_rootMultiplicity_iff (p0 : p ≠ 0) {a : R} {n : ℕ} :
    n ≤ rootMultiplicity a p ↔ (X - C a) ^ n ∣ p := by sorry

@[target]
lemma rootMultiplicity_le_iff (p0 : p ≠ 0) (a : R) (n : ℕ) :
    rootMultiplicity a p ≤ n ↔ ¬(X - C a) ^ (n + 1) ∣ p := by sorry
@[target]
lemma rootMultiplicity_add {p q : R[X]} (a : R) (hzero : p + q ≠ 0) :
    min (rootMultiplicity a p) (rootMultiplicity a q) ≤ rootMultiplicity a (p + q) := by sorry

lemma le_rootMultiplicity_mul {p q : R[X]} (x : R) (hpq : p * q ≠ 0) :
    rootMultiplicity x p + rootMultiplicity x q ≤ rootMultiplicity x (p * q) := by
  rw [le_rootMultiplicity_iff hpq, pow_add]
  exact mul_dvd_mul (pow_rootMultiplicity_dvd p x) (pow_rootMultiplicity_dvd q x)

@[target]
lemma pow_rootMultiplicity_not_dvd (p0 : p ≠ 0) (a : R) :
    ¬(X - C a) ^ (rootMultiplicity a p + 1) ∣ p := by sorry
lemma rootMultiplicity_eq_natTrailingDegree' : p.rootMultiplicity 0 = p.natTrailingDegree := by
  by_cases h : p = 0
  · simp only [h, rootMultiplicity_zero, natTrailingDegree_zero]
  refine le_antisymm ?_ ?_
  · rw [rootMultiplicity_le_iff h, map_zero, sub_zero, X_pow_dvd_iff, not_forall]
    exact ⟨p.natTrailingDegree,
      fun h' ↦ trailingCoeff_nonzero_iff_nonzero.2 h <| h' <| Nat.lt.base _⟩
  · rw [le_rootMultiplicity_iff h, map_zero, sub_zero, X_pow_dvd_iff]
    exact fun _ ↦ coeff_eq_zero_of_lt_natTrailingDegree

/-- Division by a monic polynomial doesn't change the leading coefficient. -/
lemma leadingCoeff_divByMonic_of_monic (hmonic : q.Monic)
    (hdegree : q.degree ≤ p.degree) : (p /ₘ q).leadingCoeff = p.leadingCoeff := by
  nontriviality
  have h : q.leadingCoeff * (p /ₘ q).leadingCoeff ≠ 0 := by
    simpa [divByMonic_eq_zero_iff hmonic, hmonic.leadingCoeff,
      Nat.WithBot.one_le_iff_zero_lt] using hdegree
  nth_rw 2 [← modByMonic_add_div p hmonic]
  rw [leadingCoeff_add_of_degree_lt, leadingCoeff_monic_mul hmonic]
  rw [degree_mul' h, degree_add_divByMonic hmonic hdegree]
  exact (degree_modByMonic_lt p hmonic).trans_le hdegree

variable [IsDomain R]

@[target]
lemma degree_eq_one_of_irreducible_of_root (hi : Irreducible p) {x : R} (hx : IsRoot p x) :
    degree p = 1 :=
  sorry

@[target]
lemma leadingCoeff_divByMonic_X_sub_C (p : R[X]) (hp : degree p ≠ 0) (a : R) :
    leadingCoeff (p /ₘ (X - C a)) = leadingCoeff p := by sorry

@[target]
lemma eq_of_dvd_of_natDegree_le_of_leadingCoeff {p q : R[X]} (hpq : p ∣ q)
    (h₁ : q.natDegree ≤ p.natDegree) (h₂ : p.leadingCoeff = q.leadingCoeff) :
    p = q := by sorry

lemma associated_of_dvd_of_natDegree_le_of_leadingCoeff {p q : R[X]} (hpq : p ∣ q)
    (h₁ : q.natDegree ≤ p.natDegree) (h₂ : q.leadingCoeff ∣ p.leadingCoeff) :
    Associated p q :=
  have ⟨r, hr⟩ := hpq
  have ⟨u, hu⟩ := associated_of_dvd_dvd ⟨leadingCoeff r, hr ▸ leadingCoeff_mul p r⟩ h₂
  ⟨Units.map C.toMonoidHom u, eq_of_dvd_of_natDegree_le_of_leadingCoeff
    (by rwa [Units.mul_right_dvd]) (by simpa [natDegree_mul_C] using h₁) (by simpa using hu)⟩

@[target]
lemma associated_of_dvd_of_natDegree_le {K} [Field K] {p q : K[X]} (hpq : p ∣ q) (hq : q ≠ 0)
    (h₁ : q.natDegree ≤ p.natDegree) : Associated p q :=
  sorry

lemma associated_of_dvd_of_degree_eq {K} [Field K] {p q : K[X]} (hpq : p ∣ q)
    (h₁ : p.degree = q.degree) : Associated p q :=
  (Classical.em (q = 0)).elim (fun hq ↦ (show p = q by simpa [hq] using h₁) ▸ Associated.refl p)
    (associated_of_dvd_of_natDegree_le hpq · (natDegree_le_natDegree h₁.ge))

@[target]
lemma eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le {R} [CommRing R] {p q : R[X]}
    (hp : p.Monic) (hdiv : p ∣ q) (hdeg : q.natDegree ≤ p.natDegree) :
    q = C q.leadingCoeff * p := by sorry

@[target]
lemma eq_of_monic_of_dvd_of_natDegree_le {R} [CommRing R] {p q : R[X]} (hp : p.Monic)
    (hq : q.Monic) (hdiv : p ∣ q) (hdeg : q.natDegree ≤ p.natDegree) : q = p := by sorry

end CommRing

end Polynomial
