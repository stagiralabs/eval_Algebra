import VerifiedAgora.tagger
/-
Copyright (c) 2020 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Polynomial.Reverse

/-!
# "Mirror" of a univariate polynomial

In this file we define `Polynomial.mirror`, a variant of `Polynomial.reverse`. The difference
between `reverse` and `mirror` is that `reverse` will decrease the degree if the polynomial is
divisible by `X`.

## Main definitions

- `Polynomial.mirror`

## Main results

- `Polynomial.mirror_mul_of_domain`: `mirror` preserves multiplication.
- `Polynomial.irreducible_of_mirror`: an irreducibility criterion involving `mirror`

-/


namespace Polynomial

section Semiring

variable {R : Type*} [Semiring R] (p q : R[X])

/-- mirror of a polynomial: reverses the coefficients while preserving `Polynomial.natDegree` -/
noncomputable def mirror :=
  p.reverse * X ^ p.natTrailingDegree

@[simp]
theorem mirror_zero : (0 : R[X]).mirror = 0 := by simp [mirror]

theorem mirror_monomial (n : ℕ) (a : R) : (monomial n a).mirror = monomial n a := by
  classical
    by_cases ha : a = 0
    · rw [ha, monomial_zero_right, mirror_zero]
    · rw [mirror, reverse, natDegree_monomial n a, if_neg ha, natTrailingDegree_monomial ha, ←
        C_mul_X_pow_eq_monomial, reflect_C_mul_X_pow, revAt_le (le_refl n), tsub_self, pow_zero,
        mul_one]

@[target]
theorem mirror_C (a : R) : (C a).mirror = C a :=
  sorry

@[target]
theorem mirror_X : X.mirror = (X : R[X]) :=
  sorry

theorem mirror_natDegree : p.mirror.natDegree = p.natDegree := by
  by_cases hp : p = 0
  · rw [hp, mirror_zero]
  nontriviality R
  rw [mirror, natDegree_mul', reverse_natDegree, natDegree_X_pow,
    tsub_add_cancel_of_le p.natTrailingDegree_le_natDegree]
  rwa [leadingCoeff_X_pow, mul_one, reverse_leadingCoeff, Ne, trailingCoeff_eq_zero]

theorem mirror_natTrailingDegree : p.mirror.natTrailingDegree = p.natTrailingDegree := by
  by_cases hp : p = 0
  · rw [hp, mirror_zero]
  · rw [mirror, natTrailingDegree_mul_X_pow ((mt reverse_eq_zero.mp) hp),
      natTrailingDegree_reverse, zero_add]

@[target]
theorem coeff_mirror (n : ℕ) :
    p.mirror.coeff n = p.coeff (revAt (p.natDegree + p.natTrailingDegree) n) := by sorry

--TODO: Extract `Finset.sum_range_rev_at` lemma.
@[target]
theorem mirror_eval_one : p.mirror.eval 1 = p.eval 1 := by sorry

@[target]
theorem mirror_mirror : p.mirror.mirror = p :=
  sorry

variable {p q}

theorem mirror_involutive : Function.Involutive (mirror : R[X] → R[X]) :=
  mirror_mirror

@[target]
theorem mirror_eq_iff : p.mirror = q ↔ p = q.mirror :=
  sorry

@[simp]
theorem mirror_inj : p.mirror = q.mirror ↔ p = q :=
  mirror_involutive.injective.eq_iff

@[target, simp]
theorem mirror_eq_zero : p.mirror = 0 ↔ p = 0 :=
  sorry

variable (p q)

@[target, simp]
theorem mirror_trailingCoeff : p.mirror.trailingCoeff = p.leadingCoeff := by sorry

@[simp]
theorem mirror_leadingCoeff : p.mirror.leadingCoeff = p.trailingCoeff := by
  rw [← p.mirror_mirror, mirror_trailingCoeff, p.mirror_mirror]

theorem coeff_mul_mirror :
    (p * p.mirror).coeff (p.natDegree + p.natTrailingDegree) = p.sum fun _ => (· ^ 2) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine
    (Finset.sum_congr rfl fun n hn => ?_).trans
      (p.sum_eq_of_subset (fun _ ↦ (· ^ 2)) (fun _ ↦ zero_pow two_ne_zero) fun n hn ↦
          Finset.mem_range_succ_iff.mpr
            ((le_natDegree_of_mem_supp n hn).trans (Nat.le_add_right _ _))).symm
  rw [coeff_mirror, ← revAt_le (Finset.mem_range_succ_iff.mp hn), revAt_invol, ← sq]

variable [NoZeroDivisors R]

@[target]
theorem natDegree_mul_mirror : (p * p.mirror).natDegree = 2 * p.natDegree := by sorry

@[target]
theorem natTrailingDegree_mul_mirror :
    (p * p.mirror).natTrailingDegree = 2 * p.natTrailingDegree := by sorry

end Semiring

section Ring

variable {R : Type*} [Ring R] (p q : R[X])

theorem mirror_neg : (-p).mirror = -p.mirror := by
  rw [mirror, mirror, reverse_neg, natTrailingDegree_neg, neg_mul_eq_neg_mul]

variable [NoZeroDivisors R]

@[target]
theorem mirror_mul_of_domain : (p * q).mirror = p.mirror * q.mirror := by sorry

@[target]
theorem mirror_smul (a : R) : (a • p).mirror = a • p.mirror := by sorry

end Ring

section CommRing

variable {R : Type*} [CommRing R] [NoZeroDivisors R] {f : R[X]}

theorem irreducible_of_mirror (h1 : ¬IsUnit f)
    (h2 : ∀ k, f * f.mirror = k * k.mirror → k = f ∨ k = -f ∨ k = f.mirror ∨ k = -f.mirror)
    (h3 : IsRelPrime f f.mirror) : Irreducible f := by
  constructor
  · exact h1
  · intro g h fgh
    let k := g * h.mirror
    have key : f * f.mirror = k * k.mirror := by
      rw [fgh, mirror_mul_of_domain, mirror_mul_of_domain, mirror_mirror, mul_assoc, mul_comm h,
        mul_comm g.mirror, mul_assoc, ← mul_assoc]
    have g_dvd_f : g ∣ f := by
      rw [fgh]
      exact dvd_mul_right g h
    have h_dvd_f : h ∣ f := by
      rw [fgh]
      exact dvd_mul_left h g
    have g_dvd_k : g ∣ k := dvd_mul_right g h.mirror
    have h_dvd_k_rev : h ∣ k.mirror := by
      rw [mirror_mul_of_domain, mirror_mirror]
      exact dvd_mul_left h g.mirror
    have hk := h2 k key
    rcases hk with (hk | hk | hk | hk)
    · exact Or.inr (h3 h_dvd_f (by rwa [← hk]))
    · exact Or.inr (h3 h_dvd_f (by rwa [← neg_eq_iff_eq_neg.mpr hk, mirror_neg, dvd_neg]))
    · exact Or.inl (h3 g_dvd_f (by rwa [← hk]))
    · exact Or.inl (h3 g_dvd_f (by rwa [← neg_eq_iff_eq_neg.mpr hk, dvd_neg]))

end CommRing

end Polynomial
