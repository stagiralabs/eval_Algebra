import VerifiedAgora.tagger
/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.GroupTheory.OrderOfElement

/-!
# Lemmas about rings of characteristic two

This file contains results about `CharP R 2`, in the `CharTwo` namespace.

The lemmas in this file with a `_sq` suffix are just special cases of the `_pow_char` lemmas
elsewhere, with a shorter name for ease of discovery, and no need for a `[Fact (Prime 2)]` argument.
-/

assert_not_exists Algebra LinearMap

variable {R ι : Type*}

namespace CharTwo

section AddMonoidWithOne

variable [AddMonoidWithOne R]

@[target] theorem two_eq_zero [CharP R 2] : (2 : R) = 0 := by
  sorry


/-- The only hypotheses required to build a `CharP R 2` instance are `1 ≠ 0` and `2 = 0`. -/
/-- The only hypotheses required to build a `CharP R 2` instance are `1 ≠ 0` and `2 = 0`. -/
@[target] theorem of_one_ne_zero_of_two_eq_zero (h₁ : (1 : R) ≠ 0) (h₂ : (2 : R) = 0) : CharP R 2 where
  cast_eq_zero_iff' n := by
    sorry


end AddMonoidWithOne

section Semiring

variable [Semiring R] [CharP R 2]

@[target] theorem add_self_eq_zero (x : R) : x + x = 0 := by sorry


@[scoped simp]
protected theorem two_nsmul (x : R) : 2 • x = 0 := by rw [two_smul, add_self_eq_zero]

end Semiring

section Ring

variable [Ring R] [CharP R 2]

@[target] theorem neg_eq (x : R) : -x = x := by
  sorry


theorem neg_eq' : Neg.neg = (id : R → R) :=
  funext neg_eq

@[target] theorem sub_eq_add (x y : R) : x - y = x + y := by sorry


@[deprecated sub_eq_add (since := "2024-10-24")]
theorem sub_eq_add' : HSub.hSub = (· + · : R → R → R) :=
  funext₂ sub_eq_add

@[target] theorem add_eq_iff_eq_add {a b c : R} : a + b = c ↔ a = c + b := by
  sorry


@[target] theorem eq_add_iff_add_eq {a b c : R} : a = b + c ↔ a + c = b := by
  sorry


@[scoped simp]
protected theorem two_zsmul (x : R) : (2 : ℤ) • x = 0 := by
  rw [two_zsmul, add_self_eq_zero]

end Ring

section CommSemiring

variable [CommSemiring R] [CharP R 2]

@[target] theorem add_sq (x y : R) : (x + y) ^ 2 = x ^ 2 + y ^ 2 := by sorry


@[target] theorem add_mul_self (x y : R) : (x + y) * (x + y) = x * x + y * y := by
  sorry


@[target] theorem list_sum_sq (l : List R) : l.sum ^ 2 = (l.map (· ^ 2)).sum := by sorry


@[target] theorem list_sum_mul_self (l : List R) : l.sum * l.sum = (List.map (fun x => x * x) l).sum := by
  sorry


@[target] theorem multiset_sum_sq (l : Multiset R) : l.sum ^ 2 = (l.map (· ^ 2)).sum := by sorry


@[target] theorem multiset_sum_mul_self (l : Multiset R) :
    l.sum * l.sum = (Multiset.map (fun x => x * x) l).sum := by sorry


@[target] theorem sum_sq (s : Finset ι) (f : ι → R) : (∑ i ∈ s, f i) ^ 2 = ∑ i ∈ s, f i ^ 2 := by sorry


@[target] theorem sum_mul_self (s : Finset ι) (f : ι → R) :
    ((∑ i ∈ s, f i) * ∑ i ∈ s, f i) = ∑ i ∈ s, f i * f i := by sorry


end CommSemiring

end CharTwo

section ringChar

variable [Ring R]

@[target] theorem neg_one_eq_one_iff [Nontrivial R] : (-1 : R) = 1 ↔ ringChar R = 2 := by
  sorry


@[target] theorem orderOf_neg_one [Nontrivial R] : orderOf (-1 : R) = if ringChar R = 2 then 1 else 2 := by
  sorry


end ringChar
