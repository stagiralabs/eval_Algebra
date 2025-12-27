import VerifiedAgora.tagger
/-
Copyright (c) 2023 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathlib.Algebra.BigOperators.Expect

/-!
# Balancing a function

This file defines the balancing of a function `f`, defined as `f` minus its average.

This is the unique function `g` such that `f a - f b = g a - g b` for all `a` and `b`, and
`∑ a, g a = 0`. This is particularly useful in Fourier analysis as `f` and `g` then have the same
Fourier transform, except in the `0`-th frequency where the Fourier transform of `g` vanishes.
-/

open Finset Function
open scoped BigOperators

variable {ι H F G : Type*}

namespace Fintype

section AddCommGroup
variable [Fintype ι] [AddCommGroup G] [Module ℚ≥0 G] [AddCommGroup H] [Module ℚ≥0 H]

/-- The balancing of a function, namely the function minus its average. -/
/-- The balancing of a function, namely the function minus its average. -/
def balance (f : ι → G) : ι → G := by sorry


@[target] lemma balance_apply (f : ι → G) (x : ι) : balance f x = f x - 𝔼 y, f y := by sorry


@[target] lemma balance_zero : balance (0 : ι → G) = 0 := by sorry


@[simp] lemma balance_add (f g : ι → G) : balance (f + g) = balance f + balance g := by
  simp only [balance, expect_add_distrib, ← const_add, add_sub_add_comm, Pi.add_apply]

@[target] lemma balance_sub (f g : ι → G) : balance (f - g) = balance f - balance g := by
  sorry


@[target] lemma balance_neg (f : ι → G) : balance (-f) = -balance f := by
  sorry


@[target] lemma sum_balance (f : ι → G) : ∑ x, balance f x = 0 := by
  sorry


@[simp] lemma expect_balance (f : ι → G) : 𝔼 x, balance f x = 0 := by simp [expect]

@[target] lemma balance_idem (f : ι → G) : balance (balance f) = balance f := by
  sorry


@[target] lemma map_balance [FunLike F G H] [LinearMapClass F ℚ≥0 G H] (g : F) (f : ι → G) (a : ι) :
    g (balance f a) = balance (g ∘ f) a := by sorry


end AddCommGroup
end Fintype
