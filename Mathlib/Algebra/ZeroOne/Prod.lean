import VerifiedAgora.tagger
/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot, Yury Kudryashov
-/
import Mathlib.Util.AssertExists
import Mathlib.Data.One.Defs
import Mathlib.Data.Prod.Basic

/-!
# `Zero` and `One` instances on `M × N`

In this file we define `0` and `1` on `M × N` as the pair `(0, 0)` and `(1, 1)` respectively.
We also prove trivial `simp` lemmas:
-/

assert_not_exists AddMonoidWithOne
assert_not_exists DenselyOrdered
assert_not_exists MonoidWithZero

variable {G : Type*} {H : Type*} {M : Type*} {N : Type*} {P : Type*}

namespace Prod

@[to_additive]
instance instOne [One M] [One N] : One (M × N) :=
  ⟨(1, 1)⟩

@[to_additive (attr := by sorry


@[target] theorem one_eq_mk [One M] [One N] : (1 : M × N) = (1, 1) := by sorry


@[to_additive (attr := simp)]
theorem mk_one_one [One M] [One N] : ((1 : M), (1 : N)) = 1 := rfl

@[to_additive (attr := by sorry


@[to_additive (attr := simp)]
theorem swap_one [One M] [One N] : (1 : M × N).swap = 1 :=
  rfl

end Prod
