import VerifiedAgora.tagger
/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Johan Commelin
-/
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Ring.NegOnePow
import Mathlib.Tactic.NormNum

/-! # Integer powers of `-1` in a field -/

namespace Int

@[target] lemma cast_negOnePow (K : Type*) (n : ℤ) [Field K] : n.negOnePow = (-1 : K) ^ n := by
  sorry


@[deprecated (since := "2024-10-20")] alias coe_negOnePow := cast_negOnePow

end Int
