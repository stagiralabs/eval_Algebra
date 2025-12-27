import VerifiedAgora.tagger
/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# Lemmas about `Multiplicative ℤ`.
-/


open Nat

namespace Int

section Multiplicative

open Multiplicative

@[target]
lemma toAdd_pow (a : Multiplicative ℤ) (b : ℕ) : (a ^ b).toAdd = a.toAdd * b := sorry

@[target]
lemma toAdd_zpow (a : Multiplicative ℤ) (b : ℤ) : (a ^ b).toAdd = a.toAdd * b := sorry

@[simp] lemma ofAdd_mul (a b : ℤ) : ofAdd (a * b) = ofAdd a ^ b := (toAdd_zpow ..).symm

end Multiplicative

end Int
