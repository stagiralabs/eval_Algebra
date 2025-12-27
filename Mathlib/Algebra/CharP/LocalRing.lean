import VerifiedAgora.tagger
/-
Copyright (c) 2022 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Eugster
-/
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.IsPrimePow
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs

/-!
# Characteristics of local rings

## Main result

- `charP_zero_or_prime_power`: In a commutative local ring the characteristics is either
  zero or a prime power.

-/


/-- In a local ring the characteristics is either zero or a prime power. -/
/-- In a local ring the characteristics is either zero or a prime power. -/
@[target] theorem charP_zero_or_prime_power (R : Type*) [CommRing R] [IsLocalRing R] (q : ℕ)
    [char_R_q : CharP R q] : q = 0 ∨ IsPrimePow q := by
  -- Assume `q := char(R)` is not zero.
  sorry
