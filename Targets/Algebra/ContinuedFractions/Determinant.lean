import VerifiedAgora.tagger
/-
Copyright (c) 2020 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import Mathlib.Algebra.ContinuedFractions.ContinuantsRecurrence
import Mathlib.Algebra.ContinuedFractions.TerminatedStable
import Mathlib.Tactic.Ring

/-!
# Determinant Formula for Simple Continued Fraction

## Summary

We derive the so-called *determinant formula* for `SimpContFract`:
`Aₙ * Bₙ₊₁ - Bₙ * Aₙ₊₁ = (-1)^(n + 1)`.

## TODO

Generalize this for `GenContFract` version:
`Aₙ * Bₙ₊₁ - Bₙ * Aₙ₊₁ = (-a₀) * (-a₁) * .. * (-aₙ₊₁)`.

## References

- https://en.wikipedia.org/wiki/Generalized_continued_fraction#The_determinant_formula

-/

open GenContFract

namespace SimpContFract

variable {K : Type*} [Field K] {s : SimpContFract K} {n : ℕ}

@[target]
theorem determinant_aux (hyp : n = 0 ∨ ¬(↑s : GenContFract K).TerminatedAt (n - 1)) :
    ((↑s : GenContFract K).contsAux n).a * ((↑s : GenContFract K).contsAux (n + 1)).b -
      ((↑s : GenContFract K).contsAux n).b * ((↑s : GenContFract K).contsAux (n + 1)).a =
        (-1) ^ n := by sorry
@[target]
theorem determinant (not_terminatedAt_n : ¬(↑s : GenContFract K).TerminatedAt n) :
    (↑s : GenContFract K).nums n * (↑s : GenContFract K).dens (n + 1) -
      (↑s : GenContFract K).dens n * (↑s : GenContFract K).nums (n + 1) = (-1) ^ (n + 1) :=
  sorry

end SimpContFract
