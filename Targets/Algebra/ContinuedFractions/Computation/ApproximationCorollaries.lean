import VerifiedAgora.tagger
/-
Copyright (c) 2021 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import Mathlib.Algebra.ContinuedFractions.Computation.Approximations
import Mathlib.Algebra.ContinuedFractions.ConvergentsEquiv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Topology.Order.LeftRightNhds

/-!
# Corollaries From Approximation Lemmas (`Algebra.ContinuedFractions.Computation.Approximations`)

## Summary

Using the equivalence of the convergents computations
(`GenContFract.convs` and `GenContFract.convs'`) for
continued fractions (see `Algebra.ContinuedFractions.ConvergentsEquiv`), it follows that the
convergents computations for `GenContFract.of` are equivalent.

Moreover, we show the convergence of the continued fractions computations, that is
`(GenContFract.of v).convs` indeed computes `v` in the limit.

## Main Definitions

- `ContFract.of` returns the (regular) continued fraction of a value.

## Main Theorems

- `GenContFract.of_convs_eq_convs'` shows that the convergents computations for
  `GenContFract.of` are equivalent.
- `GenContFract.of_convergence` shows that `(GenContFract.of v).convs` converges to `v`.

## Tags

convergence, fractions
-/

variable {K : Type*} (v : K) [LinearOrderedField K] [FloorRing K]

open GenContFract (of)
open scoped Topology

namespace GenContFract

@[target]
theorem of_convs_eq_convs' : (of v).convs = (of v).convs' :=
  sorry
@[target]
theorem convs_succ (n : ℕ) :
    (of v).convs (n + 1) = ⌊v⌋ + 1 / (of (Int.fract v)⁻¹).convs n := by sorry

section Convergence

/-!
### Convergence

We next show that `(GenContFract.of v).convs v` converges to `v`.
-/


variable [Archimedean K]

open Nat

@[target]
theorem of_convergence_epsilon :
    ∀ ε > (0 : K), ∃ N : ℕ, ∀ n ≥ N, |v - (of v).convs n| < ε := by sorry

@[target]
theorem of_convergence [TopologicalSpace K] [OrderTopology K] :
    Filter.Tendsto (of v).convs Filter.atTop <| 𝓝 v := by sorry

end Convergence

end GenContFract
