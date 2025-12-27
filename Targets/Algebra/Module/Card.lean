import VerifiedAgora.tagger
/-
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Algebra.NoZeroSMulDivisors.Basic
import Mathlib.SetTheory.Cardinal.Basic

/-!
# Cardinality of a module

This file proves that the cardinality of a module without zero divisors is at least the cardinality
of its base ring.
-/

open Function

universe u v

namespace Cardinal

/-- The cardinality of a nontrivial module over a ring is at least the cardinality of the ring if
there are no zero divisors (for instance if the ring is a field) -/
@[target]
theorem mk_le_of_module (R : Type u) (E : Type v)
    [AddCommGroup E] [Ring R] [Module R E] [Nontrivial E] [NoZeroSMulDivisors R E] :
    Cardinal.lift.{v} (#R) ≤ Cardinal.lift.{u} (#E) := by sorry

end Cardinal
