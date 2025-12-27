import VerifiedAgora.tagger
/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!
If `A` is a domain, and a finite-dimensional algebra over a field `F`, with prime dimension,
then there are no non-trivial `F`-subalgebras.
-/

open Module Submodule

@[target]
theorem Subalgebra.isSimpleOrder_of_finrank_prime (F A) [Field F] [Ring A] [IsDomain A]
    [Algebra F A] (hp : (finrank F A).Prime) : IsSimpleOrder (Subalgebra F A) :=
  sorry
-- TODO: `IntermediateField` version

@[deprecated (since := "2024-08-11")]
alias FiniteDimensional.Subalgebra.is_simple_order_of_finrank_prime :=
  Subalgebra.isSimpleOrder_of_finrank_prime
