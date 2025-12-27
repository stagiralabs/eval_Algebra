import VerifiedAgora.tagger
/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Sym.Sym2.Order
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Lemmas on `Finset.sum` and `Finset.prod` involving `Finset.sym2`
-/

@[target]
theorem Finset.sum_sym2_filter_not_isDiag {ι α} [LinearOrder ι] [AddCommMonoid α]
    (s : Finset ι) (p : Sym2 ι → α) :
    ∑ i ∈ s.sym2 with ¬ i.IsDiag, p i = ∑ i ∈ s.offDiag with i.1 < i.2, p s(i.1, i.2) := by sorry