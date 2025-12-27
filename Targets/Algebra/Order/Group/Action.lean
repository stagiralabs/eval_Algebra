import VerifiedAgora.tagger
/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Results about `CovariantClass G α HSMul.hSMul LE.le`

When working with group actions rather than modules, we drop the `0 < c` condition.

Notably these are relevant for pointwise actions on set-like objects.
-/

variable {ι : Sort*} {M α : Type*}

@[target]
theorem smul_mono_right [SMul M α] [Preorder α] [CovariantClass M α HSMul.hSMul LE.le]
    (m : M) : Monotone (HSMul.hSMul m : α → α) :=
  sorry
@[gcongr]
theorem smul_le_smul_left [SMul M α] [Preorder α] [CovariantClass M α HSMul.hSMul LE.le]
    (m : M) {a b : α} (h : a ≤ b) :
    m • a ≤ m • b :=
  smul_mono_right _ h

@[target]
theorem smul_inf_le [SMul M α] [SemilatticeInf α] [CovariantClass M α HSMul.hSMul LE.le]
    (m : M) (a₁ a₂ : α) : m • (a₁ ⊓ a₂) ≤ m • a₁ ⊓ m • a₂ :=
  sorry

@[target]
theorem smul_iInf_le [SMul M α] [CompleteLattice α] [CovariantClass M α HSMul.hSMul LE.le]
    {m : M} {t : ι → α} :
    m • iInf t ≤ ⨅ i, m • t i :=
  sorry

theorem smul_strictMono_right [SMul M α] [Preorder α] [CovariantClass M α HSMul.hSMul LT.lt]
    (m : M) : StrictMono (HSMul.hSMul m : α → α) :=
  fun _ _ => CovariantClass.elim _

@[target]
lemma le_pow_smul {G : Type*} [Monoid G] {α : Type*} [Preorder α] {g : G} {a : α}
    [MulAction G α] [CovariantClass G α HSMul.hSMul LE.le]
    (h : a ≤ g • a) (n : ℕ) : a ≤ g ^ n • a := by sorry

@[target]
lemma pow_smul_le {G : Type*} [Monoid G] {α : Type*} [Preorder α] {g : G} {a : α}
    [MulAction G α] [CovariantClass G α HSMul.hSMul LE.le]
    (h : g • a ≤ a) (n : ℕ) : g ^ n • a ≤ a := by sorry