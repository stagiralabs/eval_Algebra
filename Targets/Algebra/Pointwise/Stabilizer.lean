import VerifiedAgora.tagger
/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Stabilizer of a set under a pointwise action

This file characterises the stabilizer of a set/finset under the pointwise action of a group.
-/

open Function MulOpposite Set
open scoped Pointwise

namespace MulAction
variable {G H α : Type*}

/-! ### Stabilizer of a set -/

section Set
section Group
variable [Group G] [Group H] [MulAction G α] {a : G} {s t : Set α}

@[target, to_additive (attr := sorry

@[to_additive (attr := simp)]
lemma stabilizer_univ : stabilizer G (Set.univ : Set α) = ⊤ := by
  ext
  simp

@[to_additive (attr := simp)]
lemma stabilizer_singleton (b : α) : stabilizer G ({b} : Set α) = stabilizer G b := by ext; simp

@[to_additive]
lemma mem_stabilizer_set {s : Set α} : a ∈ stabilizer G s ↔ ∀ b, a • b ∈ s ↔ b ∈ s := by
  refine mem_stabilizer_iff.trans ⟨fun h b ↦ ?_, fun h ↦ ?_⟩
  · rw [← (smul_mem_smul_set_iff : a • b ∈ _ ↔ _), h]
  simp_rw [Set.ext_iff, mem_smul_set_iff_inv_smul_mem]
  exact ((MulAction.toPerm a).forall_congr' <| by simp [Iff.comm]).1 h

@[to_additive]
lemma map_stabilizer_le (f : G →* H) (s : Set G) :
    (stabilizer G s).map f ≤ stabilizer H (f '' s) := by
  rintro a
  simp only [Subgroup.mem_map, mem_stabilizer_iff, exists_prop, forall_exists_index, and_imp]
  rintro a ha rfl
  rw [← image_smul_distrib, ha]

@[to_additive (attr := simp)]
lemma stabilizer_mul_self (s : Set G) : (stabilizer G s : Set G) * s = s := by
  ext
  refine ⟨?_, fun h ↦ ⟨_, (stabilizer G s).one_mem, _, h, one_mul _⟩⟩
  rintro ⟨a, ha, b, hb, rfl⟩
  rw [← mem_stabilizer_iff.1 ha]
  exact smul_mem_smul_set hb

@[target, to_additive]
lemma stabilizer_inf_stabilizer_le_stabilizer_apply₂ {f : Set α → Set α → Set α}
    (hf : ∀ a : G, a • f s t = f (a • s) (a • t)) :
    stabilizer G s ⊓ stabilizer G t ≤ stabilizer G (f s t) := by sorry

@[target, to_additive]
lemma stabilizer_inf_stabilizer_le_stabilizer_union :
    stabilizer G s ⊓ stabilizer G t ≤ stabilizer G (s ∪ t) :=
  sorry

@[to_additive]
lemma stabilizer_inf_stabilizer_le_stabilizer_inter :
    stabilizer G s ⊓ stabilizer G t ≤ stabilizer G (s ∩ t) :=
  stabilizer_inf_stabilizer_le_stabilizer_apply₂ fun _ ↦ smul_set_inter

@[target, to_additive]
lemma stabilizer_inf_stabilizer_le_stabilizer_sdiff :
    stabilizer G s ⊓ stabilizer G t ≤ stabilizer G (s \ t) :=
  sorry

@[target, to_additive]
lemma stabilizer_union_eq_left (hdisj : Disjoint s t) (hstab : stabilizer G s ≤ stabilizer G t)
    (hstab_union : stabilizer G (s ∪ t) ≤ stabilizer G t) :
    stabilizer G (s ∪ t) = stabilizer G s := by sorry

@[to_additive]
lemma stabilizer_union_eq_right (hdisj : Disjoint s t) (hstab : stabilizer G t ≤ stabilizer G s)
    (hstab_union : stabilizer G (s ∪ t) ≤ stabilizer G s)  :
    stabilizer G (s ∪ t) = stabilizer G t := by
  rw [union_comm, stabilizer_union_eq_left hdisj.symm hstab (union_comm .. ▸ hstab_union)]

variable {s : Set G}

open scoped RightActions in
@[target, to_additive]
lemma op_smul_set_stabilizer_subset (ha : a ∈ s) : (stabilizer G s : Set G) <• a ⊆ s :=
  sorry

@[target, to_additive]
lemma stabilizer_subset_div_right (ha : a ∈ s) : ↑(stabilizer G s) ⊆ s / {a} := sorry

@[to_additive]
lemma stabilizer_finite (hs₀ : s.Nonempty) (hs : s.Finite) : (stabilizer G s : Set G).Finite := by
  obtain ⟨a, ha⟩ := hs₀
  exact (hs.div <| finite_singleton _).subset <| stabilizer_subset_div_right ha

end Group

section CommGroup
variable [CommGroup G] {s t : Set G} {a : G}

@[target, to_additive]
lemma smul_set_stabilizer_subset (ha : a ∈ s) : a • (stabilizer G s : Set G) ⊆ s := by sorry

end CommGroup
end Set

variable [Group G] [Group H] [MulAction G α] {a : G}

/-! ### Stabilizer of a subgroup -/

section Subgroup

-- TODO: Is there a lemma that could unify the following three very similar lemmas?

@[to_additive (attr := simp)]
lemma stabilizer_subgroup (s : Subgroup G) : stabilizer G (s : Set G) = s := by
  simp_rw [SetLike.ext_iff, mem_stabilizer_set]
  refine fun a ↦ ⟨fun h ↦ ?_, fun ha b ↦ s.mul_mem_cancel_left ha⟩
  simpa only [smul_eq_mul, SetLike.mem_coe, mul_one] using (h 1).2 s.one_mem

@[target, to_additive (attr := by sorry

@[to_additive (attr := simp)]
lemma stabilizer_subgroup_op (s : Subgroup Gᵐᵒᵖ) : stabilizer G (s : Set Gᵐᵒᵖ) = s.unop := by
  simp_rw [SetLike.ext_iff, mem_stabilizer_set]
  refine fun a ↦ ⟨fun h ↦ ?_, fun ha b ↦ s.mul_mem_cancel_right ha⟩
  have : 1 * MulOpposite.op a ∈ s := (h 1).2 s.one_mem
  simpa only [op_smul_eq_mul, SetLike.mem_coe, one_mul] using this

end Subgroup

/-! ### Stabilizer of a finset -/

section Finset
variable [DecidableEq α]

@[target, to_additive (attr := by sorry

@[target, to_additive (attr := sorry

@[to_additive (attr := simp)]
lemma stabilizer_finset_univ [Fintype α] : stabilizer G (Finset.univ : Finset α) = ⊤ := by
  ext
  simp

@[to_additive (attr := simp)]
lemma stabilizer_finset_singleton (b : α) : stabilizer G ({b} : Finset α) = stabilizer G b := by
  ext; simp

@[to_additive]
lemma mem_stabilizer_finset {s : Finset α} : a ∈ stabilizer G s ↔ ∀ b, a • b ∈ s ↔ b ∈ s := by
  simp_rw [← stabilizer_coe_finset, mem_stabilizer_set, Finset.mem_coe]

@[to_additive]
lemma mem_stabilizer_finset_iff_subset_smul_finset {s : Finset α} :
    a ∈ stabilizer G s ↔ s ⊆ a • s := by
  rw [mem_stabilizer_iff, Finset.subset_iff_eq_of_card_le (Finset.card_smul_finset _ _).le, eq_comm]

@[target, to_additive]
lemma mem_stabilizer_finset_iff_smul_finset_subset {s : Finset α} :
    a ∈ stabilizer G s ↔ a • s ⊆ s := by sorry

@[target, to_additive]
lemma mem_stabilizer_finset' {s : Finset α} : a ∈ stabilizer G s ↔ ∀ ⦃b⦄, b ∈ s → a • b ∈ s := by sorry

end Finset

/-! ### Stabilizer of a finite set -/

variable {s : Set α}

@[target, to_additive]
lemma mem_stabilizer_set_iff_subset_smul_set {s : Set α} (hs : s.Finite) :
    a ∈ stabilizer G s ↔ s ⊆ a • s := by sorry

@[to_additive]
lemma mem_stabilizer_set_iff_smul_set_subset {s : Set α} (hs : s.Finite) :
    a ∈ stabilizer G s ↔ a • s ⊆ s := by
  lift s to Finset α using hs
  classical
  rw [stabilizer_coe_finset, mem_stabilizer_finset_iff_smul_finset_subset, ← Finset.coe_smul_finset,
    Finset.coe_subset]

@[deprecated (since := "2024-11-25")]
alias mem_stabilizer_of_finite_iff_smul_le := mem_stabilizer_set_iff_subset_smul_set

@[deprecated (since := "2024-11-25")]
alias mem_stabilizer_of_finite_iff_le_smul := mem_stabilizer_set_iff_smul_set_subset

@[target, to_additive]
lemma mem_stabilizer_set' {s : Set α} (hs : s.Finite) :
    a ∈ stabilizer G s ↔ ∀ ⦃b⦄, b ∈ s → a • b ∈ s := by sorry

end MulAction

/-! ### Stabilizer in a commutative group -/

namespace MulAction
variable {G : Type*} [CommGroup G] (s : Set G)

@[to_additive (attr := simp)]
lemma mul_stabilizer_self : s * stabilizer G s = s := by rw [mul_comm, stabilizer_mul_self]

local notation " Q " => G ⧸ stabilizer G s
local notation " q " => ((↑) : G → Q)

@[target, to_additive]
lemma stabilizer_image_coe_quotient : stabilizer Q (q '' s) = ⊥ := by sorry

end MulAction
