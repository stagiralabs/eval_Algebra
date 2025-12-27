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

@[target] lemma stabilizer_univ : stabilizer G (Set.univ : Set α) = ⊤ := by
  sorry


@[to_additive (attr := simp)]
lemma stabilizer_singleton (b : α) : stabilizer G ({b} : Set α) = stabilizer G b := by ext; simp

@[target] lemma mem_stabilizer_set {s : Set α} : a ∈ stabilizer G s ↔ ∀ b, a • b ∈ s ↔ b ∈ s := by
  sorry


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

@[to_additive]
lemma stabilizer_inf_stabilizer_le_stabilizer_apply₂ {f : Set α → Set α → Set α}
    (hf : ∀ a : G, a • f s t = f (a • s) (a • t)) :
    stabilizer G s ⊓ stabilizer G t ≤ stabilizer G (f s t) := by aesop (add simp [SetLike.le_def])

@[target] lemma stabilizer_inf_stabilizer_le_stabilizer_union :
    stabilizer G s ⊓ stabilizer G t ≤ stabilizer G (s ∪ t) := by sorry


@[target] lemma stabilizer_inf_stabilizer_le_stabilizer_inter :
    stabilizer G s ⊓ stabilizer G t ≤ stabilizer G (s ∩ t) := by sorry


@[to_additive]
lemma stabilizer_inf_stabilizer_le_stabilizer_sdiff :
    stabilizer G s ⊓ stabilizer G t ≤ stabilizer G (s \ t) :=
  stabilizer_inf_stabilizer_le_stabilizer_apply₂ fun _ ↦ smul_set_sdiff

@[target] lemma stabilizer_union_eq_left (hdisj : Disjoint s t) (hstab : stabilizer G s ≤ stabilizer G t)
    (hstab_union : stabilizer G (s ∪ t) ≤ stabilizer G t) :
    stabilizer G (s ∪ t) = stabilizer G s := by
  sorry


@[target] lemma stabilizer_union_eq_right (hdisj : Disjoint s t) (hstab : stabilizer G t ≤ stabilizer G s)
    (hstab_union : stabilizer G (s ∪ t) ≤ stabilizer G s)  :
    stabilizer G (s ∪ t) = stabilizer G t := by
  sorry


variable {s : Set G}

open scoped RightActions in
open scoped RightActions in
@[target] lemma op_smul_set_stabilizer_subset (ha : a ∈ s) : (stabilizer G s : Set G) <• a ⊆ s :=
  smul_set_subset_iff.2 fun b hb ↦ by sorry


@[target] lemma stabilizer_subset_div_right (ha : a ∈ s) : ↑(stabilizer G s) ⊆ s / {a} := fun b hb ↦
  ⟨_, by sorry


@[target] lemma stabilizer_finite (hs₀ : s.Nonempty) (hs : s.Finite) : (stabilizer G s : Set G).Finite := by
  sorry


end Group

section CommGroup
variable [CommGroup G] {s t : Set G} {a : G}

@[target] lemma smul_set_stabilizer_subset (ha : a ∈ s) : a • (stabilizer G s : Set G) ⊆ s := by
  sorry


end CommGroup
end Set

variable [Group G] [Group H] [MulAction G α] {a : G}

/-! ### Stabilizer of a subgroup -/

section Subgroup

-- TODO: Is there a lemma that could unify the following three very similar lemmas?

@[target] lemma stabilizer_subgroup (s : Subgroup G) : stabilizer G (s : Set G) = s := by
  sorry


@[target] lemma stabilizer_op_subgroup (s : Subgroup G) : stabilizer Gᵐᵒᵖ (s : Set G) = s.op := by
  sorry


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

@[target] lemma stabilizer_coe_finset (s : Finset α) : stabilizer G (s : Set α) = stabilizer G s := by
  sorry


@[to_additive (attr := by sorry


@[target] lemma stabilizer_finset_univ [Fintype α] : stabilizer G (Finset.univ : Finset α) = ⊤ := by
  sorry


@[target] lemma stabilizer_finset_singleton (b : α) : stabilizer G ({b} : Finset α) = stabilizer G b := by
  sorry


@[target] lemma mem_stabilizer_finset {s : Finset α} : a ∈ stabilizer G s ↔ ∀ b, a • b ∈ s ↔ b ∈ s := by
  sorry


@[target] lemma mem_stabilizer_finset_iff_subset_smul_finset {s : Finset α} :
    a ∈ stabilizer G s ↔ s ⊆ a • s := by
  sorry


@[target] lemma mem_stabilizer_finset_iff_smul_finset_subset {s : Finset α} :
    a ∈ stabilizer G s ↔ a • s ⊆ s := by
  sorry


@[to_additive]
lemma mem_stabilizer_finset' {s : Finset α} : a ∈ stabilizer G s ↔ ∀ ⦃b⦄, b ∈ s → a • b ∈ s := by
  rw [← Subgroup.inv_mem_iff, mem_stabilizer_finset_iff_subset_smul_finset]
  simp_rw [← Finset.mem_inv_smul_finset_iff, Finset.subset_iff]

end Finset

/-! ### Stabilizer of a finite set -/

variable {s : Set α}

@[target] lemma mem_stabilizer_set_iff_subset_smul_set {s : Set α} (hs : s.Finite) :
    a ∈ stabilizer G s ↔ s ⊆ a • s := by
  sorry

  classical
  rw [stabilizer_coe_finset, mem_stabilizer_finset_iff_subset_smul_finset, ← Finset.coe_smul_finset,
    Finset.coe_subset]

@[target] lemma mem_stabilizer_set_iff_smul_set_subset {s : Set α} (hs : s.Finite) :
    a ∈ stabilizer G s ↔ a • s ⊆ s := by
  sorry

  classical
  rw [stabilizer_coe_finset, mem_stabilizer_finset_iff_smul_finset_subset, ← Finset.coe_smul_finset,
    Finset.coe_subset]

@[deprecated (since := "2024-11-25")]
alias mem_stabilizer_of_finite_iff_smul_le := mem_stabilizer_set_iff_subset_smul_set

@[deprecated (since := "2024-11-25")]
alias mem_stabilizer_of_finite_iff_le_smul := mem_stabilizer_set_iff_smul_set_subset

@[to_additive]
lemma mem_stabilizer_set' {s : Set α} (hs : s.Finite) :
    a ∈ stabilizer G s ↔ ∀ ⦃b⦄, b ∈ s → a • b ∈ s := by
  lift s to Finset α using hs
  classical simp [-mem_stabilizer_iff, mem_stabilizer_finset']

end MulAction

/-! ### Stabilizer in a commutative group -/

namespace MulAction
variable {G : Type*} [CommGroup G] (s : Set G)

@[target] lemma mul_stabilizer_self : s * stabilizer G s = s := by sorry


@[target] lemma stabilizer_image_coe_quotient : stabilizer Q (q '' s) = ⊥ := by
  sorry


end MulAction
