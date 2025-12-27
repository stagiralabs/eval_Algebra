import VerifiedAgora.tagger
/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Jireh Loreaux
-/
import Mathlib.Algebra.Group.Commute.Units
import Mathlib.Algebra.Group.Invertible.Basic
import Mathlib.Logic.Basic
import Mathlib.Data.Set.Basic

/-!
# Centers of magmas and semigroups

## Main definitions

* `Set.center`: the center of a magma
* `Set.addCenter`: the center of an additive magma
* `Set.centralizer`: the centralizer of a subset of a magma
* `Set.addCentralizer`: the centralizer of a subset of an additive magma

## See also

See `Mathlib.GroupTheory.Subsemigroup.Center` for the definition of the center as a subsemigroup:
* `Subsemigroup.center`: the center of a semigroup
* `AddSubsemigroup.center`: the center of an additive semigroup

We provide `Submonoid.center`, `AddSubmonoid.center`, `Subgroup.center`, `AddSubgroup.center`,
`Subsemiring.center`, and `Subring.center` in other files.

See `Mathlib.GroupTheory.Subsemigroup.Centralizer` for the definition of the centralizer
as a subsemigroup:
* `Subsemigroup.centralizer`: the centralizer of a subset of a semigroup
* `AddSubsemigroup.centralizer`: the centralizer of a subset of an additive semigroup

We provide `Monoid.centralizer`, `AddMonoid.centralizer`, `Subgroup.centralizer`, and
`AddSubgroup.centralizer` in other files.
-/

assert_not_exists RelIso Finset MonoidWithZero Subsemigroup

variable {M : Type*} {S T : Set M}

/-- Conditions for an element to be additively central -/
structure IsAddCentral [Add M] (z : M) : Prop where
  /-- addition commutes -/
  comm (a : M) : z + a = a + z
  /-- associative property for left addition -/
  left_assoc (b c : M) : z + (b + c) = (z + b) + c
  /-- middle associative addition property -/
  mid_assoc (a c : M) : (a + z) + c = a + (z + c)
  /-- associative property for right addition -/
  right_assoc (a b : M) : (a + b) + z = a + (b + z)

/-- Conditions for an element to be multiplicatively central -/
@[to_additive]
structure IsMulCentral [Mul M] (z : M) : Prop where
  /-- multiplication commutes -/
  comm (a : M) : z * a = a * z
  /-- associative property for left multiplication -/
  left_assoc (b c : M) : z * (b * c) = (z * b) * c
  /-- middle associative multiplication property -/
  mid_assoc (a c : M) : (a * z) * c = a * (z * c)
  /-- associative property for right multiplication -/
  right_assoc (a b : M) : (a * b) * z = a * (b * z)

attribute [mk_iff] IsMulCentral IsAddCentral
attribute [to_additive existing] isMulCentral_iff

namespace IsMulCentral

variable {a c : M} [Mul M]

-- cf. `Commute.left_comm`
@[to_additive]
protected theorem left_comm (h : IsMulCentral a) (b c) : a * (b * c) = b * (a * c) := by
  simp only [h.comm, h.right_assoc]

-- cf. `Commute.right_comm`
@[to_additive]
protected theorem right_comm (h : IsMulCentral c) (a b) : a * b * c = a * c * b := by
  simp only [h.right_assoc, h.mid_assoc, h.comm]

end IsMulCentral

namespace Set

/-! ### Center -/

section Mul
variable [Mul M]

variable (M) in
/-- The center of a magma. -/
variable (M) in
/-- The center of a magma. -/
@[to_additive addCenter " The center of an additive magma. "]
def center : Set M := by sorry


variable (S) in
/-- The centralizer of a subset of a magma. -/
variable (S) in
/-- The centralizer of a subset of a magma. -/
@[to_additive addCentralizer " The centralizer of a subset of an additive magma. "]
def centralizer : Set M := by sorry


@[target] lemma _root_.NonUnitalNonAssocSemiring.mem_center_iff (a : α) :
    a ∈ NonUnitalSubsemiring.center α ↔ R a = L a ∧ (L a) ∈ RingHom.rangeS (toEndRingHom α) := by
  sorry


@[to_additive mem_addCentralizer]
lemma mem_centralizer_iff {c : M} : c ∈ centralizer S ↔ ∀ m ∈ S, m * c = c * m := Iff.rfl

@[target] theorem mul_mem_center {z₁ z₂ : M} (hz₁ : z₁ ∈ Set.center M) (hz₂ : z₂ ∈ Set.center M) :
    z₁ * z₂ ∈ Set.center M where
  comm a := calc
    z₁ * z₂ * a = z₂ * z₁ * a := by sorry


@[to_additive addCenter_subset_addCentralizer]
lemma center_subset_centralizer (S : Set M) : Set.center M ⊆ S.centralizer :=
  fun _ hx m _ ↦ (hx.comm m).symm

@[to_additive addCentralizer_union]
lemma centralizer_union : centralizer (S ∪ T) = centralizer S ∩ centralizer T := by
  simp [centralizer, or_imp, forall_and, setOf_and]

@[target] lemma subset_centralizer_centralizer : S ⊆ S.centralizer.centralizer := by
  sorry


@[to_additive (attr := simp) addCentralizer_addCentralizer_addCentralizer]
lemma centralizer_centralizer_centralizer (S : Set M) :
    S.centralizer.centralizer.centralizer = S.centralizer := by
  refine Set.Subset.antisymm ?_ Set.subset_centralizer_centralizer
  intro x hx
  rw [Set.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_centralizer_iff] at hx
  exact hx y <| Set.subset_centralizer_centralizer hy

@[to_additive decidableMemAddCentralizer]
instance decidableMemCentralizer [∀ a : M, Decidable <| ∀ b ∈ S, b * a = a * b] :
    DecidablePred (· ∈ centralizer S) := fun _ ↦ decidable_of_iff' _ mem_centralizer_iff

@[target] lemma centralizer_centralizer_comm_of_comm (h_comm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) :
    ∀ x ∈ S.centralizer.centralizer, ∀ y ∈ S.centralizer.centralizer, x * y = y * x := by sorry


end Mul

section Semigroup
variable [Semigroup M] {a b : M}

@[to_additive]
theorem _root_.Semigroup.mem_center_iff {z : M} :
    z ∈ Set.center M ↔ ∀ g, g * z = z * g := ⟨fun a g ↦ by rw [IsMulCentral.comm a g],
  fun h ↦ ⟨fun _ ↦ (Commute.eq (h _)).symm, fun _ _ ↦ (mul_assoc z _ _).symm,
  fun _ _ ↦ mul_assoc _ z _, fun _ _ ↦ mul_assoc _ _ z⟩ ⟩

@[target] lemma mul_mem_centralizer (ha : a ∈ centralizer S) (hb : b ∈ centralizer S) :
    a * b ∈ centralizer S := fun g hg ↦ by
  sorry


@[target] theorem centralizer_eq_top_iff_subset : centralizer S = Set.univ ↔ S ⊆ center M :=
  eq_top_iff.trans <| ⟨
    fun h _ hx ↦ Semigroup.mem_center_iff.mpr fun _ ↦ by sorry


variable (M) in
variable (M) in
@[to_additive (attr := by sorry

@[to_additive decidableMemAddCenter]
instance decidableMemCenter [∀ a : M, Decidable <| ∀ b : M, b * a = a * b] :
    DecidablePred (· ∈ center M) := fun _ => decidable_of_iff' _ (Semigroup.mem_center_iff)

end Semigroup

section CommSemigroup
variable [CommSemigroup M]

variable (M)

@[to_additive (attr := by sorry


@[to_additive (attr := by sorry


end CommSemigroup

section MulOneClass
variable [MulOneClass M]

@[target] theorem one_mem_center : (1 : M) ∈ Set.center M where
  comm _  := by sorry


@[target] lemma one_mem_centralizer : (1 : M) ∈ centralizer S := by sorry


end MulOneClass

section Monoid
variable [Monoid M]

@[target] theorem subset_center_units : ((↑) : Mˣ → M) ⁻¹' center M ⊆ Set.center Mˣ :=
  fun _ ha => by
  sorry


@[target] theorem units_inv_mem_center {a : Mˣ} (ha : ↑a ∈ Set.center M) : ↑a⁻¹ ∈ Set.center M := by
  sorry


@[target] theorem invOf_mem_center {a : M} [Invertible a] (ha : a ∈ Set.center M) : ⅟a ∈ Set.center M := by
  sorry


end Monoid

section DivisionMonoid
variable [DivisionMonoid M] {a b : M}

@[target] theorem inv_mem_center (ha : a ∈ Set.center M) : a⁻¹ ∈ Set.center M := by
  sorry


@[target] theorem div_mem_center (ha : a ∈ Set.center M) (hb : b ∈ Set.center M) : a / b ∈ Set.center M := by
  sorry


end DivisionMonoid

section Group
variable [Group M] {a b : M}

@[target] lemma inv_mem_centralizer (ha : a ∈ centralizer S) : a⁻¹ ∈ centralizer S :=
  fun g hg ↦ by sorry


@[to_additive (attr := simp) sub_mem_addCentralizer]
lemma div_mem_centralizer (ha : a ∈ centralizer S) (hb : b ∈ centralizer S) :
    a / b ∈ centralizer S := by
  simpa only [div_eq_mul_inv] using mul_mem_centralizer ha (inv_mem_centralizer hb)

end Group
end Set
