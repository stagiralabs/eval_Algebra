import VerifiedAgora.tagger
/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard,
Amelia Livingston, Yury Kudryashov, Yakov Pechersky
-/
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.InjSurj
import Mathlib.Data.SetLike.Basic
import Mathlib.Tactic.FastInstance

/-!
# Subsemigroups: definition

This file defines bundled multiplicative and additive subsemigroups.

## Main definitions

* `Subsemigroup M`: the type of bundled subsemigroup of a magma `M`; the underlying set is given in
  the `carrier` field of the structure, and should be accessed through coercion as in `(S : Set M)`.
* `AddSubsemigroup M` : the type of bundled subsemigroups of an additive magma `M`.

For each of the following definitions in the `Subsemigroup` namespace, there is a corresponding
definition in the `AddSubsemigroup` namespace.

* `Subsemigroup.copy` : copy of a subsemigroup with `carrier` replaced by a set that is equal but
  possibly not definitionally equal to the carrier of the original `Subsemigroup`.

Similarly, for each of these definitions in the `MulHom` namespace, there is a corresponding
definition in the `AddHom` namespace.

* `MulHom.eqLocus f g`: the subsemigroup of those `x` such that `f x = g x`

## Implementation notes

Subsemigroup inclusion is denoted `≤` rather than `⊆`, although `∈` is defined as
membership of a subsemigroup's underlying set.

Note that `Subsemigroup M` does not actually require `Semigroup M`,
instead requiring only the weaker `Mul M`.

This file is designed to have very few dependencies. In particular, it should not use natural
numbers.

## Tags
subsemigroup, subsemigroups
-/

assert_not_exists RelIso CompleteLattice MonoidWithZero

variable {M : Type*} {N : Type*}

section NonAssoc

variable [Mul M] {s : Set M}

/-- `MulMemClass S M` says `S` is a type of sets `s : Set M` that are closed under `(*)` -/
class MulMemClass (S : Type*) (M : outParam Type*) [Mul M] [SetLike S M] : Prop where
  /-- A substructure satisfying `MulMemClass` is closed under multiplication. -/
  mul_mem : ∀ {s : S} {a b : M}, a ∈ s → b ∈ s → a * b ∈ s

export MulMemClass (mul_mem)

/-- `AddMemClass S M` says `S` is a type of sets `s : Set M` that are closed under `(+)` -/
class AddMemClass (S : Type*) (M : outParam Type*) [Add M] [SetLike S M] : Prop where
  /-- A substructure satisfying `AddMemClass` is closed under addition. -/
  add_mem : ∀ {s : S} {a b : M}, a ∈ s → b ∈ s → a + b ∈ s

export AddMemClass (add_mem)

attribute [to_additive] MulMemClass

attribute [aesop safe apply (rule_sets := [SetLike])] mul_mem add_mem

/-- A subsemigroup of a magma `M` is a subset closed under multiplication. -/
structure Subsemigroup (M : Type*) [Mul M] where
  /-- The carrier of a subsemigroup. -/
  carrier : Set M
  /-- The product of two elements of a subsemigroup belongs to the subsemigroup. -/
  mul_mem' {a b} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier

/-- An additive subsemigroup of an additive magma `M` is a subset closed under addition. -/
structure AddSubsemigroup (M : Type*) [Add M] where
  /-- The carrier of an additive subsemigroup. -/
  carrier : Set M
  /-- The sum of two elements of an additive subsemigroup belongs to the subsemigroup. -/
  add_mem' {a b} : a ∈ carrier → b ∈ carrier → a + b ∈ carrier

attribute [to_additive AddSubsemigroup] Subsemigroup

namespace Subsemigroup

@[to_additive]
instance : SetLike (Subsemigroup M) M :=
  ⟨Subsemigroup.carrier, fun p q h => by cases p; cases q; congr⟩

@[to_additive]
instance : MulMemClass (Subsemigroup M) M where mul_mem := fun {_ _ _} => Subsemigroup.mul_mem' _

initialize_simps_projections Subsemigroup (carrier → coe, as_prefix coe)
initialize_simps_projections AddSubsemigroup (carrier → coe, as_prefix coe)

@[to_additive (attr := simp)]
theorem mem_carrier {s : Subsemigroup M} {x : M} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl

@[to_additive (attr := simp)]
theorem mem_mk {s : Set M} {x : M} (h_mul) : x ∈ mk s h_mul ↔ x ∈ s :=
  Iff.rfl

@[to_additive (attr := simp, norm_cast)]
theorem coe_set_mk (s : Set M) (h_mul) : (mk s h_mul : Set M) = s :=
  rfl

@[to_additive (attr := simp)]
theorem mk_le_mk {s t : Set M} (h_mul) (h_mul') : mk s h_mul ≤ mk t h_mul' ↔ s ⊆ t :=
  Iff.rfl

/-- Two subsemigroups are equal if they have the same elements. -/
@[target] theorem Algebra.ext {S : Type u} {A : Type v} [CommSemiring S] [Semiring A] (h1 h2 : Algebra S A)
    (h : ∀ (r : S) (x : A), (by sorry


/-- Copy a subsemigroup replacing `carrier` with a set that is equal to it. -/
@[to_additive "Copy an additive subsemigroup replacing `carrier` with a set that is equal to it."]
protected def copy (S : Subsemigroup M) (s : Set M) (hs : s = S) :
    Subsemigroup M where
  carrier := s
  mul_mem' := hs.symm ▸ S.mul_mem'

variable {S : Subsemigroup M}

@[target] theorem coe_copy (f : CentroidHom α) (f' : α → α) (h : f' = f) : ⇑(f.copy f' h) = f' := by sorry


@[target] theorem copy_eq (f : CentroidHom α) (f' : α → α) (h : f' = f) : f.copy f' h = f := by sorry


variable (S)

/-- A subsemigroup is closed under multiplication. -/
@[to_additive "An `AddSubsemigroup` is closed under addition."]
protected theorem mul_mem {x y : M} : x ∈ S → y ∈ S → x * y ∈ S :=
  Subsemigroup.mul_mem' S

/-- The subsemigroup `M` of the magma `M`. -/
@[to_additive "The additive subsemigroup `M` of the magma `M`."]
instance : Top (Subsemigroup M) :=
  ⟨{  carrier := Set.univ
      mul_mem' := fun _ _ => Set.mem_univ _ }⟩

/-- The trivial subsemigroup `∅` of a magma `M`. -/
@[to_additive "The trivial `AddSubsemigroup` `∅` of an additive magma `M`."]
instance : Bot (Subsemigroup M) :=
  ⟨{  carrier := ∅
      mul_mem' := False.elim }⟩

@[to_additive]
instance : Inhabited (Subsemigroup M) :=
  ⟨⊥⟩

@[to_additive]
theorem not_mem_bot {x : M} : x ∉ (⊥ : Subsemigroup M) :=
  Set.not_mem_empty x

@[to_additive (attr := simp)]
theorem mem_top (x : M) : x ∈ (⊤ : Subsemigroup M) :=
  Set.mem_univ x

@[to_additive (attr := simp)]
theorem coe_top : ((⊤ : Subsemigroup M) : Set M) = Set.univ :=
  rfl

@[to_additive (attr := simp)]
theorem coe_bot : ((⊥ : Subsemigroup M) : Set M) = ∅ :=
  rfl

/-- The inf of two subsemigroups is their intersection. -/
@[to_additive "The inf of two `AddSubsemigroup`s is their intersection."]
instance : Min (Subsemigroup M) :=
  ⟨fun S₁ S₂ =>
    { carrier := S₁ ∩ S₂
      mul_mem' := fun ⟨hx, hx'⟩ ⟨hy, hy'⟩ => ⟨S₁.mul_mem hx hy, S₂.mul_mem hx' hy'⟩ }⟩

@[to_additive (attr := simp)]
theorem coe_inf (p p' : Subsemigroup M) : ((p ⊓ p' : Subsemigroup M) : Set M) = (p : Set M) ∩ p' :=
  rfl

@[to_additive (attr := simp)]
theorem mem_inf {p p' : Subsemigroup M} {x : M} : x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' :=
  Iff.rfl

@[to_additive]
theorem subsingleton_of_subsingleton [Subsingleton (Subsemigroup M)] : Subsingleton M := by
  constructor; intro x y
  have : ∀ a : M, a ∈ (⊥ : Subsemigroup M) := by simp [Subsingleton.elim (⊥ : Subsemigroup M) ⊤]
  exact absurd (this x) not_mem_bot

@[to_additive]
instance [hn : Nonempty M] : Nontrivial (Subsemigroup M) :=
  ⟨⟨⊥, ⊤, fun h => by
      obtain ⟨x⟩ := id hn
      refine absurd (?_ : x ∈ ⊥) not_mem_bot
      simp [h]⟩⟩

end Subsemigroup

namespace MulHom

variable [Mul N]

open Subsemigroup

/-- The subsemigroup of elements `x : M` such that `f x = g x` -/
/-- A linear map version of `AddMonoidHom.eqLocusM` -/
def eqLocus (f g : F) : Submodule R M :=
  { (f : M →+ M₂).eqLocusM g with
    carrier := { x | f x = g x }
    smul_mem' := fun {r} {x} (hx : _ = _) => show _ = _ by
      -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 changed `map_smulₛₗ` into `map_smulₛₗ _`
      sorry


@[to_additive]
theorem eq_of_eqOn_top {f g : M →ₙ* N} (h : Set.EqOn f g (⊤ : Subsemigroup M)) : f = g :=
  ext fun _ => h trivial

end MulHom

end NonAssoc

namespace MulMemClass

variable {A : Type*} [Mul M] [SetLike A M] [hA : MulMemClass A M] (S' : A)

-- lower priority so other instances are found first
/-- A submagma of a magma inherits a multiplication. -/
@[to_additive "An additive submagma of an additive magma inherits an addition."]
instance (priority := 900) mul : Mul S' :=
  ⟨fun a b => ⟨a.1 * b.1, mul_mem a.2 b.2⟩⟩

-- lower priority so later simp lemmas are used first; to appease simp_nf
@[target] theorem coe_mul (a b : R) : (↑(a * b : R) : A) = ↑a * ↑b := by sorry

@[target] theorem mk_mul_mk {x y : M} : Associates.mk x * Associates.mk y = Associates.mk (x * y) := by sorry


@[target] theorem mul_def {f g : MonoidAlgebra k G} :
    f * g = f.sum fun a₁ b₁ => g.sum fun a₂ b₂ => single (a₁ * a₂) (b₁ * b₂) := by
  sorry


/-- A subsemigroup of a semigroup inherits a semigroup structure. -/
@[to_additive "An `AddSubsemigroup` of an `AddSemigroup` inherits an `AddSemigroup` structure."]
instance toSemigroup {M : Type*} [Semigroup M] {A : Type*} [SetLike A M] [MulMemClass A M]
    (S : A) : Semigroup S := fast_instance%
  Subtype.coe_injective.semigroup Subtype.val fun _ _ => rfl

/-- A subsemigroup of a `CommSemigroup` is a `CommSemigroup`. -/
@[to_additive "An `AddSubsemigroup` of an `AddCommSemigroup` is an `AddCommSemigroup`."]
instance toCommSemigroup {M} [CommSemigroup M] {A : Type*} [SetLike A M] [MulMemClass A M]
    (S : A) : CommSemigroup S := fast_instance%
  Subtype.coe_injective.commSemigroup Subtype.val fun _ _ => rfl

/-- The natural semigroup hom from a subsemigroup of semigroup `M` to `M`. -/
/-- The natural `R`-linear map from a submodule of an `R`-module `M` to `M`. -/
protected def subtype : S' →ₗ[R] M where
  toFun := by sorry


variable {S'} in
variable {S'} in
@[target] lemma subtype_apply (x : S') :
    SMulMemClass.subtype S' x = x := by sorry


@[target] lemma subtype_injective :
    Function.Injective (SMulMemClass.subtype S') := by sorry


@[simp]
protected theorem coe_subtype : (SMulMemClass.subtype S' : S' → M) = Subtype.val := by sorry


end MulMemClass
