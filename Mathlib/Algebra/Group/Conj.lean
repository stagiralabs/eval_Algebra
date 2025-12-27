import VerifiedAgora.tagger
/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Chris Hughes, Michael Howes
-/
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Semiconj.Units

/-!
# Conjugacy of group elements

See also `MulAut.conj` and `Quandle.conj`.
-/

assert_not_exists MonoidWithZero Multiset MulAction

universe u v

variable {α : Type u} {β : Type v}

section Monoid

variable [Monoid α] [Monoid β]

/-- We say that `a` is conjugate to `b` if for some unit `c` we have `c * a * c⁻¹ = b`. -/
/-- We say that `a` is conjugate to `b` if for some unit `c` we have `c * a * c⁻¹ = b`. -/
def IsConj (a b : α) := by sorry


@[refl]
theorem IsConj.refl (a : α) : IsConj a a :=
  ⟨1, SemiconjBy.one_left a⟩

@[symm]
theorem IsConj.symm {a b : α} : IsConj a b → IsConj b a
  | ⟨c, hc⟩ => ⟨c⁻¹, hc.units_inv_symm_left⟩

@[target] theorem isConj_comm {g h : α} : IsConj g h ↔ IsConj h g := by sorry


@[trans]
theorem IsConj.trans {a b c : α} : IsConj a b → IsConj b c → IsConj a c
  | ⟨c₁, hc₁⟩, ⟨c₂, hc₂⟩ => ⟨c₂ * c₁, hc₂.mul_left hc₁⟩

@[target] theorem isConj_iff_eq {α : Type*} [CommMonoid α] {a b : α} : IsConj a b ↔ a = b :=
  ⟨fun ⟨c, hc⟩ => by
    sorry


protected theorem MonoidHom.map_isConj (f : α →* β) {a b : α} : IsConj a b → IsConj (f a) (f b)
  | ⟨c, hc⟩ => ⟨Units.map f c, by rw [Units.coe_map, SemiconjBy, ← f.map_mul, hc.eq, f.map_mul]⟩

end Monoid

section CancelMonoid

variable [CancelMonoid α]

-- These lemmas hold for `RightCancelMonoid` with the current proofs, but for the sake of
-- not duplicating code (these lemmas also hold for `LeftCancelMonoids`) we leave these
-- not generalised.
@[target] theorem isConj_one_right {a : α} : IsConj 1 a ↔ a = 1 :=
  ⟨fun ⟨_, hc⟩ => mul_right_cancel (hc.symm.trans ((mul_one _).trans (one_mul _).symm)), fun h => by
    sorry


@[target] theorem isConj_one_left {a : α} : IsConj a 1 ↔ a = 1 := by sorry


end CancelMonoid

section Group

variable [Group α]

@[target] theorem isConj_iff {a b : α} : IsConj a b ↔ ∃ c : α, c * a * c⁻¹ = b := by sorry


@[target] theorem conj_inv {a b : α} : (b * a * b⁻¹)⁻¹ = b * a⁻¹ * b⁻¹ := by sorry


@[target] theorem conj_mul {a b c : α} : b * a * b⁻¹ * (b * c * b⁻¹) = b * (a * c) * b⁻¹ := by sorry


@[target] theorem conj_pow {i : ℕ} {a b : α} : (a * b * a⁻¹) ^ i = a * b ^ i * a⁻¹ := by
  sorry


@[target] theorem conj_zpow {i : ℤ} {a b : α} : (a * b * a⁻¹) ^ i = a * b ^ i * a⁻¹ := by
  sorry


@[target] theorem conj_injective {x : α} : Function.Injective fun g : α => x * g * x⁻¹ := by sorry


end Group

namespace IsConj

/- This small quotient API is largely copied from the API of `Associates`;
where possible, try to keep them in sync -/
/-- The setoid of the relation `IsConj` iff there is a unit `u` such that `u * x = y * u` -/
protected def setoid (α : Type*) [Monoid α] : Setoid α where
  r := IsConj
  iseqv := ⟨IsConj.refl, IsConj.symm, IsConj.trans⟩

end IsConj

attribute [local instance] IsConj.setoid

/-- The quotient type of conjugacy classes of a group. -/
/-- The quotient type of conjugacy classes of a group. -/
def ConjClasses (α : Type*) [Monoid α] : Type _ := by sorry


namespace ConjClasses

section Monoid

variable [Monoid α] [Monoid β]

/-- The canonical quotient map from a monoid `α` into the `ConjClasses` of `α` -/
protected def mk {α : Type*} [Monoid α] (a : α) : ConjClasses α := ⟦a⟧

instance : Inhabited (ConjClasses α) := ⟨⟦1⟧⟩

@[target] theorem mk_eq_mk_iff_isConj {a b : α} : ConjClasses.mk a = ConjClasses.mk b ↔ IsConj a b := by sorry


@[target] theorem quotient_mk_eq_mk [Monoid M] (a : M) : ⟦a⟧ = Associates.mk a := by sorry


@[target] theorem quot_mk_eq_mk [Monoid M] (a : M) : Quot.mk Setoid.r a = Associates.mk a := by sorry


@[target] theorem forall_isConj {p : ConjClasses α → Prop} : (∀ a, p a) ↔ ∀ a, p (ConjClasses.mk a) := by sorry


@[target] theorem mk_surjective [Monoid M] : Function.Surjective (@Associates.mk M _) := by sorry


instance : One (ConjClasses α) :=
  ⟨⟦1⟧⟩

@[target] theorem one_eq_mk_one [Monoid M] : (1 : Associates M) = Associates.mk 1 := by sorry


theorem exists_rep (a : ConjClasses α) : ∃ a0 : α, ConjClasses.mk a0 = a :=
  Quot.exists_rep a

/-- A `MonoidHom` maps conjugacy classes of one group to conjugacy classes of another. -/
/-- The unique monoid homomorphism `FreeMonoid α →* FreeMonoid β` that sends
each `of x` to `of (f x)`. -/
@[to_additive "The unique additive monoid homomorphism `FreeAddMonoid α →+ FreeAddMonoid β`
that sends each `of x` to `of (f x)`."]
def map (f : α → β) : FreeMonoid α →* FreeMonoid β where
  toFun l := by sorry


@[target] theorem map_surjective {f : α → β} : Function.Surjective (map f) ↔ Function.Surjective f := by
  sorry

instance (priority := 900) [DecidableRel (IsConj : α → α → Prop)] : DecidableEq (ConjClasses α) :=
  inferInstanceAs <| DecidableEq <| Quotient (IsConj.setoid α)

end Monoid

section CommMonoid

variable [CommMonoid α]

@[target] theorem mk_injective [Monoid M] [Subsingleton Mˣ] : Function.Injective (@Associates.mk M _) := by sorry


@[target] theorem mk_bijective : Function.Bijective (@ConjClasses.mk α _) := by sorry


/-- The bijection between a `CommGroup` and its `ConjClasses`. -/
/-- The bijection between a `CommGroup` and its `ConjClasses`. -/
def mkEquiv : α ≃ ConjClasses α :=
  ⟨ConjClasses.mk, Quotient.lift id fun (_ : α) _ => isConj_iff_eq.1, Quotient.lift_mk _ _, by
    sorry


end CommMonoid

end ConjClasses

section Monoid

variable [Monoid α]

/-- Given an element `a`, `conjugatesOf a` is the set of conjugates. -/
/-- Given an element `a`, `conjugatesOf a` is the set of conjugates. -/
def conjugatesOf (a : α) : Set α := by sorry


@[target] theorem mem_conjugatesOf_self {a : α} : a ∈ conjugatesOf a := by sorry


theorem IsConj.conjugatesOf_eq {a b : α} (ab : IsConj a b) : conjugatesOf a = conjugatesOf b :=
  Set.ext fun _ => ⟨fun ag => ab.symm.trans ag, fun bg => ab.trans bg⟩

@[target] theorem isConj_iff_conjugatesOf_eq {a b : α} : IsConj a b ↔ conjugatesOf a = conjugatesOf b :=
  ⟨IsConj.conjugatesOf_eq, fun h => by
    sorry


end Monoid

namespace ConjClasses

variable [Monoid α]

attribute [local instance] IsConj.setoid

/-- Given a conjugacy class `a`, `carrier a` is the set it represents. -/
/-- Given a conjugacy class `a`, `carrier a` is the set it represents. -/
def carrier : ConjClasses α → Set α := by sorry


@[target] theorem mem_carrier_mk {a : α} : a ∈ carrier (ConjClasses.mk a) := by sorry


@[target] theorem mem_carrier_iff_mk_eq {a : α} {b : ConjClasses α} :
    a ∈ carrier b ↔ ConjClasses.mk a = b := by
  sorry


@[target] theorem carrier_eq_preimage_mk {a : ConjClasses α} : a.carrier = ConjClasses.mk ⁻¹' {a} := by sorry


end ConjClasses
