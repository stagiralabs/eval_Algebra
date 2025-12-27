import VerifiedAgora.tagger
/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Group.Hom.End
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Set.Pointwise.SMul
import Mathlib.Order.WellFoundedSet

/-! # Pointwise instances on `Submonoid`s and `AddSubmonoid`s

This file provides:

* `Submonoid.inv`
* `AddSubmonoid.neg`

and the actions

* `Submonoid.pointwiseMulAction`
* `AddSubmonoid.pointwiseMulAction`

which matches the action of `Set.mulActionSet`.

`SMul (AddSubmonoid R) (AddSubmonoid A)` is also provided given `DistribSMul R A`,
and when `R = A` it is definitionally equal to the multiplication on `AddSubmonoid R`.

These are all available in the `Pointwise` locale.

Additionally, it provides various degrees of monoid structure:
* `AddSubmonoid.one`
* `AddSubmonoid.mul`
* `AddSubmonoid.mulOneClass`
* `AddSubmonoid.semigroup`
* `AddSubmonoid.monoid`
which is available globally to match the monoid structure implied by `Submodule.idemSemiring`.

## Implementation notes

Most of the lemmas in this file are direct copies of lemmas from `Algebra/Pointwise.lean`.
While the statements of these lemmas are defeq, we repeat them here due to them not being
syntactically equal. Before adding new lemmas here, consider if they would also apply to the action
on `Set`s.

Many results about multiplication is derived from the corresponding results about
scalar multiplication, but results requiring right distributivity do not have
SMul versions, due to the lack of a suitable typeclass (unless one goes all the
way to `Module`).

-/


open Set Pointwise

variable {α G M R A S : Type*}
variable [Monoid M] [AddMonoid A]

@[target, to_additive (attr := by sorry

set_option linter.unusedVariables false in
@[target, to_additive (attr := sorry

@[to_additive]
theorem mul_subset_closure (hs : s ⊆ u) (ht : t ⊆ u) : s * t ⊆ Submonoid.closure u :=
  mul_subset (Subset.trans hs Submonoid.subset_closure) (Subset.trans ht Submonoid.subset_closure)

@[target, to_additive]
theorem coe_mul_self_eq (s : Submonoid M) : (s : Set M) * s = s := by sorry

@[to_additive]
theorem closure_mul_le (S T : Set M) : closure (S * T) ≤ closure S ⊔ closure T :=
  sInf_le fun _x ⟨_s, hs, _t, ht, hx⟩ => hx ▸
    (closure S ⊔ closure T).mul_mem (SetLike.le_def.mp le_sup_left <| subset_closure hs)
      (SetLike.le_def.mp le_sup_right <| subset_closure ht)

@[target, to_additive]
lemma closure_pow_le : ∀ {n}, n ≠ 0 → closure (s ^ n) ≤ closure s
  | 1, _ => by simp
  | n + 2, _ =>
    calc
      closure (s ^ (n + 2))
      _ = closure (s ^ (n + 1) * s) := by sorry

@[to_additive]
lemma closure_pow {n : ℕ} (hs : 1 ∈ s) (hn : n ≠ 0) : closure (s ^ n) = closure s :=
  (closure_pow_le hn).antisymm <| by gcongr; exact subset_pow hs hn

@[to_additive]
theorem sup_eq_closure_mul (H K : Submonoid M) : H ⊔ K = closure ((H : Set M) * (K : Set M)) :=
  le_antisymm
    (sup_le (fun h hh => subset_closure ⟨h, hh, 1, K.one_mem, mul_one h⟩) fun k hk =>
      subset_closure ⟨1, H.one_mem, k, hk, one_mul k⟩)
    ((closure_mul_le _ _).trans <| by rw [closure_eq, closure_eq])

@[target, to_additive]
theorem pow_smul_mem_closure_smul {N : Type*} [CommMonoid N] [MulAction M N] [IsScalarTower M N N]
    (r : M) (s : Set N) {x : N} (hx : x ∈ closure s) : ∃ n : ℕ, r ^ n • x ∈ closure (r • s) := by sorry

variable [Group G]

/-- The submonoid with every element inverted. -/
@[to_additive "The additive submonoid with every element negated."]
protected def inv : Inv (Submonoid G) where
  inv S :=
    { carrier := (S : Set G)⁻¹
      mul_mem' := fun ha hb => by rw [mem_inv, mul_inv_rev]; exact mul_mem hb ha
      one_mem' := mem_inv.2 <| by rw [inv_one]; exact S.one_mem' }

scoped[Pointwise] attribute [instance] Submonoid.inv AddSubmonoid.neg

@[target, to_additive (attr := sorry

@[target, to_additive (attr := sorry
@[to_additive "Inversion is involutive on additive submonoids."]
def involutiveInv : InvolutiveInv (Submonoid G) :=
  SetLike.coe_injective.involutiveInv _ fun _ => rfl

scoped[Pointwise] attribute [instance] Submonoid.involutiveInv AddSubmonoid.involutiveNeg

@[to_additive (attr := simp)]
theorem inv_le_inv (S T : Submonoid G) : S⁻¹ ≤ T⁻¹ ↔ S ≤ T :=
  SetLike.coe_subset_coe.symm.trans Set.inv_subset_inv

@[target, to_additive]
theorem inv_le (S T : Submonoid G) : S⁻¹ ≤ T ↔ S ≤ T⁻¹ :=
  sorry
@[to_additive (attr := simps!) "Pointwise negation of additive submonoids as an order isomorphism"]
def invOrderIso : Submonoid G ≃o Submonoid G where
  toEquiv := Equiv.inv _
  map_rel_iff' := inv_le_inv _ _

@[target, to_additive]
theorem closure_inv (s : Set G) : closure s⁻¹ = (closure s)⁻¹ := by sorry

@[to_additive (attr := simp)]
theorem inv_inf (S T : Submonoid G) : (S ⊓ T)⁻¹ = S⁻¹ ⊓ T⁻¹ :=
  SetLike.coe_injective Set.inter_inv

@[target, to_additive (attr := sorry

@[target, to_additive (attr := sorry

@[target, to_additive (attr := sorry

@[to_additive (attr := simp)]
theorem inv_iInf {ι : Sort*} (S : ι → Submonoid G) : (⨅ i, S i)⁻¹ = ⨅ i, (S i)⁻¹ :=
  (invOrderIso : Submonoid G ≃o Submonoid G).map_iInf _

@[to_additive (attr := simp)]
theorem inv_iSup {ι : Sort*} (S : ι → Submonoid G) : (⨆ i, S i)⁻¹ = ⨆ i, (S i)⁻¹ :=
  (invOrderIso : Submonoid G ≃o Submonoid G).map_iSup _

end Submonoid

namespace Submonoid

section Monoid

variable [Monoid α] [MulDistribMulAction α M]

-- todo: add `to_additive`?
/-- The action on a submonoid corresponding to applying the action to every element.

This is available as an instance in the `Pointwise` locale. -/
protected def pointwiseMulAction : MulAction α (Submonoid M) where
  smul a S := S.map (MulDistribMulAction.toMonoidEnd _ M a)
  one_smul S := by
    change S.map _ = S
    simpa only [map_one] using S.map_id
  mul_smul _ _ S :=
    (congr_arg (fun f : Monoid.End M => S.map f) (MonoidHom.map_mul _ _ _)).trans
      (S.map_map _ _).symm

scoped[Pointwise] attribute [instance] Submonoid.pointwiseMulAction

@[simp]
theorem coe_pointwise_smul (a : α) (S : Submonoid M) : ↑(a • S) = a • (S : Set M) :=
  rfl

theorem smul_mem_pointwise_smul (m : M) (a : α) (S : Submonoid M) : m ∈ S → a • m ∈ a • S :=
  (Set.smul_mem_smul_set : _ → _ ∈ a • (S : Set M))

instance : CovariantClass α (Submonoid M) HSMul.hSMul LE.le :=
  ⟨fun _ _ => image_subset _⟩

theorem mem_smul_pointwise_iff_exists (m : M) (a : α) (S : Submonoid M) :
    m ∈ a • S ↔ ∃ s : M, s ∈ S ∧ a • s = m :=
  (Set.mem_smul_set : m ∈ a • (S : Set M) ↔ _)

@[simp]
theorem smul_bot (a : α) : a • (⊥ : Submonoid M) = ⊥ :=
  map_bot _

theorem smul_sup (a : α) (S T : Submonoid M) : a • (S ⊔ T) = a • S ⊔ a • T :=
  map_sup _ _ _

theorem smul_closure (a : α) (s : Set M) : a • closure s = closure (a • s) :=
  MonoidHom.map_mclosure _ _

lemma pointwise_isCentralScalar [MulDistribMulAction αᵐᵒᵖ M] [IsCentralScalar α M] :
    IsCentralScalar α (Submonoid M) :=
  ⟨fun _ S => (congr_arg fun f : Monoid.End M => S.map f) <| MonoidHom.ext <| op_smul_eq_smul _⟩

scoped[Pointwise] attribute [instance] Submonoid.pointwise_isCentralScalar

end Monoid

section Group

variable [Group α] [MulDistribMulAction α M]

@[simp]
theorem smul_mem_pointwise_smul_iff {a : α} {S : Submonoid M} {x : M} : a • x ∈ a • S ↔ x ∈ S :=
  smul_mem_smul_set_iff

theorem mem_pointwise_smul_iff_inv_smul_mem {a : α} {S : Submonoid M} {x : M} :
    x ∈ a • S ↔ a⁻¹ • x ∈ S :=
  mem_smul_set_iff_inv_smul_mem

theorem mem_inv_pointwise_smul_iff {a : α} {S : Submonoid M} {x : M} : x ∈ a⁻¹ • S ↔ a • x ∈ S :=
  mem_inv_smul_set_iff

@[simp]
theorem pointwise_smul_le_pointwise_smul_iff {a : α} {S T : Submonoid M} : a • S ≤ a • T ↔ S ≤ T :=
  smul_set_subset_smul_set_iff

theorem pointwise_smul_subset_iff {a : α} {S T : Submonoid M} : a • S ≤ T ↔ S ≤ a⁻¹ • T :=
  smul_set_subset_iff_subset_inv_smul_set

theorem subset_pointwise_smul_iff {a : α} {S T : Submonoid M} : S ≤ a • T ↔ a⁻¹ • S ≤ T :=
  subset_smul_set_iff

end Group

section GroupWithZero

variable [GroupWithZero α] [MulDistribMulAction α M]

@[simp]
theorem smul_mem_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) (S : Submonoid M) (x : M) :
    a • x ∈ a • S ↔ x ∈ S :=
  smul_mem_smul_set_iff₀ ha (S : Set M) x

theorem mem_pointwise_smul_iff_inv_smul_mem₀ {a : α} (ha : a ≠ 0) (S : Submonoid M) (x : M) :
    x ∈ a • S ↔ a⁻¹ • x ∈ S :=
  mem_smul_set_iff_inv_smul_mem₀ ha (S : Set M) x

theorem mem_inv_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) (S : Submonoid M) (x : M) :
    x ∈ a⁻¹ • S ↔ a • x ∈ S :=
  mem_inv_smul_set_iff₀ ha (S : Set M) x

@[simp]
theorem pointwise_smul_le_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) {S T : Submonoid M} :
    a • S ≤ a • T ↔ S ≤ T :=
  smul_set_subset_smul_set_iff₀ ha

theorem pointwise_smul_le_iff₀ {a : α} (ha : a ≠ 0) {S T : Submonoid M} : a • S ≤ T ↔ S ≤ a⁻¹ • T :=
  smul_set_subset_iff₀ ha

theorem le_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) {S T : Submonoid M} : S ≤ a • T ↔ a⁻¹ • S ≤ T :=
  subset_smul_set_iff₀ ha

end GroupWithZero

@[target, to_additive]
theorem mem_closure_inv {G : Type*} [Group G] (S : Set G) (x : G) :
    x ∈ Submonoid.closure S⁻¹ ↔ x⁻¹ ∈ Submonoid.closure S := by sorry

end Submonoid

namespace AddSubmonoid

section Monoid

variable [Monoid α] [DistribMulAction α A]

/-- The action on an additive submonoid corresponding to applying the action to every element.

This is available as an instance in the `Pointwise` locale. -/
protected def pointwiseMulAction : MulAction α (AddSubmonoid A) where
  smul a S := S.map (DistribMulAction.toAddMonoidEnd _ A a)
  one_smul S :=
    (congr_arg (fun f : AddMonoid.End A => S.map f) (MonoidHom.map_one _)).trans S.map_id
  mul_smul _ _ S :=
    (congr_arg (fun f : AddMonoid.End A => S.map f) (MonoidHom.map_mul _ _ _)).trans
      (S.map_map _ _).symm

scoped[Pointwise] attribute [instance] AddSubmonoid.pointwiseMulAction

@[target, simp]
theorem coe_pointwise_smul (a : α) (S : AddSubmonoid A) : ↑(a • S) = a • (S : Set A) :=
  sorry

@[target]
theorem smul_mem_pointwise_smul (m : A) (a : α) (S : AddSubmonoid A) : m ∈ S → a • m ∈ a • S :=
  sorry

@[target]
theorem mem_smul_pointwise_iff_exists (m : A) (a : α) (S : AddSubmonoid A) :
    m ∈ a • S ↔ ∃ s : A, s ∈ S ∧ a • s = m :=
  sorry

@[target, simp]
theorem smul_bot (a : α) : a • (⊥ : AddSubmonoid A) = ⊥ :=
  sorry

@[target]
theorem smul_sup (a : α) (S T : AddSubmonoid A) : a • (S ⊔ T) = a • S ⊔ a • T :=
  sorry

@[target, simp]
theorem smul_closure (a : α) (s : Set A) : a • closure s = closure (a • s) :=
  sorry

@[target]
lemma pointwise_isCentralScalar [DistribMulAction αᵐᵒᵖ A] [IsCentralScalar α A] :
    IsCentralScalar α (AddSubmonoid A) :=
  sorry

end Monoid

section Group

variable [Group α] [DistribMulAction α A]

@[simp]
theorem smul_mem_pointwise_smul_iff {a : α} {S : AddSubmonoid A} {x : A} : a • x ∈ a • S ↔ x ∈ S :=
  smul_mem_smul_set_iff

@[target]
theorem mem_pointwise_smul_iff_inv_smul_mem {a : α} {S : AddSubmonoid A} {x : A} :
    x ∈ a • S ↔ a⁻¹ • x ∈ S :=
  sorry

@[target]
theorem mem_inv_pointwise_smul_iff {a : α} {S : AddSubmonoid A} {x : A} : x ∈ a⁻¹ • S ↔ a • x ∈ S :=
  sorry

@[target, simp]
theorem pointwise_smul_le_pointwise_smul_iff {a : α} {S T : AddSubmonoid A} :
    a • S ≤ a • T ↔ S ≤ T :=
  sorry

@[target]
theorem pointwise_smul_le_iff {a : α} {S T : AddSubmonoid A} : a • S ≤ T ↔ S ≤ a⁻¹ • T :=
  sorry

theorem le_pointwise_smul_iff {a : α} {S T : AddSubmonoid A} : S ≤ a • T ↔ a⁻¹ • S ≤ T :=
  subset_smul_set_iff

end Group

section GroupWithZero

variable [GroupWithZero α] [DistribMulAction α A]

@[target, simp]
theorem smul_mem_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) (S : AddSubmonoid A) (x : A) :
    a • x ∈ a • S ↔ x ∈ S :=
  sorry

@[target]
theorem mem_pointwise_smul_iff_inv_smul_mem₀ {a : α} (ha : a ≠ 0) (S : AddSubmonoid A) (x : A) :
    x ∈ a • S ↔ a⁻¹ • x ∈ S :=
  sorry

@[target]
theorem mem_inv_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) (S : AddSubmonoid A) (x : A) :
    x ∈ a⁻¹ • S ↔ a • x ∈ S :=
  sorry

@[target, simp]
theorem pointwise_smul_le_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) {S T : AddSubmonoid A} :
    a • S ≤ a • T ↔ S ≤ T :=
  sorry

theorem pointwise_smul_le_iff₀ {a : α} (ha : a ≠ 0) {S T : AddSubmonoid A} :
    a • S ≤ T ↔ S ≤ a⁻¹ • T :=
  smul_set_subset_iff₀ ha

@[target]
theorem le_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) {S T : AddSubmonoid A} :
    S ≤ a • T ↔ a⁻¹ • S ≤ T :=
  sorry

end GroupWithZero

end AddSubmonoid

/-! ### Elementwise monoid structure of additive submonoids

These definitions are a cut-down versions of the ones around `Submodule.mul`, as that API is
usually more useful. -/

namespace AddSubmonoid

section AddMonoidWithOne

variable [AddMonoidWithOne R]

/-- If `R` is an additive monoid with one (e.g., a semiring), then `1 : AddSubmonoid R` is the range
of `Nat.cast : ℕ → R`. -/
protected def one : One (AddSubmonoid R) :=
  ⟨AddMonoidHom.mrange (Nat.castAddMonoidHom R)⟩
scoped[Pointwise] attribute [instance] AddSubmonoid.one

theorem one_eq_mrange : (1 : AddSubmonoid R) = AddMonoidHom.mrange (Nat.castAddMonoidHom R) :=
  rfl

theorem natCast_mem_one (n : ℕ) : (n : R) ∈ (1 : AddSubmonoid R) :=
  ⟨_, rfl⟩

@[target, simp]
theorem mem_one {x : R} : x ∈ (1 : AddSubmonoid R) ↔ ∃ n : ℕ, ↑n = x :=
  sorry

theorem one_eq_closure : (1 : AddSubmonoid R) = closure {1} := by
  rw [closure_singleton_eq, one_eq_mrange]
  congr 1
  ext
  simp

@[target]
theorem one_eq_closure_one_set : (1 : AddSubmonoid R) = closure 1 :=
  sorry

end AddMonoidWithOne

section SMul

variable [AddMonoid R] [DistribSMul R A]

/-- For `M : Submonoid R` and `N : AddSubmonoid A`, `M • N` is the additive submonoid
generated by all `m • n` where `m ∈ M` and `n ∈ N`. -/
protected def smul : SMul (AddSubmonoid R) (AddSubmonoid A) where
  smul M N := ⨆ s : M, N.map (DistribSMul.toAddMonoidHom A s.1)

scoped[Pointwise] attribute [instance] AddSubmonoid.smul

variable {M M' : AddSubmonoid R} {N P : AddSubmonoid A} {m : R} {n : A}

@[target]
theorem smul_mem_smul (hm : m ∈ M) (hn : n ∈ N) : m • n ∈ M • N :=
  sorry

theorem smul_le : M • N ≤ P ↔ ∀ m ∈ M, ∀ n ∈ N, m • n ∈ P :=
  ⟨fun H _m hm _n hn => H <| smul_mem_smul hm hn, fun H =>
    iSup_le fun ⟨m, hm⟩ => map_le_iff_le_comap.2 fun n hn => H m hm n hn⟩

@[elab_as_elim]
protected theorem smul_induction_on {C : A → Prop} {a : A} (ha : a ∈ M • N)
    (hm : ∀ m ∈ M, ∀ n ∈ N, C (m • n)) (hadd : ∀ x y, C x → C y → C (x + y)) : C a :=
  (@smul_le _ _ _ _ _ _ _ ⟨⟨setOf C, hadd _ _⟩, by
    simpa only [smul_zero] using hm _ (zero_mem _) _ (zero_mem _)⟩).2 hm ha

@[simp]
theorem addSubmonoid_smul_bot (S : AddSubmonoid R) : S • (⊥ : AddSubmonoid A) = ⊥ :=
  eq_bot_iff.2 <| smul_le.2 fun m _ n hn => by
    rw [AddSubmonoid.mem_bot] at hn ⊢; rw [hn, smul_zero]

@[target]
theorem smul_le_smul (h : M ≤ M') (hnp : N ≤ P) : M • N ≤ M' • P :=
  sorry

@[target]
theorem smul_le_smul_left (h : M ≤ M') : M • P ≤ M' • P :=
  sorry

theorem smul_le_smul_right (h : N ≤ P) : M • N ≤ M • P :=
  smul_le_smul le_rfl h

@[target]
theorem smul_subset_smul : (↑M : Set R) • (↑N : Set A) ⊆ (↑(M • N) : Set A) :=
  sorry

@[target]
theorem addSubmonoid_smul_sup : M • (N ⊔ P) = M • N ⊔ M • P :=
  sorry

variable {ι : Sort*}

@[target]
theorem smul_iSup (T : AddSubmonoid R) (S : ι → AddSubmonoid A) : (T • ⨆ i, S i) = ⨆ i, T • S i :=
  sorry

end SMul

section NonUnitalNonAssocSemiring

variable [NonUnitalNonAssocSemiring R]

/-- Multiplication of additive submonoids of a semiring R. The additive submonoid `S * T` is the
smallest R-submodule of `R` containing the elements `s * t` for `s ∈ S` and `t ∈ T`. -/
protected def mul : Mul (AddSubmonoid R) :=
  ⟨fun M N => ⨆ s : M, N.map (AddMonoidHom.mul s.1)⟩
scoped[Pointwise] attribute [instance] AddSubmonoid.mul

@[target]
theorem mul_mem_mul {M N : AddSubmonoid R} {m n : R} (hm : m ∈ M) (hn : n ∈ N) : m * n ∈ M * N :=
  sorry

theorem mul_le {M N P : AddSubmonoid R} : M * N ≤ P ↔ ∀ m ∈ M, ∀ n ∈ N, m * n ∈ P :=
  smul_le

@[elab_as_elim]
protected theorem mul_induction_on {M N : AddSubmonoid R} {C : R → Prop} {r : R} (hr : r ∈ M * N)
    (hm : ∀ m ∈ M, ∀ n ∈ N, C (m * n)) (ha : ∀ x y, C x → C y → C (x + y)) : C r :=
  AddSubmonoid.smul_induction_on hr hm ha

-- need `add_smul` to generalize to `SMul`
@[target]
theorem closure_mul_closure (S T : Set R) : closure S * closure T = closure (S * T) := by sorry

theorem mul_eq_closure_mul_set (M N : AddSubmonoid R) :
    M * N = closure ((M : Set R) * (N : Set R)) := by
  rw [← closure_mul_closure, closure_eq, closure_eq]

@[simp]
theorem mul_bot (S : AddSubmonoid R) : S * ⊥ = ⊥ :=
  addSubmonoid_smul_bot S

-- need `zero_smul` to generalize to `SMul`
@[simp]
theorem bot_mul (S : AddSubmonoid R) : ⊥ * S = ⊥ :=
  eq_bot_iff.2 <| mul_le.2 fun m hm n _ => by
    rw [AddSubmonoid.mem_bot] at hm ⊢; rw [hm, zero_mul]

variable {M N P Q : AddSubmonoid R}

@[mono, gcongr] lemma mul_le_mul (hmp : M ≤ P) (hnq : N ≤ Q) : M * N ≤ P * Q := smul_le_smul hmp hnq

@[gcongr] lemma mul_le_mul_left (h : M ≤ N) : M * P ≤ N * P := smul_le_smul_left h
@[gcongr] lemma mul_le_mul_right (h : N ≤ P) : M * N ≤ M * P := smul_le_smul_right h

@[target]
theorem mul_subset_mul : (↑M : Set R) * (↑N : Set R) ⊆ (↑(M * N) : Set R) :=
  sorry

theorem mul_sup : M * (N ⊔ P) = M * N ⊔ M * P :=
  addSubmonoid_smul_sup

-- need `zero_smul` and `add_smul` to generalize to `SMul`
@[target]
theorem sup_mul : (M ⊔ N) * P = M * P ⊔ N * P :=
  sorry

variable {ι : Sort*}

-- need `zero_smul` and `add_smul` to generalize to `SMul`
@[target]
theorem iSup_mul (S : ι → AddSubmonoid R) (T : AddSubmonoid R) : (⨆ i, S i) * T = ⨆ i, S i * T :=
  sorry

theorem mul_iSup (T : AddSubmonoid R) (S : ι → AddSubmonoid R) : (T * ⨆ i, S i) = ⨆ i, T * S i :=
  smul_iSup T S

@[target]
theorem mul_comm_of_commute (h : ∀ m ∈ M, ∀ n ∈ N, Commute m n) : M * N = N * M :=
  sorry

end NonUnitalNonAssocSemiring

section NonUnitalNonAssocRing

variable [NonUnitalNonAssocRing R]

/-- `AddSubmonoid.neg` distributes over multiplication.

This is available as an instance in the `Pointwise` locale. -/
protected def hasDistribNeg : HasDistribNeg (AddSubmonoid R) :=
  { AddSubmonoid.involutiveNeg with
    neg_mul := fun x y => by
      refine
          le_antisymm (mul_le.2 fun m hm n hn => ?_)
            ((AddSubmonoid.neg_le _ _).2 <| mul_le.2 fun m hm n hn => ?_) <;>
        simp only [AddSubmonoid.mem_neg, ← neg_mul] at *
      · exact mul_mem_mul hm hn
      · exact mul_mem_mul (neg_mem_neg.2 hm) hn
    mul_neg := fun x y => by
      refine
          le_antisymm (mul_le.2 fun m hm n hn => ?_)
            ((AddSubmonoid.neg_le _ _).2 <| mul_le.2 fun m hm n hn => ?_) <;>
        simp only [AddSubmonoid.mem_neg, ← mul_neg] at *
      · exact mul_mem_mul hm hn
      · exact mul_mem_mul hm (neg_mem_neg.2 hn) }

scoped[Pointwise] attribute [instance] AddSubmonoid.hasDistribNeg

end NonUnitalNonAssocRing

section NonAssocSemiring

variable [NonAssocSemiring R]

/-- A `MulOneClass` structure on additive submonoids of a (possibly, non-associative) semiring. -/
protected def mulOneClass : MulOneClass (AddSubmonoid R) where
  one := 1
  mul := (· * ·)
  one_mul M := by rw [one_eq_closure_one_set, ← closure_eq M, closure_mul_closure, one_mul]
  mul_one M := by rw [one_eq_closure_one_set, ← closure_eq M, closure_mul_closure, mul_one]
scoped[Pointwise] attribute [instance] AddSubmonoid.mulOneClass

end NonAssocSemiring

section NonUnitalSemiring

variable [NonUnitalSemiring R]

/-- Semigroup structure on additive submonoids of a (possibly, non-unital) semiring. -/
protected def semigroup : Semigroup (AddSubmonoid R) where
  mul := (· * ·)
  mul_assoc _M _N _P :=
    le_antisymm
      (mul_le.2 fun _mn hmn p hp => AddSubmonoid.mul_induction_on hmn
        (fun m hm n hn ↦ mul_assoc m n p ▸ mul_mem_mul hm <| mul_mem_mul hn hp)
        fun x y ↦ (add_mul x y p).symm ▸ add_mem)
      (mul_le.2 fun m hm _np hnp => AddSubmonoid.mul_induction_on hnp
        (fun n hn p hp ↦ mul_assoc m n p ▸ mul_mem_mul (mul_mem_mul hm hn) hp)
        fun x y ↦ (mul_add m x y) ▸ add_mem)
scoped[Pointwise] attribute [instance] AddSubmonoid.semigroup
end NonUnitalSemiring

section Semiring

variable [Semiring R]

/-- Monoid structure on additive submonoids of a semiring. -/
protected def monoid : Monoid (AddSubmonoid R) :=
  { AddSubmonoid.semigroup, AddSubmonoid.mulOneClass with }
scoped[Pointwise] attribute [instance] AddSubmonoid.monoid

@[target]
theorem closure_pow (s : Set R) : ∀ n : ℕ, closure s ^ n = closure (s ^ n)
  | 0 => by rw [pow_zero, pow_zero, one_eq_closure_one_set]
  | n + 1 => by rw [pow_succ, pow_succ, closure_pow s n, closure_mul_closure]

theorem pow_eq_closure_pow_set (s : AddSubmonoid R) (n : ℕ) :
    s ^ n = closure ((s : Set R) ^ n) := by sorry

theorem pow_subset_pow {s : AddSubmonoid R} {n : ℕ} : (↑s : Set R) ^ n ⊆ ↑(s ^ n) :=
  (pow_eq_closure_pow_set s n).symm ▸ subset_closure

end Semiring

end AddSubmonoid

namespace Set.IsPWO

variable [OrderedCancelCommMonoid α] {s : Set α}

@[target, to_additive]
theorem submonoid_closure (hpos : ∀ x : α, x ∈ s → 1 ≤ x) (h : s.IsPWO) :
    IsPWO (Submonoid.closure s : Set α) := by sorry

end Set.IsPWO
