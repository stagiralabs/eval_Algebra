import VerifiedAgora.tagger
/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/
import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Common

/-!
# Monoids of endomorphisms, groups of automorphisms

This file defines
* the endomorphism monoid structure on `Function.End α := α → α`
* the endomorphism monoid structure on `Monoid.End M := M →* M` and `AddMonoid.End M := M →+ M`
* the automorphism group structure on `Equiv.Perm α := α ≃ α`
* the automorphism group structure on `MulAut M := M ≃* M` and `AddAut M := M ≃+ M`.

## Implementation notes

The definition of multiplication in the endomorphism monoids and automorphism groups agrees with
function composition, and multiplication in `CategoryTheory.End`, but not with
`CategoryTheory.comp`.

## Tags

end monoid, aut group
-/

assert_not_exists MonoidWithZero MulAction RelIso

variable {A M G α β : Type*}

/-! ### Type endomorphisms -/

variable (α) in
/-- The monoid of endomorphisms.

Note that this is generalized by `CategoryTheory.End` to categories other than `Type u`. -/
protected def Function.End := α → α

instance : Monoid (Function.End α) where
  one := id
  mul := (· ∘ ·)
  mul_assoc _ _ _ := rfl
  mul_one _ := rfl
  one_mul _ := rfl
  npow n f := f^[n]
  npow_succ _ _ := Function.iterate_succ _ _

instance : Inhabited (Function.End α) := ⟨1⟩

/-! ### Monoid endomorphisms -/

namespace Equiv.Perm

instance instOne : One (Perm α) where one := Equiv.refl _
instance instMul : Mul (Perm α) where mul f g := Equiv.trans g f
instance instInv : Inv (Perm α) where inv := Equiv.symm
instance instPowNat : Pow (Perm α) ℕ where
  pow f n := ⟨f^[n], f.symm^[n], f.left_inv.iterate _, f.right_inv.iterate _⟩

instance permGroup : Group (Perm α) where
  mul_assoc _ _ _ := (trans_assoc _ _ _).symm
  one_mul := trans_refl
  mul_one := refl_trans
  inv_mul_cancel := self_trans_symm
  npow n f := f ^ n
  npow_succ _ _ := coe_fn_injective <| Function.iterate_succ _ _
  zpow := zpowRec fun n f ↦ f ^ n
  zpow_succ' _ _ := coe_fn_injective <| Function.iterate_succ _ _

@[target, simp]
theorem default_eq : (default : Perm α) = 1 :=
  sorry
@[simps]
def equivUnitsEnd : Perm α ≃* Units (Function.End α) where
  -- Porting note: needed to add `.toFun`.
  toFun e := ⟨e.toFun, e.symm.toFun, e.self_comp_symm, e.symm_comp_self⟩
  invFun u :=
    ⟨(u : Function.End α), (↑u⁻¹ : Function.End α), congr_fun u.inv_val, congr_fun u.val_inv⟩
  left_inv _ := ext fun _ => rfl
  right_inv _ := Units.ext rfl
  map_mul' _ _ := rfl

/-- Lift a monoid homomorphism `f : G →* Function.End α` to a monoid homomorphism
`f : G →* Equiv.Perm α`. -/
@[simps!]
def _root_.MonoidHom.toHomPerm {G : Type*} [Group G] (f : G →* Function.End α) : G →* Perm α :=
  equivUnitsEnd.symm.toMonoidHom.comp f.toHomUnits

theorem mul_apply (f g : Perm α) (x) : (f * g) x = f (g x) :=
  Equiv.trans_apply _ _ _

theorem one_apply (x) : (1 : Perm α) x = x :=
  rfl

@[simp]
theorem inv_apply_self (f : Perm α) (x) : f⁻¹ (f x) = x :=
  f.symm_apply_apply x

@[simp]
theorem apply_inv_self (f : Perm α) (x) : f (f⁻¹ x) = x :=
  f.apply_symm_apply x

theorem one_def : (1 : Perm α) = Equiv.refl α :=
  rfl

theorem mul_def (f g : Perm α) : f * g = g.trans f :=
  rfl

theorem inv_def (f : Perm α) : f⁻¹ = f.symm :=
  rfl

@[simp, norm_cast] lemma coe_one : ⇑(1 : Perm α) = id := rfl

@[simp, norm_cast] lemma coe_mul (f g : Perm α) : ⇑(f * g) = f ∘ g := rfl

@[norm_cast] lemma coe_pow (f : Perm α) (n : ℕ) : ⇑(f ^ n) = f^[n] := rfl

@[simp] lemma iterate_eq_pow (f : Perm α) (n : ℕ) : f^[n] = ⇑(f ^ n) := rfl

@[target]
theorem eq_inv_iff_eq {f : Perm α} {x y : α} : x = f⁻¹ y ↔ f x = y :=
  sorry

@[target]
theorem inv_eq_iff_eq {f : Perm α} {x y : α} : f⁻¹ x = y ↔ x = f y :=
  sorry

theorem zpow_apply_comm {α : Type*} (σ : Perm α) (m n : ℤ) {x : α} :
    (σ ^ m) ((σ ^ n) x) = (σ ^ n) ((σ ^ m) x) := by
  rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, zpow_mul_comm]

/-! Lemmas about mixing `Perm` with `Equiv`. Because we have multiple ways to express
`Equiv.refl`, `Equiv.symm`, and `Equiv.trans`, we want simp lemmas for every combination.
The assumption made here is that if you're using the group structure, you want to preserve it after
simp. -/


@[target, simp]
theorem trans_one {α : Sort*} {β : Type*} (e : α ≃ β) : e.trans (1 : Perm β) = e :=
  sorry

@[simp]
theorem mul_refl (e : Perm α) : e * Equiv.refl α = e :=
  Equiv.trans_refl e

@[target, simp]
theorem one_symm : (1 : Perm α).symm = 1 :=
  sorry

@[target, simp]
theorem refl_inv : (Equiv.refl α : Perm α)⁻¹ = 1 :=
  sorry

@[simp]
theorem one_trans {α : Type*} {β : Sort*} (e : α ≃ β) : (1 : Perm α).trans e = e :=
  Equiv.refl_trans e

@[target, simp]
theorem refl_mul (e : Perm α) : Equiv.refl α * e = e :=
  sorry

@[target, simp]
theorem inv_trans_self (e : Perm α) : e⁻¹.trans e = 1 :=
  sorry

@[simp]
theorem mul_symm (e : Perm α) : e * e.symm = 1 :=
  Equiv.symm_trans_self e

@[target, simp]
theorem self_trans_inv (e : Perm α) : e.trans e⁻¹ = 1 :=
  sorry

@[simp]
theorem symm_mul (e : Perm α) : e.symm * e = 1 :=
  Equiv.self_trans_symm e

/-! Lemmas about `Equiv.Perm.sumCongr` re-expressed via the group structure. -/


@[simp]
theorem sumCongr_mul {α β : Type*} (e : Perm α) (f : Perm β) (g : Perm α) (h : Perm β) :
    sumCongr e f * sumCongr g h = sumCongr (e * g) (f * h) :=
  sumCongr_trans g h e f

@[target, simp]
theorem sumCongr_inv {α β : Type*} (e : Perm α) (f : Perm β) :
    (sumCongr e f)⁻¹ = sumCongr e⁻¹ f⁻¹ :=
  sorry

@[target, simp]
theorem sumCongr_one {α β : Type*} : sumCongr (1 : Perm α) (1 : Perm β) = 1 :=
  sorry
@[simps]
def sumCongrHom (α β : Type*) : Perm α × Perm β →* Perm (α ⊕ β) where
  toFun a := sumCongr a.1 a.2
  map_one' := sumCongr_one
  map_mul' _ _ := (sumCongr_mul _ _ _ _).symm

@[target]
theorem sumCongrHom_injective {α β : Type*} : Function.Injective (sumCongrHom α β) := by sorry

@[target, simp]
theorem sumCongr_swap_one {α β : Type*} [DecidableEq α] [DecidableEq β] (i j : α) :
    sumCongr (Equiv.swap i j) (1 : Perm β) = Equiv.swap (Sum.inl i) (Sum.inl j) :=
  sorry

@[simp]
theorem sumCongr_one_swap {α β : Type*} [DecidableEq α] [DecidableEq β] (i j : β) :
    sumCongr (1 : Perm α) (Equiv.swap i j) = Equiv.swap (Sum.inr i) (Sum.inr j) :=
  sumCongr_refl_swap i j

/-! Lemmas about `Equiv.Perm.sigmaCongrRight` re-expressed via the group structure. -/


@[target, simp]
theorem sigmaCongrRight_mul {α : Type*} {β : α → Type*} (F : ∀ a, Perm (β a))
    (G : ∀ a, Perm (β a)) : sigmaCongrRight F * sigmaCongrRight G = sigmaCongrRight (F * G) :=
  sorry

@[simp]
theorem sigmaCongrRight_inv {α : Type*} {β : α → Type*} (F : ∀ a, Perm (β a)) :
    (sigmaCongrRight F)⁻¹ = sigmaCongrRight fun a => (F a)⁻¹ :=
  sigmaCongrRight_symm F

@[target, simp]
theorem sigmaCongrRight_one {α : Type*} {β : α → Type*} :
    sigmaCongrRight (1 : ∀ a, Equiv.Perm <| β a) = 1 :=
  sorry
@[simps]
def sigmaCongrRightHom {α : Type*} (β : α → Type*) : (∀ a, Perm (β a)) →* Perm (Σa, β a) where
  toFun := sigmaCongrRight
  map_one' := sigmaCongrRight_one
  map_mul' _ _ := (sigmaCongrRight_mul _ _).symm

@[target]
theorem sigmaCongrRightHom_injective {α : Type*} {β : α → Type*} :
    Function.Injective (sigmaCongrRightHom β) := by sorry
@[simps]
def subtypeCongrHom (p : α → Prop) [DecidablePred p] :
    Perm { a // p a } × Perm { a // ¬p a } →* Perm α where
  toFun pair := Perm.subtypeCongr pair.fst pair.snd
  map_one' := Perm.subtypeCongr.refl
  map_mul' _ _ := (Perm.subtypeCongr.trans _ _ _ _).symm

@[target]
theorem subtypeCongrHom_injective (p : α → Prop) [DecidablePred p] :
    Function.Injective (subtypeCongrHom p) := by sorry
@[target, simp]
theorem permCongr_eq_mul (e p : Perm α) : e.permCongr p = e * p * e⁻¹ :=
  sorry

section ExtendDomain

/-! Lemmas about `Equiv.Perm.extendDomain` re-expressed via the group structure. -/


variable (e : Perm α) {p : β → Prop} [DecidablePred p] (f : α ≃ Subtype p)

@[target, simp]
theorem extendDomain_one : extendDomain 1 f = 1 :=
  sorry

@[simp]
theorem extendDomain_inv : (e.extendDomain f)⁻¹ = e⁻¹.extendDomain f :=
  rfl

@[simp]
theorem extendDomain_mul (e e' : Perm α) :
    e.extendDomain f * e'.extendDomain f = (e * e').extendDomain f :=
  extendDomain_trans _ _ _

/-- `extendDomain` as a group homomorphism -/
@[simps]
def extendDomainHom : Perm α →* Perm β where
  toFun e := extendDomain e f
  map_one' := extendDomain_one f
  map_mul' e e' := (extendDomain_mul f e e').symm

@[target]
theorem extendDomainHom_injective : Function.Injective (extendDomainHom f) :=
  sorry

@[target, simp]
theorem extendDomain_eq_one_iff {e : Perm α} {f : α ≃ Subtype p} : e.extendDomain f = 1 ↔ e = 1 :=
  sorry

@[target, simp]
lemma extendDomain_pow (n : ℕ) : (e ^ n).extendDomain f = e.extendDomain f ^ n :=
  sorry

@[simp]
lemma extendDomain_zpow (n : ℤ) : (e ^ n).extendDomain f = e.extendDomain f ^ n :=
  map_zpow (extendDomainHom f) _ _

end ExtendDomain

section Subtype

variable {p : α → Prop} {f : Perm α}

/-- If the permutation `f` fixes the subtype `{x // p x}`, then this returns the permutation
  on `{x // p x}` induced by `f`. -/
def subtypePerm (f : Perm α) (h : ∀ x, p x ↔ p (f x)) : Perm { x // p x } where
  toFun := fun x => ⟨f x, (h _).1 x.2⟩
  invFun := fun x => ⟨f⁻¹ x, (h (f⁻¹ x)).2 <| by simpa using x.2⟩
  left_inv _ := by simp only [Perm.inv_apply_self, Subtype.coe_eta, Subtype.coe_mk]
  right_inv _ := by simp only [Perm.apply_inv_self, Subtype.coe_eta, Subtype.coe_mk]

@[target, simp]
theorem subtypePerm_apply (f : Perm α) (h : ∀ x, p x ↔ p (f x)) (x : { x // p x }) :
    subtypePerm f h x = ⟨f x, (h _).1 x.2⟩ :=
  sorry

@[target, simp]
theorem subtypePerm_one (p : α → Prop) (h := sorry

@[target, simp]
theorem subtypePerm_mul (f g : Perm α) (hf hg) :
    (f.subtypePerm hf * g.subtypePerm hg : Perm { x // p x }) =
      (f * g).subtypePerm fun _ => (hg _).trans <| hf _ :=
  sorry
@[target]
theorem subtypePerm_inv (f : Perm α) (hf) :
    f⁻¹.subtypePerm hf = (f.subtypePerm <| inv_aux.2 hf : Perm { x // p x })⁻¹ :=
  sorry
@[simp]
theorem inv_subtypePerm (f : Perm α) (hf) :
    (f.subtypePerm hf : Perm { x // p x })⁻¹ = f⁻¹.subtypePerm (inv_aux.1 hf) :=
  rfl

private theorem pow_aux (hf : ∀ x, p x ↔ p (f x)) : ∀ {n : ℕ} (x), p x ↔ p ((f ^ n) x)
  | 0, _ => Iff.rfl
  | _ + 1, _ => (hf _).trans (pow_aux hf _)

@[simp]
theorem subtypePerm_pow (f : Perm α) (n : ℕ) (hf) :
    (f.subtypePerm hf : Perm { x // p x }) ^ n = (f ^ n).subtypePerm (pow_aux hf) := by
  induction n with
  | zero => simp
  | succ n ih => simp_rw [pow_succ', ih, subtypePerm_mul]

private theorem zpow_aux (hf : ∀ x, p x ↔ p (f x)) : ∀ {n : ℤ} (x), p x ↔ p ((f ^ n) x)
  | Int.ofNat _ => pow_aux hf
  | Int.negSucc n => by
    rw [zpow_negSucc]
    exact inv_aux.1 (pow_aux hf)

@[target, simp]
theorem subtypePerm_zpow (f : Perm α) (n : ℤ) (hf) :
    (f.subtypePerm hf ^ n : Perm { x // p x }) = (f ^ n).subtypePerm (zpow_aux hf) := by sorry

variable [DecidablePred p] {a : α}

/-- The inclusion map of permutations on a subtype of `α` into permutations of `α`,
  fixing the other points. -/
def ofSubtype : Perm (Subtype p) →* Perm α where
  toFun f := extendDomain f (Equiv.refl (Subtype p))
  map_one' := Equiv.Perm.extendDomain_one _
  map_mul' f g := (Equiv.Perm.extendDomain_mul _ f g).symm

@[target]
theorem ofSubtype_subtypePerm {f : Perm α} (h₁ : ∀ x, p x ↔ p (f x)) (h₂ : ∀ x, f x ≠ x → p x) :
    ofSubtype (subtypePerm f h₁) = f :=
  sorry

@[target]
theorem ofSubtype_apply_of_mem (f : Perm (Subtype p)) (ha : p a) : ofSubtype f a = f ⟨a, ha⟩ :=
  sorry

@[target, simp]
theorem ofSubtype_apply_coe (f : Perm (Subtype p)) (x : Subtype p) : ofSubtype f x = f x :=
  sorry

theorem ofSubtype_apply_of_not_mem (f : Perm (Subtype p)) (ha : ¬p a) : ofSubtype f a = a :=
  extendDomain_apply_not_subtype _ _ ha

@[target]
theorem mem_iff_ofSubtype_apply_mem (f : Perm (Subtype p)) (x : α) :
    p x ↔ p ((ofSubtype f : α → α) x) :=
  sorry

theorem ofSubtype_injective : Function.Injective (ofSubtype : Perm (Subtype p) → Perm α) := by
  intro x y h
  rw [Perm.ext_iff] at h ⊢
  intro a
  specialize h a
  rwa [ofSubtype_apply_coe, ofSubtype_apply_coe, SetCoe.ext_iff] at h

@[target, simp]
theorem subtypePerm_ofSubtype (f : Perm (Subtype p)) :
    subtypePerm (ofSubtype f) (mem_iff_ofSubtype_apply_mem f) = f :=
  sorry

theorem ofSubtype_subtypePerm_of_mem {p : α → Prop} [DecidablePred p]
    {g : Perm α} (hg : ∀ (x : α), p x ↔ p (g x))
    {a : α} (ha : p a) : (ofSubtype (g.subtypePerm hg)) a = g a :=
  ofSubtype_apply_of_mem (g.subtypePerm hg) ha

@[target]
theorem ofSubtype_subtypePerm_of_not_mem {p : α → Prop} [DecidablePred p]
    {g : Perm α} (hg : ∀ (x : α), p x ↔ p (g x))
    {a : α} (ha : ¬ p a) : (ofSubtype (g.subtypePerm hg)) a = a :=
  sorry
@[simps]
protected def subtypeEquivSubtypePerm (p : α → Prop) [DecidablePred p] :
    Perm (Subtype p) ≃ { f : Perm α // ∀ a, ¬p a → f a = a } where
  toFun f := ⟨ofSubtype f, fun _ => f.ofSubtype_apply_of_not_mem⟩
  invFun f :=
    (f : Perm α).subtypePerm fun a =>
      ⟨Decidable.not_imp_not.1 fun hfa => f.val.injective (f.prop _ hfa) ▸ hfa,
        Decidable.not_imp_not.1 fun ha hfa => ha <| f.prop a ha ▸ hfa⟩
  left_inv := Equiv.Perm.subtypePerm_ofSubtype
  right_inv f :=
    Subtype.ext ((Equiv.Perm.ofSubtype_subtypePerm _) fun a => Not.decidable_imp_symm <| f.prop a)

@[target]
theorem subtypeEquivSubtypePerm_apply_of_mem (f : Perm (Subtype p)) (h : p a) :
    (Perm.subtypeEquivSubtypePerm p f).1 a = f ⟨a, h⟩ :=
  sorry

theorem subtypeEquivSubtypePerm_apply_of_not_mem (f : Perm (Subtype p)) (h : ¬p a) :
    ((Perm.subtypeEquivSubtypePerm p) f).1 a = a :=
  f.ofSubtype_apply_of_not_mem h

end Subtype

end Perm

section Swap

variable [DecidableEq α]

@[target, simp]
theorem swap_inv (x y : α) : (swap x y)⁻¹ = swap x y :=
  sorry

@[simp]
theorem swap_mul_self (i j : α) : swap i j * swap i j = 1 :=
  swap_swap i j

theorem swap_mul_eq_mul_swap (f : Perm α) (x y : α) : swap x y * f = f * swap (f⁻¹ x) (f⁻¹ y) :=
  Equiv.ext fun z => by
    simp only [Perm.mul_apply, swap_apply_def]
    split_ifs <;>
      simp_all only [Perm.apply_inv_self, Perm.eq_inv_iff_eq, eq_self_iff_true, not_true]

@[target]
theorem mul_swap_eq_swap_mul (f : Perm α) (x y : α) : f * swap x y = swap (f x) (f y) * f := by sorry

@[target]
theorem swap_apply_apply (f : Perm α) (x y : α) : swap (f x) (f y) = f * swap x y * f⁻¹ := by sorry
@[target, simp]
theorem swap_mul_self_mul (i j : α) (σ : Perm α) : Equiv.swap i j * (Equiv.swap i j * σ) = σ := by sorry
@[target, simp]
theorem mul_swap_mul_self (i j : α) (σ : Perm α) : σ * Equiv.swap i j * Equiv.swap i j = σ := by sorry
@[target, simp]
theorem swap_mul_involutive (i j : α) : Function.Involutive (Equiv.swap i j * ·) :=
  sorry
@[simp]
theorem mul_swap_involutive (i j : α) : Function.Involutive (· * Equiv.swap i j) :=
  mul_swap_mul_self i j

@[target, simp]
theorem swap_eq_one_iff {i j : α} : swap i j = (1 : Perm α) ↔ i = j :=
  sorry

@[target]
theorem swap_mul_eq_iff {i j : α} {σ : Perm α} : swap i j * σ = σ ↔ i = j := by sorry

@[target]
theorem mul_swap_eq_iff {i j : α} {σ : Perm α} : σ * swap i j = σ ↔ i = j := by sorry

theorem swap_mul_swap_mul_swap {x y z : α} (hxy : x ≠ y) (hxz : x ≠ z) :
    swap y z * swap x y * swap y z = swap z x := by
  nth_rewrite 3 [← swap_inv]
  rw [← swap_apply_apply, swap_apply_left, swap_apply_of_ne_of_ne hxy hxz, swap_comm]

end Swap

section AddGroup
variable [AddGroup α] (a b : α)

@[simp] lemma addLeft_zero : Equiv.addLeft (0 : α) = 1 := ext zero_add

@[simp] lemma addRight_zero : Equiv.addRight (0 : α) = 1 := ext add_zero

@[simp] lemma addLeft_add : Equiv.addLeft (a + b) = Equiv.addLeft a * Equiv.addLeft b :=
  ext <| add_assoc _ _

@[simp] lemma addRight_add : Equiv.addRight (a + b) = Equiv.addRight b * Equiv.addRight a :=
  ext fun _ ↦ (add_assoc _ _ _).symm

@[simp] lemma inv_addLeft : (Equiv.addLeft a)⁻¹ = Equiv.addLeft (-a) := Equiv.coe_inj.1 rfl

@[simp] lemma inv_addRight : (Equiv.addRight a)⁻¹ = Equiv.addRight (-a) := Equiv.coe_inj.1 rfl

@[simp] lemma pow_addLeft (n : ℕ) : Equiv.addLeft a ^ n = Equiv.addLeft (n • a) := by
  ext; simp [Perm.coe_pow]

@[simp] lemma pow_addRight (n : ℕ) : Equiv.addRight a ^ n = Equiv.addRight (n • a) := by
  ext; simp [Perm.coe_pow]

@[simp] lemma zpow_addLeft (n : ℤ) : Equiv.addLeft a ^ n = Equiv.addLeft (n • a) :=
  (map_zsmul ({ toFun := Equiv.addLeft, map_zero' := addLeft_zero, map_add' := addLeft_add } :
    α →+ Additive (Perm α)) _ _).symm

@[simp] lemma zpow_addRight : ∀ (n : ℤ), Equiv.addRight a ^ n = Equiv.addRight (n • a)
  | Int.ofNat n => by simp
  | Int.negSucc n => by simp

end AddGroup

section Group
variable [Group α] (a b : α)

@[to_additive existing (attr := simp)]
lemma mulLeft_one : Equiv.mulLeft (1 : α) = 1 := ext one_mul

@[to_additive existing (attr := simp)]
lemma mulRight_one : Equiv.mulRight (1 : α) = 1 := ext mul_one

@[to_additive existing (attr := simp)]
lemma mulLeft_mul : Equiv.mulLeft (a * b) = Equiv.mulLeft a * Equiv.mulLeft b :=
  ext <| mul_assoc _ _

@[target, to_additive existing (attr := sorry

@[target, to_additive existing (attr := sorry

@[target, to_additive existing (attr := sorry

@[target, to_additive existing (attr := by sorry

@[target, to_additive existing (attr := by sorry

@[to_additive existing (attr := simp) zpow_addLeft]
lemma zpow_mulLeft (n : ℤ) : Equiv.mulLeft a ^ n = Equiv.mulLeft (a ^ n) :=
  (map_zpow ({ toFun := Equiv.mulLeft, map_one' := mulLeft_one, map_mul' := mulLeft_mul } :
              α →* Perm α) _ _).symm

@[to_additive existing (attr := simp) zpow_addRight]
lemma zpow_mulRight : ∀ n : ℤ, Equiv.mulRight a ^ n = Equiv.mulRight (a ^ n)
  | Int.ofNat n => by simp
  | Int.negSucc n => by simp

end Group
end Equiv

/-- The group of multiplicative automorphisms. -/
@[reducible, to_additive "The group of additive automorphisms."]
def MulAut (M : Type*) [Mul M] :=
  M ≃* M

-- Note that `(attr := reducible)` in `to_additive` currently doesn't work,
-- so we add the reducible attribute manually.
attribute [reducible] AddAut

namespace MulAut

variable (M) [Mul M]

/-- The group operation on multiplicative automorphisms is defined by `g h => MulEquiv.trans h g`.
This means that multiplication agrees with composition, `(g*h)(x) = g (h x)`.
-/
instance : Group (MulAut M) where
  mul g h := MulEquiv.trans h g
  one := MulEquiv.refl _
  inv := MulEquiv.symm
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
  inv_mul_cancel := MulEquiv.self_trans_symm

instance : Inhabited (MulAut M) :=
  ⟨1⟩

@[simp]
theorem coe_mul (e₁ e₂ : MulAut M) : ⇑(e₁ * e₂) = e₁ ∘ e₂ :=
  rfl

@[simp]
theorem coe_one : ⇑(1 : MulAut M) = id :=
  rfl

theorem mul_def (e₁ e₂ : MulAut M) : e₁ * e₂ = e₂.trans e₁ :=
  rfl

theorem one_def : (1 : MulAut M) = MulEquiv.refl _ :=
  rfl

theorem inv_def (e₁ : MulAut M) : e₁⁻¹ = e₁.symm :=
  rfl

@[simp]
theorem mul_apply (e₁ e₂ : MulAut M) (m : M) : (e₁ * e₂) m = e₁ (e₂ m) :=
  rfl

@[simp]
theorem one_apply (m : M) : (1 : MulAut M) m = m :=
  rfl

@[simp]
theorem apply_inv_self (e : MulAut M) (m : M) : e (e⁻¹ m) = m :=
  MulEquiv.apply_symm_apply _ _

@[simp]
theorem inv_apply_self (e : MulAut M) (m : M) : e⁻¹ (e m) = m :=
  MulEquiv.apply_symm_apply _ _

/-- Monoid hom from the group of multiplicative automorphisms to the group of permutations. -/
def toPerm : MulAut M →* Equiv.Perm M where
  toFun := MulEquiv.toEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Group conjugation, `MulAut.conj g h = g * h * g⁻¹`, as a monoid homomorphism
mapping multiplication in `G` into multiplication in the automorphism group `MulAut G`.
See also the type `ConjAct G` for any group `G`, which has a `MulAction (ConjAct G) G` instance
where `conj G` acts on `G` by conjugation. -/
def conj [Group G] : G →* MulAut G where
  toFun g :=
    { toFun := fun h => g * h * g⁻¹
      invFun := fun h => g⁻¹ * h * g
      left_inv := fun _ => by simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
      right_inv := fun _ => by simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]
      map_mul' := by simp only [mul_assoc, inv_mul_cancel_left, forall_const] }
  map_mul' g₁ g₂ := by
    ext h
    show g₁ * g₂ * h * (g₁ * g₂)⁻¹ = g₁ * (g₂ * h * g₂⁻¹) * g₁⁻¹
    simp only [mul_assoc, mul_inv_rev]
  map_one' := by ext; simp only [one_mul, inv_one, mul_one, one_apply]; rfl

@[simp]
theorem conj_apply [Group G] (g h : G) : conj g h = g * h * g⁻¹ :=
  rfl

@[simp]
theorem conj_symm_apply [Group G] (g h : G) : (conj g).symm h = g⁻¹ * h * g :=
  rfl

@[simp]
theorem conj_inv_apply [Group G] (g h : G) : (conj g)⁻¹ h = g⁻¹ * h * g :=
  rfl

/-- Isomorphic groups have isomorphic automorphism groups. -/
@[simps]
def congr [Group G] {H : Type*} [Group H] (ϕ : G ≃* H) :
    MulAut G ≃* MulAut H where
  toFun f := ϕ.symm.trans (f.trans ϕ)
  invFun f := ϕ.trans (f.trans ϕ.symm)
  left_inv _ := by simp [DFunLike.ext_iff]
  right_inv _ := by simp [DFunLike.ext_iff]
  map_mul' := by simp [DFunLike.ext_iff]

end MulAut

namespace AddAut

variable (A) [Add A]

/-- The group operation on additive automorphisms is defined by `g h => AddEquiv.trans h g`.
This means that multiplication agrees with composition, `(g*h)(x) = g (h x)`.
-/
instance group : Group (AddAut A) where
  mul g h := AddEquiv.trans h g
  one := AddEquiv.refl _
  inv := AddEquiv.symm
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
  inv_mul_cancel := AddEquiv.self_trans_symm

instance : Inhabited (AddAut A) :=
  ⟨1⟩

@[target, simp]
theorem coe_mul (e₁ e₂ : AddAut A) : ⇑(e₁ * e₂) = e₁ ∘ e₂ :=
  sorry

@[simp]
theorem coe_one : ⇑(1 : AddAut A) = id :=
  rfl

@[target]
theorem mul_def (e₁ e₂ : AddAut A) : e₁ * e₂ = e₂.trans e₁ :=
  sorry

@[target]
theorem one_def : (1 : AddAut A) = AddEquiv.refl _ :=
  sorry

@[target]
theorem inv_def (e₁ : AddAut A) : e₁⁻¹ = e₁.symm :=
  sorry

@[target, simp]
theorem mul_apply (e₁ e₂ : AddAut A) (a : A) : (e₁ * e₂) a = e₁ (e₂ a) :=
  sorry

@[target, simp]
theorem one_apply (a : A) : (1 : AddAut A) a = a :=
  sorry

@[target, simp]
theorem apply_inv_self (e : AddAut A) (a : A) : e⁻¹ (e a) = a :=
  sorry

@[target, simp]
theorem inv_apply_self (e : AddAut A) (a : A) : e (e⁻¹ a) = a :=
  sorry
def toPerm : AddAut A →* Equiv.Perm A where
  toFun := AddEquiv.toEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Additive group conjugation, `AddAut.conj g h = g + h - g`, as an additive monoid
homomorphism mapping addition in `G` into multiplication in the automorphism group `AddAut G`
(written additively in order to define the map). -/
def conj [AddGroup G] : G →+ Additive (AddAut G) where
  toFun g :=
    @Additive.ofMul (AddAut G)
      { toFun := fun h => g + h + -g
        -- this definition is chosen to match `MulAut.conj`
        invFun := fun h => -g + h + g
        left_inv := fun _ => by
          simp only [add_assoc, neg_add_cancel_left, neg_add_cancel, add_zero]
        right_inv := fun _ => by
          simp only [add_assoc, add_neg_cancel_left, add_neg_cancel, add_zero]
        map_add' := by simp only [add_assoc, neg_add_cancel_left, forall_const] }
  map_add' g₁ g₂ := by
    apply Additive.toMul.injective; ext h
    show g₁ + g₂ + h + -(g₁ + g₂) = g₁ + (g₂ + h + -g₂) + -g₁
    simp only [add_assoc, neg_add_rev]
  map_zero' := by
    apply Additive.toMul.injective; ext
    simp only [zero_add, neg_zero, add_zero, toMul_ofMul, toMul_zero, one_apply]
    rfl

@[target, simp]
theorem conj_apply [AddGroup G] (g h : G) : conj g h = g + h + -g :=
  sorry

@[target, simp]
theorem conj_symm_apply [AddGroup G] (g h : G) : (conj g).symm h = -g + h + g :=
  sorry

@[target, simp]
theorem conj_inv_apply [AddGroup G] (g h : G) : (conj g).toMul⁻¹ h = -g + h + g :=
  sorry

@[target]
theorem neg_conj_apply [AddGroup G] (g h : G) : (-conj g) h = -g + h + g := by sorry
@[simps]
def congr [AddGroup G] {H : Type*} [AddGroup H] (ϕ : G ≃+ H) :
    AddAut G ≃* AddAut H where
  toFun f := ϕ.symm.trans (f.trans ϕ)
  invFun f := ϕ.trans (f.trans ϕ.symm)
  left_inv _ := by simp [DFunLike.ext_iff]
  right_inv _ := by simp [DFunLike.ext_iff]
  map_mul' := by simp [DFunLike.ext_iff]

end AddAut

variable (G)

/-- `Multiplicative G` and `G` have isomorphic automorphism groups. -/
@[simps!]
def MulAutMultiplicative [AddGroup G] : MulAut (Multiplicative G) ≃* AddAut G :=
  { AddEquiv.toMultiplicative.symm with map_mul' := fun _ _ ↦ rfl }

/-- `Additive G` and `G` have isomorphic automorphism groups. -/
@[simps!]
def AddAutAdditive [Group G] : AddAut (Additive G) ≃* MulAut G :=
  { MulEquiv.toAdditive.symm with map_mul' := fun _ _ ↦ rfl }
