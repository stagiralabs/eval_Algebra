import VerifiedAgora.tagger
/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Group.Opposite
import Mathlib.Algebra.GroupWithZero.InjSurj
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Logic.Equiv.Set
import Mathlib.Util.AssertExists

/-!
# (Semi)ring equivs

In this file we define an extension of `Equiv` called `RingEquiv`, which is a datatype representing
an isomorphism of `Semiring`s, `Ring`s, `DivisionRing`s, or `Field`s.

## Notations

* ``infixl ` ≃+* `:25 := RingEquiv``

The extended equiv have coercions to functions, and the coercion is the canonical notation when
treating the isomorphism as maps.

## Implementation notes

The fields for `RingEquiv` now avoid the unbundled `isMulHom` and `isAddHom`, as these are
deprecated.

Definition of multiplication in the groups of automorphisms agrees with function composition,
multiplication in `Equiv.Perm`, and multiplication in `CategoryTheory.End`, not with
`CategoryTheory.CategoryStruct.comp`.

## Tags

Equiv, MulEquiv, AddEquiv, RingEquiv, MulAut, AddAut, RingAut
-/

-- guard against import creep
assert_not_exists Field Fintype

variable {F α β R S S' : Type*}


/-- makes a `NonUnitalRingHom` from the bijective inverse of a `NonUnitalRingHom` -/
@[simps] def NonUnitalRingHom.inverse
    [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S]
    (f : R →ₙ+* S) (g : S → R)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) : S →ₙ+* R :=
  { (f : R →+ S).inverse g h₁ h₂, (f : R →ₙ* S).inverse g h₁ h₂ with toFun := g }

/-- makes a `RingHom` from the bijective inverse of a `RingHom` -/
@[simps] def RingHom.inverse [NonAssocSemiring R] [NonAssocSemiring S]
    (f : RingHom R S) (g : S → R)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) : S →+* R :=
  { (f : OneHom R S).inverse g h₁,
    (f : MulHom R S).inverse g h₁ h₂,
    (f : R →+ S).inverse g h₁ h₂ with toFun := g }

/-- An equivalence between two (non-unital non-associative semi)rings that preserves the
algebraic structure. -/
structure RingEquiv (R S : Type*) [Mul R] [Mul S] [Add R] [Add S] extends R ≃ S, R ≃* S, R ≃+ S

/-- Notation for `RingEquiv`. -/
infixl:25 " ≃+* " => RingEquiv

/-- The "plain" equivalence of types underlying an equivalence of (semi)rings. -/
add_decl_doc RingEquiv.toEquiv

/-- The equivalence of additive monoids underlying an equivalence of (semi)rings. -/
add_decl_doc RingEquiv.toAddEquiv

/-- The equivalence of multiplicative monoids underlying an equivalence of (semi)rings. -/
add_decl_doc RingEquiv.toMulEquiv

/-- `RingEquivClass F R S` states that `F` is a type of ring structure preserving equivalences.
You should extend this class when you extend `RingEquiv`. -/
class RingEquivClass (F R S : Type*) [Mul R] [Add R] [Mul S] [Add S] [EquivLike F R S]
  extends MulEquivClass F R S : Prop where
  /-- By definition, a ring isomorphism preserves the additive structure. -/
  map_add : ∀ (f : F) (a b), f (a + b) = f a + f b

namespace RingEquivClass

variable [EquivLike F R S]

-- See note [lower instance priority]
instance (priority := 100) toAddEquivClass [Mul R] [Add R]
    [Mul S] [Add S] [h : RingEquivClass F R S] : AddEquivClass F R S :=
  { h with }

-- See note [lower instance priority]
instance (priority := 100) toRingHomClass [NonAssocSemiring R] [NonAssocSemiring S]
    [h : RingEquivClass F R S] : RingHomClass F R S :=
  { h with
    map_zero := map_zero
    map_one := map_one }

-- See note [lower instance priority]
instance (priority := 100) toNonUnitalRingHomClass [NonUnitalNonAssocSemiring R]
    [NonUnitalNonAssocSemiring S] [h : RingEquivClass F R S] : NonUnitalRingHomClass F R S :=
  { h with
    map_zero := map_zero }

/-- Turn an element of a type `F` satisfying `RingEquivClass F α β` into an actual
`RingEquiv`. This is declared as the default coercion from `F` to `α ≃+* β`. -/
/-- Turn an element of a type `F` satisfying `RingEquivClass F α β` into an actual
`RingEquiv`. This is declared as the default coercion from `F` to `α ≃+* β`. -/
@[coe]
def toRingEquiv [Mul α] [Add α] [Mul β] [Add β] [EquivLike F α β] [RingEquivClass F α β] (f : F) :
    α ≃+* β := by sorry


end RingEquivClass

/-- Any type satisfying `RingEquivClass` can be cast into `RingEquiv` via
`RingEquivClass.toRingEquiv`. -/
instance [Mul α] [Add α] [Mul β] [Add β] [EquivLike F α β] [RingEquivClass F α β] :
    CoeTC F (α ≃+* β) :=
  ⟨RingEquivClass.toRingEquiv⟩

namespace RingEquiv

section Basic

variable [Mul R] [Mul S] [Add R] [Add S] [Mul S'] [Add S']

section coe

instance : EquivLike (R ≃+* S) R S where
  coe f := f.toFun
  inv f := f.invFun
  coe_injective' e f h₁ h₂ := by
    cases e
    cases f
    congr
    apply Equiv.coe_fn_injective h₁
  left_inv f := f.left_inv
  right_inv f := f.right_inv

instance : RingEquivClass (R ≃+* S) R S where
  map_add f := f.map_add'
  map_mul f := f.map_mul'

/-- Two ring isomorphisms agree if they are defined by the
    same underlying function. -/
@[target] theorem Algebra.ext {S : Type u} {A : Type v} [CommSemiring S] [Semiring A] (h1 h2 : Algebra S A)
    (h : ∀ (r : S) (x : A), (by sorry


protected theorem congr_arg {f : R ≃+* S} {x x' : R} : x = x' → f x = f x' :=
  DFunLike.congr_arg f

protected theorem congr_fun {f g : R ≃+* S} (h : f = g) (x : R) : f x = g x :=
  DFunLike.congr_fun h x

@[target] theorem coe_mk (f : A → B) (h₁ h₂ h₃ h₄) : ⇑(⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩ : A →ₛₙₐ[φ] B) = f := by sorry


@[target] theorem mk_coe (f : A →ₛₙₐ[φ] B) (h₁ h₂ h₃ h₄) : (⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩ : A →ₛₙₐ[φ] B) = f := by
  sorry


@[target] theorem toEquiv_eq_coe (f : R ≃+* S) : f.toEquiv = f := by sorry


@[simp]
theorem coe_toEquiv (f : R ≃+* S) : ⇑(f : R ≃ S) = f :=
  rfl

@[target] theorem toAddEquiv_eq_coe (f : R ≃+* S) : f.toAddEquiv = ↑f := by sorry


@[simp]
theorem toMulEquiv_eq_coe (f : R ≃+* S) : f.toMulEquiv = ↑f :=
  rfl

@[target] theorem coe_toMulEquiv (f : R ≃+* S) : ⇑(f : R ≃* S) = f := by sorry


@[target] theorem coe_toAddEquiv (f : R ≃+* S) : ⇑(f : R ≃+ S) = f := by sorry


end coe

section map

/-- A ring isomorphism preserves multiplication. -/
protected theorem map_mul (e : R ≃+* S) (x y : R) : e (x * y) = e x * e y :=
  map_mul e x y

/-- A ring isomorphism preserves addition. -/
protected theorem map_add (e : R ≃+* S) (x y : R) : e (x + y) = e x + e y :=
  map_add e x y

end map

section bijective

protected theorem bijective (e : R ≃+* S) : Function.Bijective e :=
  EquivLike.bijective e

protected theorem injective (e : R ≃+* S) : Function.Injective e :=
  EquivLike.injective e

protected theorem surjective (e : R ≃+* S) : Function.Surjective e :=
  EquivLike.surjective e

end bijective

variable (R)

section refl

/-- The identity map is a ring isomorphism. -/
@[target] lemma refl (A : CSA K) : IsBrauerEquivalent A A := by sorry


instance : Inhabited (R ≃+* R) :=
  ⟨RingEquiv.refl R⟩

@[target] theorem refl_apply (x : R) : RingEquiv.refl R x = x := by sorry


@[target] theorem coe_refl (R : Type*) [Mul R] [Add R] : ⇑(RingEquiv.refl R) = id := by sorry


@[deprecated coe_refl (since := "2025-02-10")]
alias coe_refl_id := coe_refl

@[simp]
theorem coe_addEquiv_refl : (RingEquiv.refl R : R ≃+ R) = AddEquiv.refl R :=
  rfl

@[target] theorem coe_mulEquiv_refl : (RingEquiv.refl R : R ≃* R) = MulEquiv.refl R := by sorry


end refl

variable {R}

section symm

/-- The inverse of a ring isomorphism is a ring isomorphism. -/
@[symm]
protected def symm (e : R ≃+* S) : S ≃+* R :=
  { e.toMulEquiv.symm, e.toAddEquiv.symm with }

@[target] theorem invFun_eq_symm (f : R ≃+* S) : EquivLike.inv f = f.symm := by sorry


@[target] theorem symm_symm (e : R ≃+* S) : e.symm.symm = e := by sorry


@[target] theorem symm_bijective : Function.Bijective (RingEquiv.symm : (R ≃+* S) → S ≃+* R) := by sorry


@[simp]
theorem mk_coe' (e : R ≃+* S) (f h₁ h₂ h₃ h₄) :
    (⟨⟨f, ⇑e, h₁, h₂⟩, h₃, h₄⟩ : S ≃+* R) = e.symm :=
  symm_bijective.injective <| ext fun _ => rfl

/-- Auxiliary definition to avoid looping in `dsimp` with `RingEquiv.symm_mk`. -/
@[target] theorem symm_mk (f : R → S) (g h₁ h₂ h₃ h₄) :
    (mk ⟨f, g, h₁, h₂⟩ h₃ h₄).symm =
      { symm_mk.aux f g h₁ h₂ h₃ h₄ with
        toFun := by sorry


@[simp]
theorem symm_mk (f : R → S) (g h₁ h₂ h₃ h₄) :
    (mk ⟨f, g, h₁, h₂⟩ h₃ h₄).symm =
      { symm_mk.aux f g h₁ h₂ h₃ h₄ with
        toFun := g
        invFun := f } :=
  rfl

@[simp]
theorem symm_refl : (RingEquiv.refl R).symm = RingEquiv.refl R :=
  rfl

@[target] theorem coe_toEquiv_symm (e : R ≃+* S) : (e.symm : S ≃ R) = (e : R ≃ S).symm := by sorry


@[target] theorem apply_symm_apply (e : R ≃+* S) : ∀ x, e (e.symm x) = x := by sorry


@[target] theorem symm_apply_apply (e : R ≃+* S) : ∀ x, e.symm (e x) = x := by sorry


@[target] theorem image_eq_preimage (e : R ≃+* S) (s : Set R) : e '' s = e.symm ⁻¹' s := by sorry


end symm

section simps

/-- See Note [custom simps projection] -/
def Simps.symm_apply (e : R ≃+* S) : S → R :=
  e.symm

initialize_simps_projections RingEquiv (toFun → apply, invFun → symm_apply)

end simps

section trans

/-- Transitivity of `RingEquiv`. -/
@[trans]
protected def trans (e₁ : R ≃+* S) (e₂ : S ≃+* S') : R ≃+* S' :=
  { e₁.toMulEquiv.trans e₂.toMulEquiv, e₁.toAddEquiv.trans e₂.toAddEquiv with }

@[target] theorem coe_trans (e₁ : R ≃+* S) (e₂ : S ≃+* S') : (e₁.trans e₂ : R → S') = e₂ ∘ e₁ := by sorry


@[target] theorem trans_apply (e₁ : R ≃+* S) (e₂ : S ≃+* S') (a : R) : e₁.trans e₂ a = e₂ (e₁ a) := by sorry


@[target] theorem symm_trans_apply (e₁ : R ≃+* S) (e₂ : S ≃+* S') (a : S') :
    (e₁.trans e₂).symm a = e₁.symm (e₂.symm a) := by sorry


@[target] theorem symm_trans (e₁ : R ≃+* S) (e₂ : S ≃+* S') : (e₁.trans e₂).symm = e₂.symm.trans e₁.symm := by sorry


@[target] theorem coe_mulEquiv_trans (e₁ : R ≃+* S) (e₂ : S ≃+* S') :
    (e₁.trans e₂ : R ≃* S') = (e₁ : R ≃* S).trans ↑e₂ := by sorry


@[target] theorem coe_addEquiv_trans (e₁ : R ≃+* S) (e₂ : S ≃+* S') :
    (e₁.trans e₂ : R ≃+ S') = (e₁ : R ≃+ S).trans ↑e₂ := by sorry


end trans

section unique

/-- The `RingEquiv` between two semirings with a unique element. -/
def ofUnique {M N} [Unique M] [Unique N] [Add M] [Mul M] [Add N] [Mul N] : M ≃+* N :=
  { AddEquiv.ofUnique, MulEquiv.ofUnique with }

@[deprecated (since := "2024-12-26")] alias ringEquivOfUnique := ofUnique

instance {M N} [Unique M] [Unique N] [Add M] [Mul M] [Add N] [Mul N] :
    Unique (M ≃+* N) where
  default := .ofUnique
  uniq _ := ext fun _ => Subsingleton.elim _ _

end unique

end Basic

section Opposite

open MulOpposite

/-- A ring iso `α ≃+* β` can equivalently be viewed as a ring iso `αᵐᵒᵖ ≃+* βᵐᵒᵖ`. -/
@[simps! symm_apply_apply symm_apply_symm_apply apply_apply apply_symm_apply]
protected def op {α β} [Add α] [Mul α] [Add β] [Mul β] :
    α ≃+* β ≃ (αᵐᵒᵖ ≃+* βᵐᵒᵖ) where
  toFun f := { AddEquiv.mulOp f.toAddEquiv, MulEquiv.op f.toMulEquiv with }
  invFun f := { AddEquiv.mulOp.symm f.toAddEquiv, MulEquiv.op.symm f.toMulEquiv with }
  left_inv f := by
    ext
    rfl
  right_inv f := by
    ext
    rfl

/-- The 'unopposite' of a ring iso `αᵐᵒᵖ ≃+* βᵐᵒᵖ`. Inverse to `RingEquiv.op`. -/
@[simp]
protected def unop {α β} [Add α] [Mul α] [Add β] [Mul β] : αᵐᵒᵖ ≃+* βᵐᵒᵖ ≃ (α ≃+* β) :=
  RingEquiv.op.symm

/-- A ring is isomorphic to the opposite of its opposite. -/
/-- An algebra is isomorphic to the opposite of its opposite. -/
@[simps!]
def opOp : A ≃ₐ[R] Aᵐᵒᵖᵐᵒᵖ where
  __ := by sorry


section NonUnitalCommSemiring

variable (R) [NonUnitalCommSemiring R]

/-- A non-unital commutative ring is isomorphic to its opposite. -/
/--
An algebra homomorphism `f : A →ₐ[R] B` such that `f x` commutes with `f y` for all `x, y` defines
an algebra homomorphism to `Bᵐᵒᵖ`. -/
/--
An algebra homomorphism `f : A →ₐ[R] B` such that `f x` commutes with `f y` for all `x, y` defines
an algebra homomorphism to `Bᵐᵒᵖ`. -/
/-- A commutative algebra is isomorphic to its opposite. -/
@[simps!]
def toOpposite : A ≃ₐ[R] Aᵐᵒᵖ where
  __ := by sorry


end NonUnitalCommSemiring

end Opposite

section NonUnitalSemiring

variable [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] (f : R ≃+* S) (x : R)

/-- A ring isomorphism sends zero to zero. -/
protected theorem map_zero : f 0 = 0 :=
  map_zero f

variable {x}

protected theorem map_eq_zero_iff : f x = 0 ↔ x = 0 :=
  EmbeddingLike.map_eq_zero_iff

@[target] theorem map_ne_zero_iff : f x ≠ 0 ↔ x ≠ 0 := by sorry


variable [FunLike F R S]

/-- Produce a ring isomorphism from a bijective ring homomorphism. -/
noncomputable def ofBijective [NonUnitalRingHomClass F R S] (f : F) (hf : Function.Bijective f) :
    R ≃+* S :=
  { Equiv.ofBijective f hf with
    map_mul' := map_mul f
    map_add' := map_add f }

@[target] theorem coe_ofBijective [NonUnitalRingHomClass F R S] (f : F) (hf : Function.Bijective f) :
    (ofBijective f hf : R → S) = f := by sorry


theorem ofBijective_apply [NonUnitalRingHomClass F R S] (f : F) (hf : Function.Bijective f)
    (x : R) : ofBijective f hf x = f x :=
  rfl

/-- Product of a singleton family of (non-unital non-associative semi)rings is isomorphic
to the only member of this family. -/
/-- Product of a singleton family of (non-unital non-associative semi)rings is isomorphic
to the only member of this family. -/
@[simps! (config := by sorry


/-- A family of ring isomorphisms `∀ j, (R j ≃+* S j)` generates a
ring isomorphisms between `∀ j, R j` and `∀ j, S j`.

This is the `RingEquiv` version of `Equiv.piCongrRight`, and the dependent version of
`RingEquiv.arrowCongr`.
-/
/-- A family of algebra equivalences `∀ i, (A₁ i ≃ₐ A₂ i)` generates a
multiplicative equivalence between `Π i, A₁ i` and `Π i, A₂ i`.

This is the `AlgEquiv` version of `Equiv.piCongrRight`, and the dependent version of
`AlgEquiv.arrowCongr`.
-/
@[simps apply]
def piCongrRight (e : ∀ i, A₁ i ≃ₐ[R] A₂ i) : (Π i, A₁ i) ≃ₐ[R] Π i, A₂ i :=
  { @RingEquiv.piCongrRight ι A₁ A₂ _ _ fun i ↦ (e i).toRingEquiv with
    toFun := fun x j ↦ e j (x j)
    invFun := fun x j ↦ (e j).symm (x j)
    commutes' := fun r ↦ by
      sorry


@[target] theorem piCongrRight_refl :
    (piCongrRight fun i ↦ (AlgEquiv.refl : A₁ i ≃ₐ[R] A₁ i)) = AlgEquiv.refl := by sorry


@[target] theorem piCongrRight_symm (e : ∀ i, A₁ i ≃ₐ[R] A₂ i) :
    (piCongrRight e).symm = piCongrRight fun i ↦ (e i).symm := by sorry


@[simp]
theorem piCongrRight_trans {ι : Type*} {R S T : ι → Type*}
    [∀ i, NonUnitalNonAssocSemiring (R i)] [∀ i, NonUnitalNonAssocSemiring (S i)]
    [∀ i, NonUnitalNonAssocSemiring (T i)] (e : ∀ i, R i ≃+* S i) (f : ∀ i, S i ≃+* T i) :
    (piCongrRight e).trans (piCongrRight f) = piCongrRight fun i => (e i).trans (f i) :=
  rfl

/-- Transport dependent functions through an equivalence of the base space.

This is `Equiv.piCongrLeft'` as a `RingEquiv`. -/
/-- Transport dependent functions through an equivalence of the base space.

This is `Equiv.piCongrLeft` as a `RingEquiv`. -/
@[simps!]
def piCongrLeft {ι ι' : Type*} (S : ι' → Type*) (e : ι ≃ ι')
    [∀ i, NonUnitalNonAssocSemiring (S i)] :
    ((i : ι) → S (e i)) ≃+* ((i : ι') → S i) := by sorry


@[simp]
theorem piCongrLeft'_symm {R : Type*} [NonUnitalNonAssocSemiring R] (e : α ≃ β) :
    (RingEquiv.piCongrLeft' (fun _ => R) e).symm = RingEquiv.piCongrLeft' _ e.symm := by
  simp only [piCongrLeft', RingEquiv.symm, MulEquiv.symm, Equiv.piCongrLeft'_symm]

/-- Transport dependent functions through an equivalence of the base space.

This is `Equiv.piCongrLeft` as a `RingEquiv`. -/
@[simps!]
def piCongrLeft {ι ι' : Type*} (S : ι' → Type*) (e : ι ≃ ι')
    [∀ i, NonUnitalNonAssocSemiring (S i)] :
    ((i : ι) → S (e i)) ≃+* ((i : ι') → S i) :=
  (RingEquiv.piCongrLeft' S e.symm).symm

/-- Splits the indices of ring `∀ (i : ι), Y i` along the predicate `p`. This is
`Equiv.piEquivPiSubtypeProd` as a `RingEquiv`. -/
/-- Splits the indices of ring `∀ (i : ι), Y i` along the predicate `p`. This is
`Equiv.piEquivPiSubtypeProd` as a `RingEquiv`. -/
@[simps!]
def piEquivPiSubtypeProd {ι : Type*} (p : ι → Prop) [DecidablePred p] (Y : ι → Type*)
    [∀ i, NonUnitalNonAssocSemiring (Y i)] :
    ((i : ι) → Y i) ≃+* ((i : { x : ι // p x }) → Y i) × ((i : { x : ι // ¬p x }) → Y i) where
  toEquiv := by sorry


/-- Product of ring equivalences. This is `Equiv.prodCongr` as a `RingEquiv`. -/
/-- Product of ring equivalences. This is `Equiv.prodCongr` as a `RingEquiv`. -/
@[simps!]
def prodCongr {R R' S S' : Type*} [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring R']
    [NonUnitalNonAssocSemiring S] [NonUnitalNonAssocSemiring S']
    (f : R ≃+* R') (g : S ≃+* S') :
    R × S ≃+* R' × S' where
  toEquiv := Equiv.prodCongr f g
  map_mul' _ _ := by
    sorry


@[target] theorem coe_prodCongr {R R' S S' : Type*} [NonUnitalNonAssocSemiring R]
    [NonUnitalNonAssocSemiring R'] [NonUnitalNonAssocSemiring S] [NonUnitalNonAssocSemiring S']
    (f : R ≃+* R') (g : S ≃+* S') :
    ⇑(RingEquiv.prodCongr f g) = Prod.map f g := by sorry


/-- This is `Equiv.piOptionEquivProd` as a `RingEquiv`. -/
/-- This is `Equiv.piOptionEquivProd` as a `RingEquiv`. -/
@[simps!]
def piOptionEquivProd {ι : Type*} {R : Option ι → Type*} [Π i, NonUnitalNonAssocSemiring (R i)] :
    (Π i, R i) ≃+* R none × (Π i, R (some i)) where
  toEquiv := by sorry


end NonUnitalSemiring

section Semiring

variable [NonAssocSemiring R] [NonAssocSemiring S] (f : R ≃+* S) (x : R)

/-- A ring isomorphism sends one to one. -/
protected theorem map_one : f 1 = 1 :=
  map_one f

variable {x}

protected theorem map_eq_one_iff : f x = 1 ↔ x = 1 :=
  EmbeddingLike.map_eq_one_iff

@[target] theorem map_ne_one_iff : f x ≠ 1 ↔ x ≠ 1 := by sorry


@[target] theorem coe_monoidHom_refl : (RingEquiv.refl R : R →* R) = MonoidHom.id R := by sorry


@[target] theorem coe_addMonoidHom_refl : (RingEquiv.refl R : R →+ R) = AddMonoidHom.id R := by sorry



@[target] theorem coe_ringHom_refl : (RingEquiv.refl R : R →+* R) = RingHom.id R := by sorry


@[target] theorem coe_monoidHom_trans [NonAssocSemiring S'] (e₁ : R ≃+* S) (e₂ : S ≃+* S') :
    (e₁.trans e₂ : R →* S') = (e₂ : S →* S').comp ↑e₁ := by sorry


@[target] theorem coe_addMonoidHom_trans [NonAssocSemiring S'] (e₁ : R ≃+* S) (e₂ : S ≃+* S') :
    (e₁.trans e₂ : R →+ S') = (e₂ : S →+ S').comp ↑e₁ := by sorry


@[target] theorem coe_ringHom_trans [NonAssocSemiring S'] (e₁ : R ≃+* S) (e₂ : S ≃+* S') :
    (e₁.trans e₂ : R →+* S') = (e₂ : S →+* S').comp ↑e₁ := by sorry


@[target] theorem comp_symm (e : R ≃+* S) : (e : R →+* S).comp (e.symm : S →+* R) = RingHom.id S := by sorry


@[target] theorem symm_comp (e : R ≃+* S) : (e.symm : S →+* R).comp (e : R →+* S) = RingHom.id R := by sorry


end Semiring

section NonUnitalRing

variable [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S] (f : R ≃+* S) (x y : R)

protected theorem map_neg : f (-x) = -f x :=
  map_neg f x

protected theorem map_sub : f (x - y) = f x - f y :=
  map_sub f x y

end NonUnitalRing

section Ring

variable [NonAssocRing R] [NonAssocRing S] (f : R ≃+* S)

protected theorem map_neg_one {F : Type*} [Ring β] [FunLike F α β] [RingHomClass F α β]
    (f : F) : map (f : α →* β) (-1) = -1 := by
  sorry


@[target] theorem map_eq_neg_one_iff {x : R} : f x = -1 ↔ x = -1 := by
  sorry


end Ring

section NonUnitalSemiringHom

variable [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] [NonUnitalNonAssocSemiring S']

/-- Reinterpret a ring equivalence as a non-unital ring homomorphism. -/
/-- Reinterpret a ring equivalence as a non-unital ring homomorphism. -/
def toNonUnitalRingHom (e : R ≃+* S) : R →ₙ+* S := by sorry


@[target] theorem toNonUnitalRingHom_injective :
    Function.Injective (toNonUnitalRingHom : R ≃+* S → R →ₙ+* S) := by sorry


@[target] theorem toNonUnitalRingHom_eq_coe (f : R ≃+* S) : f.toNonUnitalRingHom = ↑f := by sorry


@[target] theorem coe_toNonUnitalRingHom (f : R ≃+* S) : ⇑(f : R →ₙ+* S) = f := by sorry


@[target] theorem coe_nonUnitalRingHom_inj_iff {R S : Type*} [NonUnitalNonAssocSemiring R]
    [NonUnitalNonAssocSemiring S] (f g : R ≃+* S) : f = g ↔ (f : R →ₙ+* S) = g :=
  ⟨fun h => by sorry


@[simp]
theorem toNonUnitalRingHom_refl :
    (RingEquiv.refl R).toNonUnitalRingHom = NonUnitalRingHom.id R :=
  rfl

@[target] theorem toNonUnitalRingHom_apply_symm_toNonUnitalRingHom_apply (e : R ≃+* S) :
    ∀ y : S, e.toNonUnitalRingHom (e.symm.toNonUnitalRingHom y) = y := by sorry


@[target] theorem symm_toNonUnitalRingHom_apply_toNonUnitalRingHom_apply (e : R ≃+* S) :
    ∀ x : R, e.symm.toNonUnitalRingHom (e.toNonUnitalRingHom x) = x := by sorry


@[target] theorem toNonUnitalRingHom_trans (e₁ : R ≃+* S) (e₂ : S ≃+* S') :
    (e₁.trans e₂).toNonUnitalRingHom = e₂.toNonUnitalRingHom.comp e₁.toNonUnitalRingHom := by sorry


@[target] theorem toNonUnitalRingHomm_comp_symm_toNonUnitalRingHom (e : R ≃+* S) :
    e.toNonUnitalRingHom.comp e.symm.toNonUnitalRingHom = NonUnitalRingHom.id _ := by
  sorry


@[target] theorem symm_toNonUnitalRingHom_comp_toNonUnitalRingHom (e : R ≃+* S) :
    e.symm.toNonUnitalRingHom.comp e.toNonUnitalRingHom = NonUnitalRingHom.id _ := by
  sorry


end NonUnitalSemiringHom

section SemiringHom

variable [NonAssocSemiring R] [NonAssocSemiring S] [NonAssocSemiring S']

/-- Reinterpret a ring equivalence as a ring homomorphism. -/
/-- Reinterpret a ring equivalence as a ring homomorphism. -/
def toRingHom (e : R ≃+* S) : R →+* S := by sorry


@[target] theorem toRingHom_injective : Function.Injective (toRingHom : R ≃+* S → R →+* S) := by sorry


@[target] theorem toRingHom_eq_coe (f : A →ₐ[R] B) : f.toRingHom = f := by sorry


@[target] theorem coe_toRingHom (f : A →ₐ[R] B) : ⇑(f : A →+* B) = f := by sorry


@[target] theorem coe_ringHom_inj_iff {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S]
    (f g : R ≃+* S) : f = g ↔ (f : R →+* S) = g :=
  ⟨fun h => by sorry


/-- The two paths coercion can take to a `NonUnitalRingEquiv` are equivalent -/
/-- The two paths coercion can take to a `NonUnitalRingEquiv` are equivalent -/
@[target] theorem toNonUnitalRingHom_commutes (f : R ≃+* S) :
    ((f : R →+* S) : R →ₙ+* S) = (f : R →ₙ+* S) := by sorry


/-- Reinterpret a ring equivalence as a monoid homomorphism. -/
/-- Reinterpret a ring equivalence as a monoid homomorphism. -/
abbrev toMonoidHom (e : R ≃+* S) : R →* S := by sorry


/-- Reinterpret a ring equivalence as an `AddMonoid` homomorphism. -/
/-- Reinterpret a ring equivalence as an `AddMonoid` homomorphism. -/
abbrev toAddMonoidHom (e : R ≃+* S) : R →+ S := by sorry


/-- The two paths coercion can take to an `AddMonoidHom` are equivalent -/
/-- The two paths coercion can take to an `AddMonoidHom` are equivalent -/
@[target] theorem toAddMonoidMom_commutes (f : R ≃+* S) :
    (f : R →+* S).toAddMonoidHom = (f : R ≃+ S).toAddMonoidHom := by sorry


/-- The two paths coercion can take to a `MonoidHom` are equivalent -/
/-- The two paths coercion can take to a `MonoidHom` are equivalent -/
@[target] theorem toMonoidHom_commutes (f : R ≃+* S) :
    (f : R →+* S).toMonoidHom = (f : R ≃* S).toMonoidHom := by sorry


/-- The two paths coercion can take to an `Equiv` are equivalent -/
/-- The two paths coercion can take to an `Equiv` are equivalent -/
@[target] theorem toEquiv_commutes (f : R ≃+* S) : (f : R ≃+ S).toEquiv = (f : R ≃* S).toEquiv := by sorry


@[target] theorem toRingHom_refl : (RingEquiv.refl R).toRingHom = RingHom.id R := by sorry


@[target] theorem toMonoidHom_refl : (RingEquiv.refl R).toMonoidHom = MonoidHom.id R := by sorry


@[target] theorem toAddMonoidHom_refl : (RingEquiv.refl R).toAddMonoidHom = AddMonoidHom.id R := by sorry


@[target] theorem toRingHom_apply_symm_toRingHom_apply (e : R ≃+* S) :
    ∀ y : S, e.toRingHom (e.symm.toRingHom y) = y := by sorry


@[target] theorem symm_toRingHom_apply_toRingHom_apply (e : R ≃+* S) :
    ∀ x : R, e.symm.toRingHom (e.toRingHom x) = x := by sorry


@[target] theorem toRingHom_trans (e₁ : R ≃+* S) (e₂ : S ≃+* S') :
    (e₁.trans e₂).toRingHom = e₂.toRingHom.comp e₁.toRingHom := by sorry


@[target] theorem toRingHom_comp_symm_toRingHom (e : R ≃+* S) :
    e.toRingHom.comp e.symm.toRingHom = RingHom.id _ := by
  sorry


@[target] theorem symm_toRingHom_comp_toRingHom (e : R ≃+* S) :
    e.symm.toRingHom.comp e.toRingHom = RingHom.id _ := by
  sorry


/-- Construct an equivalence of rings from homomorphisms in both directions, which are inverses.
-/
/--
Construct an equivalence of rings from unital homomorphisms in both directions, which are inverses.
-/
@[simps]
def ofHomInv {R S F G : Type*} [NonAssocSemiring R] [NonAssocSemiring S]
    [FunLike F R S] [FunLike G S R] [RingHomClass F R S]
    [RingHomClass G S R] (hom : F) (inv : G)
    (hom_inv_id : (inv : S →+* R).comp (hom : R →+* S) = RingHom.id R)
    (inv_hom_id : (hom : R →+* S).comp (inv : S →+* R) = RingHom.id S) :
    R ≃+* S where
  toFun := by sorry


/--
Construct an equivalence of rings from unital homomorphisms in both directions, which are inverses.
-/
@[simps]
def ofHomInv {R S F G : Type*} [NonAssocSemiring R] [NonAssocSemiring S]
    [FunLike F R S] [FunLike G S R] [RingHomClass F R S]
    [RingHomClass G S R] (hom : F) (inv : G)
    (hom_inv_id : (inv : S →+* R).comp (hom : R →+* S) = RingHom.id R)
    (inv_hom_id : (hom : R →+* S).comp (inv : S →+* R) = RingHom.id S) :
    R ≃+* S where
  toFun := hom
  invFun := inv
  left_inv := DFunLike.congr_fun hom_inv_id
  right_inv := DFunLike.congr_fun inv_hom_id
  map_mul' := map_mul hom
  map_add' := map_add hom

end SemiringHom

variable [Semiring R] [Semiring S]

section GroupPower

protected theorem map_pow (f : R ≃+* S) (a) : ∀ n : ℕ, f (a ^ n) = f a ^ n :=
  map_pow f a

end GroupPower

end RingEquiv

namespace MulEquiv

/-- Gives a `RingEquiv` from an element of a `MulEquivClass` preserving addition. -/
def toRingEquiv {R S F : Type*} [Add R] [Add S] [Mul R] [Mul S] [EquivLike F R S]
    [MulEquivClass F R S] (f : F)
    (H : ∀ x y : R, f (x + y) = f x + f y) : R ≃+* S :=
  { (f : R ≃* S).toEquiv, (f : R ≃* S), AddEquiv.mk' (f : R ≃* S).toEquiv H with }

end MulEquiv

namespace AddEquiv

/-- Gives a `RingEquiv` from an element of an `AddEquivClass` preserving addition. -/
def toRingEquiv {R S F : Type*} [Add R] [Add S] [Mul R] [Mul S] [EquivLike F R S]
    [AddEquivClass F R S] (f : F)
    (H : ∀ x y : R, f (x * y) = f x * f y) : R ≃+* S :=
  { (f : R ≃+ S).toEquiv, (f : R ≃+ S), MulEquiv.mk' (f : R ≃+ S).toEquiv H with }

end AddEquiv

namespace RingEquiv

variable [Add R] [Add S] [Mul R] [Mul S]

@[target] theorem self_trans_symm (e : R ≃+* S) : e.trans e.symm = RingEquiv.refl R := by sorry


@[target] theorem symm_trans_self (e : R ≃+* S) : e.symm.trans e = RingEquiv.refl S := by sorry


end RingEquiv

namespace RingEquiv

variable [NonAssocSemiring R] [NonAssocSemiring S]

/-- If a ring homomorphism has an inverse, it is a ring isomorphism. -/
/-- If a ring homomorphism has an inverse, it is a ring isomorphism. -/
@[simps]
def ofRingHom (f : R →+* S) (g : S →+* R) (h₁ : f.comp g = RingHom.id S)
    (h₂ : g.comp f = RingHom.id R) : R ≃+* S := by sorry


@[target] theorem coe_ringHom_ofRingHom (f : R →+* S) (g : S →+* R) (h₁ h₂) : ofRingHom f g h₁ h₂ = f := by sorry


@[simp]
theorem ofRingHom_coe_ringHom (f : R ≃+* S) (g : S →+* R) (h₁ h₂) : ofRingHom (↑f) g h₁ h₂ = f :=
  ext fun _ ↦ rfl

@[target] theorem ofRingHom_symm (f : R →+* S) (g : S →+* R) (h₁ h₂) :
    (ofRingHom f g h₁ h₂).symm = ofRingHom g f h₂ h₁ := by sorry


end RingEquiv

namespace MulEquiv

/-- If two rings are isomorphic, and the second doesn't have zero divisors,
then so does the first. -/
protected theorem noZeroDivisors {A : Type*} (B : Type*) [MulZeroClass A] [MulZeroClass B]
    [NoZeroDivisors B] (e : A ≃* B) : NoZeroDivisors A :=
  e.injective.noZeroDivisors e (map_zero e) (map_mul e)

/-- If two rings are isomorphic, and the second is a domain, then so is the first. -/
protected theorem isDomain {A : Type*} (B : Type*) [Semiring A] [Semiring B] [IsDomain B]
    (e : A ≃* B) : IsDomain A :=
  { e.injective.isLeftCancelMulZero e (map_zero e) (map_mul e),
    e.injective.isRightCancelMulZero e (map_zero e) (map_mul e) with
    exists_pair_ne := ⟨e.symm 0, e.symm 1, e.symm.injective.ne zero_ne_one⟩ }

end MulEquiv
