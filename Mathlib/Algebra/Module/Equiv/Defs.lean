import VerifiedAgora.tagger
/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro, Anne Baanen,
  Frédéric Dupuis, Heather Macbeth
-/
import Mathlib.Algebra.Module.LinearMap.Defs

/-!
# (Semi)linear equivalences

In this file we define

* `LinearEquiv σ M M₂`, `M ≃ₛₗ[σ] M₂`: an invertible semilinear map. Here, `σ` is a `RingHom`
  from `R` to `R₂` and an `e : M ≃ₛₗ[σ] M₂` satisfies `e (c • x) = (σ c) • (e x)`. The plain
  linear version, with `σ` being `RingHom.id R`, is denoted by `M ≃ₗ[R] M₂`, and the
  star-linear version (with `σ` being `starRingEnd`) is denoted by `M ≃ₗ⋆[R] M₂`.

## Implementation notes

To ensure that composition works smoothly for semilinear equivalences, we use the typeclasses
`RingHomCompTriple`, `RingHomInvPair` and `RingHomSurjective` from
`Algebra/Ring/CompTypeclasses`.

The group structure on automorphisms, `LinearEquiv.automorphismGroup`, is provided elsewhere.

## TODO

* Parts of this file have not yet been generalized to semilinear maps

## Tags

linear equiv, linear equivalences, linear isomorphism, linear isomorphic
-/

assert_not_exists Field Pi.module

open Function

variable {R : Type*} {R₁ : Type*} {R₂ : Type*} {R₃ : Type*}
variable {S : Type*} {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}
variable {N₁ : Type*} {N₂ : Type*}

section

/-- A linear equivalence is an invertible linear map. -/
structure LinearEquiv {R : Type*} {S : Type*} [Semiring R] [Semiring S] (σ : R →+* S)
  {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (M : Type*) (M₂ : Type*)
  [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module S M₂] extends LinearMap σ M M₂, M ≃+ M₂

attribute [coe] LinearEquiv.toLinearMap

/-- The linear map underlying a linear equivalence. -/
add_decl_doc LinearEquiv.toLinearMap

/-- The additive equivalence of types underlying a linear equivalence. -/
add_decl_doc LinearEquiv.toAddEquiv

/-- The backwards directed function underlying a linear equivalence. -/
add_decl_doc LinearEquiv.invFun

/-- `LinearEquiv.invFun` is a right inverse to the linear equivalence's underlying function. -/
add_decl_doc LinearEquiv.right_inv

/-- `LinearEquiv.invFun` is a left inverse to the linear equivalence's underlying function. -/
add_decl_doc LinearEquiv.left_inv

/-- `M ≃ₛₗ[σ] M₂` denotes the type of linear equivalences between `M` and `M₂` over a
ring homomorphism `σ`. -/
notation:50 M " ≃ₛₗ[" σ "] " M₂ => LinearEquiv σ M M₂

/-- `M ≃ₗ [R] M₂` denotes the type of linear equivalences between `M` and `M₂` over
a plain linear map `M →ₗ M₂`. -/
notation:50 M " ≃ₗ[" R "] " M₂ => LinearEquiv (RingHom.id R) M M₂

/-- `SemilinearEquivClass F σ M M₂` asserts `F` is a type of bundled `σ`-semilinear equivs
`M → M₂`.

See also `LinearEquivClass F R M M₂` for the case where `σ` is the identity map on `R`.

A map `f` between an `R`-module and an `S`-module over a ring homomorphism `σ : R →+* S`
is semilinear if it satisfies the two properties `f (x + y) = f x + f y` and
`f (c • x) = (σ c) • f x`. -/
class SemilinearEquivClass (F : Type*) {R S : outParam Type*} [Semiring R] [Semiring S]
  (σ : outParam <| R →+* S) {σ' : outParam <| S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
  (M M₂ : outParam Type*) [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module S M₂]
  [EquivLike F M M₂]
  extends AddEquivClass F M M₂ : Prop where
  /-- Applying a semilinear equivalence `f` over `σ` to `r • x` equals `σ r • f x`. -/
  map_smulₛₗ : ∀ (f : F) (r : R) (x : M), f (r • x) = σ r • f x

-- `R, S, σ, σ'` become metavars, but it's OK since they are outparams.

/-- `LinearEquivClass F R M M₂` asserts `F` is a type of bundled `R`-linear equivs `M → M₂`.
This is an abbreviation for `SemilinearEquivClass F (RingHom.id R) M M₂`.
-/
abbrev LinearEquivClass (F : Type*) (R M M₂ : outParam Type*) [Semiring R] [AddCommMonoid M]
    [AddCommMonoid M₂] [Module R M] [Module R M₂] [EquivLike F M M₂] :=
  SemilinearEquivClass F (RingHom.id R) M M₂

end

namespace SemilinearEquivClass

variable (F : Type*) [Semiring R] [Semiring S]
variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂]
variable [Module R M] [Module S M₂] {σ : R →+* S} {σ' : S →+* R}

instance (priority := 100) [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
  [EquivLike F M M₂] [s : SemilinearEquivClass F σ M M₂] : SemilinearMapClass F σ M M₂ :=
  { s with }

variable {F}

/-- Reinterpret an element of a type of semilinear equivalences as a semilinear equivalence. -/
@[coe]
def semilinearEquiv [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    [EquivLike F M M₂] [SemilinearEquivClass F σ M M₂] (f : F) : M ≃ₛₗ[σ] M₂ :=
  { (f : M ≃+ M₂), (f : M →ₛₗ[σ] M₂) with }

/-- Reinterpret an element of a type of semilinear equivalences as a semilinear equivalence. -/
instance instCoeToSemilinearEquiv [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    [EquivLike F M M₂] [SemilinearEquivClass F σ M M₂] : CoeHead F (M ≃ₛₗ[σ] M₂) where
  coe f := semilinearEquiv f

end SemilinearEquivClass

namespace LinearEquiv

section AddCommMonoid

variable [Semiring R] [Semiring S]

section

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂]
variable [Module R M] [Module S M₂] {σ : R →+* S} {σ' : S →+* R}
variable [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]

instance : Coe (M ≃ₛₗ[σ] M₂) (M →ₛₗ[σ] M₂) :=
  ⟨toLinearMap⟩

-- This exists for compatibility, previously `≃ₗ[R]` extended `≃` instead of `≃+`.
/-- The equivalence of types underlying a linear equivalence. -/
def toEquiv : (M ≃ₛₗ[σ] M₂) → M ≃ M₂ := fun f ↦ f.toAddEquiv.toEquiv

theorem toEquiv_injective : Function.Injective (toEquiv : (M ≃ₛₗ[σ] M₂) → M ≃ M₂) :=
  fun ⟨⟨⟨_, _⟩, _⟩, _, _, _⟩ ⟨⟨⟨_, _⟩, _⟩, _, _, _⟩ h ↦
    (LinearEquiv.mk.injEq _ _ _ _ _ _ _ _).mpr
      ⟨LinearMap.ext (congr_fun (Equiv.mk.inj h).1), (Equiv.mk.inj h).2⟩

@[target] lemma toEquiv_inj {e₁ e₂ : G ≃+c[a, b] H} : e₁.toEquiv = e₂.toEquiv ↔ e₁ = e₂ := by sorry


@[target] theorem toLinearMap_injective :
    Function.Injective (toLinearMap : _ → A →ₗ[R] B) := by sorry


@[simp, norm_cast]
theorem toLinearMap_inj {e₁ e₂ : M ≃ₛₗ[σ] M₂} : (↑e₁ : M →ₛₗ[σ] M₂) = e₂ ↔ e₁ = e₂ :=
  toLinearMap_injective.eq_iff

instance : EquivLike (M ≃ₛₗ[σ] M₂) M M₂ where
  inv := LinearEquiv.invFun
  coe_injective' _ _ h _ := toLinearMap_injective (DFunLike.coe_injective h)
  left_inv := LinearEquiv.left_inv
  right_inv := LinearEquiv.right_inv

instance : SemilinearEquivClass (M ≃ₛₗ[σ] M₂) σ M M₂ where
  map_add := (·.map_add')
  map_smulₛₗ := (·.map_smul')

@[target] theorem coe_mk (f : A → B) (h₁ h₂ h₃ h₄) : ⇑(⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩ : A →ₛₙₐ[φ] B) = f := by sorry


@[target] theorem coe_injective : @Function.Injective (A →ₛₙₐ[φ] B) (A → B) (↑) := by
  sorry


end

section

variable [Semiring R₁] [Semiring R₂] [Semiring R₃]
variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂]
variable [AddCommMonoid M₃]
variable [AddCommMonoid N₁] [AddCommMonoid N₂]
variable {module_M : Module R M} {module_S_M₂ : Module S M₂} {σ : R →+* S} {σ' : S →+* R}
variable {re₁ : RingHomInvPair σ σ'} {re₂ : RingHomInvPair σ' σ}
variable (e e' : M ≃ₛₗ[σ] M₂)

@[simp]
protected theorem coe_coe {F : Type*} [FunLike F A B]
    [NonUnitalAlgSemiHomClass F φ A B] (f : F) :
    ⇑(f : A →ₛₙₐ[φ] B) = f := by sorry


@[simp]
theorem coe_toEquiv : ⇑(e.toEquiv) = e :=
  rfl

@[simp]
theorem coe_toLinearMap : ⇑e.toLinearMap = e :=
  rfl

@[target] theorem toFun_eq_coe (f : A →ₛₙₐ[φ] B) : f.toFun = ⇑f := by sorry


section

variable {e e'}

@[target] theorem Algebra.ext {S : Type u} {A : Type v} [CommSemiring S] [Semiring A] (h1 h2 : Algebra S A)
    (h : ∀ (r : S) (x : A), (by sorry


protected theorem congr_arg {x x'} : x = x' → e x = e x' :=
  DFunLike.congr_arg e

protected theorem congr_fun (h : e = e') (x : M) : e x = e' x :=
  DFunLike.congr_fun h x

end

section

variable (M R)

/-- The identity map is a linear equivalence. -/
@[target] lemma refl (A : CSA K) : IsBrauerEquivalent A A := by sorry


end

@[simp]
theorem refl_apply [Module R M] (x : M) : refl R M x = x :=
  rfl

/-- Linear equivalences are symmetric. -/
@[target] lemma symm {A B : CSA K} (h : IsBrauerEquivalent A B) : IsBrauerEquivalent B A := by sorry


/-- See Note [custom simps projection] -/
def Simps.apply {R : Type*} {S : Type*} [Semiring R] [Semiring S]
    {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    {M : Type*} {M₂ : Type*} [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module S M₂]
    (e : M ≃ₛₗ[σ] M₂) : M → M₂ :=
  e

/-- See Note [custom simps projection] -/
def Simps.symm_apply {R : Type*} {S : Type*} [Semiring R] [Semiring S]
    {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    {M : Type*} {M₂ : Type*} [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module S M₂]
    (e : M ≃ₛₗ[σ] M₂) : M₂ → M :=
  e.symm

initialize_simps_projections LinearEquiv (toFun → apply, invFun → symm_apply)

@[target] theorem invFun_eq_symm (f : R ≃+* S) : EquivLike.inv f = f.symm := by sorry


@[target] theorem coe_toEquiv_symm (e : R ≃+* S) : (e.symm : S ≃ R) = (e : R ≃ S).symm := by sorry


variable {module_M₁ : Module R₁ M₁} {module_M₂ : Module R₂ M₂} {module_M₃ : Module R₃ M₃}
variable {module_N₁ : Module R₁ N₁} {module_N₂ : Module R₁ N₂}
variable {σ₁₂ : R₁ →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R₁ →+* R₃}
variable {σ₂₁ : R₂ →+* R₁} {σ₃₂ : R₃ →+* R₂} {σ₃₁ : R₃ →+* R₁}
variable [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
variable [RingHomCompTriple σ₃₂ σ₂₁ σ₃₁]
variable {re₁₂ : RingHomInvPair σ₁₂ σ₂₁} {re₂₃ : RingHomInvPair σ₂₃ σ₃₂}
variable [RingHomInvPair σ₁₃ σ₃₁] {re₂₁ : RingHomInvPair σ₂₁ σ₁₂}
variable {re₃₂ : RingHomInvPair σ₃₂ σ₂₃} [RingHomInvPair σ₃₁ σ₁₃]
variable (e₁₂ : M₁ ≃ₛₗ[σ₁₂] M₂) (e₂₃ : M₂ ≃ₛₗ[σ₂₃] M₃)

set_option linter.unusedVariables false in
/-- Linear equivalences are transitive. -/
-- Note: the `RingHomCompTriple σ₃₂ σ₂₁ σ₃₁` is unused, but is convenient to carry around
-- implicitly for lemmas like `LinearEquiv.self_trans_symm`.
open Matrix in
@[target] lemma trans {A B C : CSA K} (hAB : IsBrauerEquivalent A B) (hBC : IsBrauerEquivalent B C) :
    IsBrauerEquivalent A C := by
  sorry


/-- `e₁ ≪≫ₗ e₂` denotes the composition of the linear equivalences `e₁` and `e₂`. -/
notation3:80 (name := transNotation) e₁:80 " ≪≫ₗ " e₂:81 =>
  @LinearEquiv.trans _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (RingHom.id _) (RingHom.id _) (RingHom.id _)
    (RingHom.id _) (RingHom.id _) (RingHom.id _) RingHomCompTriple.ids RingHomCompTriple.ids
    RingHomInvPair.ids RingHomInvPair.ids RingHomInvPair.ids RingHomInvPair.ids RingHomInvPair.ids
    RingHomInvPair.ids e₁ e₂

variable {e₁₂} {e₂₃}

@[simp]
theorem coe_toAddEquiv : e.toAddEquiv = e :=
  rfl

@[simp]
lemma coe_addEquiv_apply (x : M) : (e : M ≃+ M₂) x = e x := by
  rfl

/-- The two paths coercion can take to an `AddMonoidHom` are equivalent -/
theorem toAddMonoidHom_commutes : e.toLinearMap.toAddMonoidHom = e.toAddEquiv.toAddMonoidHom :=
  rfl

lemma coe_toAddEquiv_symm : (e₁₂.symm : M₂ ≃+ M₁) = (e₁₂ : M₁ ≃+ M₂).symm := by
  rfl

@[target] theorem trans_apply (e₁ : R ≃+* S) (e₂ : S ≃+* S') (a : R) : e₁.trans e₂ a = e₂ (e₁ a) := by sorry


@[target] theorem coe_trans (e₁ : R ≃+* S) (e₂ : S ≃+* S') : (e₁.trans e₂ : R → S') = e₂ ∘ e₁ := by sorry


@[simp]
theorem apply_symm_apply (c : M₂) : e (e.symm c) = c :=
  e.right_inv c

@[target] theorem symm_apply_apply (e : R ≃+* S) : ∀ x, e.symm (e x) = x := by sorry


@[simp]
theorem trans_symm : (e₁₂.trans e₂₃ : M₁ ≃ₛₗ[σ₁₃] M₃).symm = e₂₃.symm.trans e₁₂.symm :=
  rfl

theorem symm_trans_apply (c : M₃) :
    (e₁₂.trans e₂₃ : M₁ ≃ₛₗ[σ₁₃] M₃).symm c = e₁₂.symm (e₂₃.symm c) :=
  rfl

@[target] lemma trans_refl (e : G ≃+c[a, b] H) : e.trans (.refl b) = e := by sorry


@[target] lemma refl_trans (e : G ≃+c[a, b] H) : (refl a).trans e = e := by sorry


theorem symm_apply_eq {x y} : e.symm x = y ↔ x = e y :=
  e.toEquiv.symm_apply_eq

theorem eq_symm_apply {x y} : y = e.symm x ↔ e y = x :=
  e.toEquiv.eq_symm_apply

theorem eq_comp_symm {α : Type*} (f : M₂ → α) (g : M₁ → α) : f = g ∘ e₁₂.symm ↔ f ∘ e₁₂ = g :=
  e₁₂.toEquiv.eq_comp_symm f g

theorem comp_symm_eq {α : Type*} (f : M₂ → α) (g : M₁ → α) : g ∘ e₁₂.symm = f ↔ g = f ∘ e₁₂ :=
  e₁₂.toEquiv.comp_symm_eq f g

theorem eq_symm_comp {α : Type*} (f : α → M₁) (g : α → M₂) : f = e₁₂.symm ∘ g ↔ e₁₂ ∘ f = g :=
  e₁₂.toEquiv.eq_symm_comp f g

theorem symm_comp_eq {α : Type*} (f : α → M₁) (g : α → M₂) : e₁₂.symm ∘ g = f ↔ g = e₁₂ ∘ f :=
  e₁₂.toEquiv.symm_comp_eq f g

variable [RingHomCompTriple σ₂₁ σ₁₃ σ₂₃] [RingHomCompTriple σ₃₁ σ₁₂ σ₃₂]

theorem eq_comp_toLinearMap_symm (f : M₂ →ₛₗ[σ₂₃] M₃) (g : M₁ →ₛₗ[σ₁₃] M₃) :
    f = g.comp e₁₂.symm.toLinearMap ↔ f.comp e₁₂.toLinearMap = g := by
  constructor <;> intro H <;> ext
  · simp [H, e₁₂.toEquiv.eq_comp_symm f g]
  · simp [← H, ← e₁₂.toEquiv.eq_comp_symm f g]

theorem comp_toLinearMap_symm_eq (f : M₂ →ₛₗ[σ₂₃] M₃) (g : M₁ →ₛₗ[σ₁₃] M₃) :
    g.comp e₁₂.symm.toLinearMap = f ↔ g = f.comp e₁₂.toLinearMap := by
  constructor <;> intro H <;> ext
  · simp [← H, ← e₁₂.toEquiv.comp_symm_eq f g]
  · simp [H, e₁₂.toEquiv.comp_symm_eq f g]

theorem eq_toLinearMap_symm_comp (f : M₃ →ₛₗ[σ₃₁] M₁) (g : M₃ →ₛₗ[σ₃₂] M₂) :
    f = e₁₂.symm.toLinearMap.comp g ↔ e₁₂.toLinearMap.comp f = g := by
  constructor <;> intro H <;> ext
  · simp [H, e₁₂.toEquiv.eq_symm_comp f g]
  · simp [← H, ← e₁₂.toEquiv.eq_symm_comp f g]

theorem toLinearMap_symm_comp_eq (f : M₃ →ₛₗ[σ₃₁] M₁) (g : M₃ →ₛₗ[σ₃₂] M₂) :
    e₁₂.symm.toLinearMap.comp g = f ↔ g = e₁₂.toLinearMap.comp f := by
  constructor <;> intro H <;> ext
  · simp [← H, ← e₁₂.toEquiv.symm_comp_eq f g]
  · simp [H, e₁₂.toEquiv.symm_comp_eq f g]

@[simp]
theorem comp_toLinearMap_eq_iff (f g : M₃ →ₛₗ[σ₃₁] M₁) :
    e₁₂.toLinearMap.comp f = e₁₂.toLinearMap.comp g ↔ f = g := by
  refine ⟨fun h => ?_, congrArg e₁₂.comp⟩
  rw [← (toLinearMap_symm_comp_eq g (e₁₂.toLinearMap.comp f)).mpr h, eq_toLinearMap_symm_comp]

@[simp]
theorem eq_comp_toLinearMap_iff (f g : M₂ →ₛₗ[σ₂₃] M₃) :
    f.comp e₁₂.toLinearMap = g.comp e₁₂.toLinearMap ↔ f = g := by
  refine ⟨fun h => ?_, fun a ↦ congrFun (congrArg LinearMap.comp a) e₁₂.toLinearMap⟩
  rw [(eq_comp_toLinearMap_symm g (f.comp e₁₂.toLinearMap)).mpr h.symm, eq_comp_toLinearMap_symm]

@[target] theorem refl_symm : (StarAlgEquiv.refl : A ≃⋆ₐ[R] A).symm = StarAlgEquiv.refl := by sorry


@[simp]
theorem self_trans_symm (f : M₁ ≃ₛₗ[σ₁₂] M₂) : f.trans f.symm = LinearEquiv.refl R₁ M₁ := by
  ext x
  simp

@[target] theorem symm_trans_self (e : R ≃+* S) : e.symm.trans e = RingEquiv.refl S := by sorry


@[simp]
theorem refl_toLinearMap [Module R M] : (LinearEquiv.refl R M : M →ₗ[R] M) = LinearMap.id :=
  rfl

@[simp]
theorem comp_coe [Module R M] [Module R M₂] [Module R M₃] (f : M ≃ₗ[R] M₂) (f' : M₂ ≃ₗ[R] M₃) :
    (f' : M₂ →ₗ[R] M₃).comp (f : M →ₗ[R] M₂) = (f.trans f' : M ≃ₗ[R] M₃) :=
  rfl

@[target] theorem mk_coe (f : A →ₛₙₐ[φ] B) (h₁ h₂ h₃ h₄) : (⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩ : A →ₛₙₐ[φ] B) = f := by
  sorry


protected theorem map_add (a b : M) : e (a + b) = e a + e b :=
  map_add e a b

protected theorem map_zero : e 0 = 0 :=
  map_zero e

protected theorem map_smulₛₗ (c : R) (x : M) : e (c • x) = (σ : R → S) c • e x :=
  e.map_smul' c x

@[simp] -- Marked as `@[simp]` because `MulActionSemiHomClass.map_smulₛₗ` can't be.
protected theorem map_smul (f : A →ₛₙₐ[φ] B) (c : R) (x : A) : f (c • x) = (φ c) • f x := by sorry


theorem map_eq_zero_iff {x : M} : e x = 0 ↔ x = 0 :=
  e.toAddEquiv.map_eq_zero_iff

theorem map_ne_zero_iff {x : M} : e x ≠ 0 ↔ x ≠ 0 :=
  e.toAddEquiv.map_ne_zero_iff

@[target] theorem symm_symm (e : R ≃+* S) : e.symm.symm = e := by sorry


@[target] theorem symm_bijective : Function.Bijective (RingEquiv.symm : (R ≃+* S) → S ≃+* R) := by sorry


@[simp]
theorem mk_coe' (f h₁ h₂ h₃ h₄) :
    (LinearEquiv.mk ⟨⟨f, h₁⟩, h₂⟩ (⇑e) h₃ h₄ : M₂ ≃ₛₗ[σ'] M) = e.symm :=
  symm_bijective.injective <| ext fun _ ↦ rfl

/-- Auxiliary definition to avoid looping in `dsimp` with `LinearEquiv.symm_mk`. -/
@[target] theorem symm_mk (f : R → S) (g h₁ h₂ h₃ h₄) :
    (mk ⟨f, g, h₁, h₂⟩ h₃ h₄).symm =
      { symm_mk.aux f g h₁ h₂ h₃ h₄ with
        toFun := by sorry


@[simp]
theorem symm_mk (f h₁ h₂ h₃ h₄) :
    (⟨⟨⟨e, h₁⟩, h₂⟩, f, h₃, h₄⟩ : M ≃ₛₗ[σ] M₂).symm =
      { symm_mk.aux e f h₁ h₂ h₃ h₄ with
        toFun := f
        invFun := e } :=
  rfl

@[simp]
theorem coe_symm_mk [Module R M] [Module R M₂]
    {to_fun inv_fun map_add map_smul left_inv right_inv} :
    ⇑(⟨⟨⟨to_fun, map_add⟩, map_smul⟩, inv_fun, left_inv, right_inv⟩ : M ≃ₗ[R] M₂).symm = inv_fun :=
  rfl

protected theorem bijective : Function.Bijective e :=
  e.toEquiv.bijective

protected theorem injective : Function.Injective e :=
  e.toEquiv.injective

protected theorem surjective : Function.Surjective e :=
  e.toEquiv.surjective

protected theorem image_eq_preimage (s : Set M) : e '' s = e.symm ⁻¹' s :=
  e.toEquiv.image_eq_preimage s

protected theorem image_symm_eq_preimage (s : Set M₂) : e.symm '' s = e ⁻¹' s :=
  e.toEquiv.symm.image_eq_preimage s

end

/-- Interpret a `RingEquiv` `f` as an `f`-semilinear equiv. -/
@[simps]
def _root_.RingEquiv.toSemilinearEquiv (f : R ≃+* S) :
    haveI := RingHomInvPair.of_ringEquiv f
    haveI := RingHomInvPair.symm (↑f : R →+* S) (f.symm : S →+* R)
    R ≃ₛₗ[(↑f : R →+* S)] S :=
  haveI := RingHomInvPair.of_ringEquiv f
  haveI := RingHomInvPair.symm (↑f : R →+* S) (f.symm : S →+* R)
  { f with
    toFun := f
    map_smul' := f.map_mul }

variable [AddCommMonoid M]

/-- An involutive linear map is a linear equivalence. -/
def ofInvolutive {σ σ' : R →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    {_ : Module R M} (f : M →ₛₗ[σ] M) (hf : Involutive f) : M ≃ₛₗ[σ] M :=
  { f, hf.toPerm f with }

@[simp]
theorem coe_ofInvolutive {σ σ' : R →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    {_ : Module R M} (f : M →ₛₗ[σ] M) (hf : Involutive f) : ⇑(ofInvolutive f hf) = f :=
  rfl

end AddCommMonoid

end LinearEquiv
