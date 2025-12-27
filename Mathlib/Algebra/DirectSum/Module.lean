import VerifiedAgora.tagger
/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Direct sum of modules

The first part of the file provides constructors for direct sums of modules. It provides a
construction of the direct sum using the universal property and proves its uniqueness
(`DirectSum.toModule.unique`).

The second part of the file covers the special case of direct sums of submodules of a fixed module
`M`.  There is a canonical linear map from this direct sum to `M` (`DirectSum.coeLinearMap`), and
the construction is of particular importance when this linear map is an equivalence; that is, when
the submodules provide an internal decomposition of `M`.  The property is defined more generally
elsewhere as `DirectSum.IsInternal`, but its basic consequences on `Submodule`s are established
in this file.

-/


universe u v w u₁

namespace DirectSum

open DirectSum Finsupp

section General

variable {R : Type u} [Semiring R]
variable {ι : Type v}
variable {M : ι → Type w} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

instance : Module R (⨁ i, M i) :=
  DFinsupp.module

instance {S : Type*} [Semiring S] [∀ i, Module S (M i)] [∀ i, SMulCommClass R S (M i)] :
    SMulCommClass R S (⨁ i, M i) :=
  DFinsupp.smulCommClass

instance {S : Type*} [Semiring S] [SMul R S] [∀ i, Module S (M i)] [∀ i, IsScalarTower R S (M i)] :
    IsScalarTower R S (⨁ i, M i) :=
  DFinsupp.isScalarTower

instance [∀ i, Module Rᵐᵒᵖ (M i)] [∀ i, IsCentralScalar R (M i)] : IsCentralScalar R (⨁ i, M i) :=
  DFinsupp.isCentralScalar

@[target] theorem smul_apply (n : M) (f : CentroidHom α) (a : α) : (n • f) a = n • f a := by sorry


variable (R ι M)

section DecidableEq

variable [DecidableEq ι]

/-- Create the direct sum given a family `M` of `R` modules indexed over `ι`. -/
/-- Create the direct sum given a family `M` of `R` modules indexed over `ι`. -/
def lmk : ∀ s : Finset ι, (∀ i : (↑s : Set ι), M i.val) →ₗ[R] ⨁ i, M i := by sorry


/-- Inclusion of each component into the direct sum. -/
/-- Inclusion of each component into the direct sum. -/
def lof : ∀ i : ι, M i →ₗ[R] ⨁ i, M i := by sorry


@[target] theorem lof_eq_of (i : ι) (b : M i) : lof R ι M i b = of M i b := by sorry


variable {ι M}

@[target] theorem single_eq_lof (i : ι) (b : M i) : DFinsupp.single i b = lof R ι M i b := by sorry


/-- Scalar multiplication commutes with direct sums. -/
/-- Scalar multiplication commutes with direct sums. -/
@[target] theorem mk_smul (s : Finset ι) (c : R) (x) : mk M s (c • x) = c • mk M s x := by sorry


/-- Scalar multiplication commutes with the inclusion of each component into the direct sum. -/
@[to_additive (attr := by sorry


variable {R}

@[target] lemma support_smul [Zero R] [Zero M] [SMulWithZero R M] [NoZeroSMulDivisors R M] (f : α → R)
    (g : α → M) : support (f • g) = support f ∩ support g := by sorry


variable {N : Type u₁} [AddCommMonoid N] [Module R N]
variable (φ : ∀ i, M i →ₗ[R] N)
variable (R ι N)

/-- The linear map constructed using the universal property of the coproduct. -/
instance (priority := 200) toModule {R A} {_ : CommSemiring R} {_ : Semiring A} [Algebra R A] :
    Module R A where
  one_smul _ := by sorry


/-- Coproducts in the categories of modules and additive monoids commute with the forgetful functor
from modules to additive monoids. -/
theorem coe_toModule_eq_coe_toAddMonoid :
    (toModule R ι N φ : (⨁ i, M i) → N) = toAddMonoid fun i ↦ (φ i).toAddMonoidHom := rfl

variable {ι N φ}

/-- The map constructed using the universal property gives back the original maps when
restricted to each component. -/
/-- The map constructed using the universal property gives back the original maps when
restricted to each component. -/
@[target] theorem toModule_lof (i) (x : M i) : toModule R ι N φ (lof R ι M i x) = φ i x := by sorry


variable (ψ : (⨁ i, M i) →ₗ[R] N)

/-- Every linear map from a direct sum agrees with the one obtained by applying
the universal property to each of its components. -/
theorem toModule.unique (f : ⨁ i, M i) : ψ f = toModule R ι N (fun i ↦ ψ.comp <| lof R ι M i) f :=
  toAddMonoid.unique ψ.toAddMonoidHom f

variable {ψ} {ψ' : (⨁ i, M i) →ₗ[R] N}

/-- Two `LinearMap`s out of a direct sum are equal if they agree on the generators.

See note [partially-applied ext lemmas]. -/
/-- Two `LinearMap`s out of a direct sum are equal if they agree on the generators.

See note [partially-applied ext lemmas]. -/
@[target] theorem linearMap_ext ⦃ψ ψ' : (⨁ i, M i) →ₗ[R] N⦄
    (H : ∀ i, ψ.comp (lof R ι M i) = ψ'.comp (lof R ι M i)) : ψ = ψ' := by sorry


/-- The inclusion of a subset of the direct summands
into a larger subset of the direct summands, as a linear map. -/
/-- The inclusion of a subset of the direct summands
into a larger subset of the direct summands, as a linear map. -/
def lsetToSet (S T : Set ι) (H : S ⊆ T) : (⨁ i : S, M i) →ₗ[R] ⨁ i : T, M i := by sorry


variable (ι M)

/-- Given `Fintype α`, `linearEquivFunOnFintype R` is the natural `R`-linear equivalence
between `⨁ i, M i` and `∀ i, M i`. -/
/-- Given `Fintype α`, `linearEquivFunOnFintype R` is the natural `R`-linear equivalence
between `⨁ i, M i` and `∀ i, M i`. -/
@[simps apply]
def linearEquivFunOnFintype [Fintype ι] : (⨁ i, M i) ≃ₗ[R] ∀ i, M i :=
  { DFinsupp.equivFunOnFintype with
    toFun := (↑)
    map_add' := fun f g ↦ by
      sorry


variable {ι M}

@[target] theorem linearEquivFunOnFintype_lof [Fintype ι] (i : ι) (m : M i) :
    (linearEquivFunOnFintype R ι M) (lof R ι M i m) = Pi.single i m := by
  sorry


@[target] theorem linearEquivFunOnFintype_symm_single [Fintype ι] (i : ι) (m : M i) :
    (linearEquivFunOnFintype R ι M).symm (Pi.single i m) = lof R ι M i m := by
  sorry


end DecidableEq

@[target] theorem linearEquivFunOnFintype_symm_coe [Fintype ι] (f : ⨁ i, M i) :
    (linearEquivFunOnFintype R ι M).symm f = f := by
  sorry


/-- The natural linear equivalence between `⨁ _ : ι, M` and `M` when `Unique ι`. -/
protected def lid (M : Type v) (ι : Type* := PUnit) [AddCommMonoid M] [Module R M] [Unique ι] :
    (⨁ _ : ι, M) ≃ₗ[R] M :=
  { DirectSum.id M ι, toModule R ι M fun _ ↦ LinearMap.id with }

/-- The projection map onto one component, as a linear map. -/
def component (i : ι) : (⨁ i, M i) →ₗ[R] M i :=
  DFinsupp.lapply i

variable {ι M}

@[target] theorem apply_eq_component (f : ⨁ i, M i) (i : ι) : f i = component R ι M i f := by sorry

@[target] theorem ext_component {f g : ⨁ i, M i} (h : ∀ i, component R ι M i f = component R ι M i g) :
    f = g := by sorry


@[target] theorem ext_component_iff {f g : ⨁ i, M i} :
    f = g ↔ ∀ i, component R ι M i f = component R ι M i g :=
  ⟨fun h _ ↦ by sorry


@[target] theorem lof_apply [DecidableEq ι] (i : ι) (b : M i) : ((lof R ι M i) b) i = b := by sorry


@[simp]
theorem component.lof_self [DecidableEq ι] (i : ι) (b : M i) :
    component R ι M i ((lof R ι M i) b) = b :=
  lof_apply R i b

theorem component.of [DecidableEq ι] (i j : ι) (b : M j) :
    component R ι M i ((lof R ι M j) b) = if h : j = i then Eq.recOn h b else 0 :=
  DFinsupp.single_apply

section map

variable {R} {N : ι → Type*} [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
  (f : Π i, M i →ₗ[R] N i)

/-- The linear map between direct sums induced by a family of linear maps. -/
/-- The linear map between direct sums induced by a family of linear maps. -/
def lmap : (⨁ i, M i) →ₗ[R] ⨁ i, N i := by sorry


@[target] theorem lmap_apply (x i) : lmap f x i = f i (x i) := by sorry


@[simp] theorem lmap_lof [DecidableEq ι] (i) (x : M i) :
    lmap f (lof R _ _ _ x) = lof R _ _ _ (f i x) :=
  DFinsupp.mapRange_single (hf := fun _ ↦ map_zero _)

@[target] theorem lmap_injective : Function.Injective (lmap f) ↔ ∀ i, Function.Injective (f i) := by
  sorry

  classical exact DFinsupp.mapRange_injective (hf := fun _ ↦ map_zero _)

end map

section CongrLeft

variable {κ : Type*}

/-- Reindexing terms of a direct sum is linear. -/
/-- Reindexing terms of a direct sum is linear. -/
def lequivCongrLeft (h : ι ≃ κ) : (⨁ i, M i) ≃ₗ[R] ⨁ k, M (h.symm k) := by sorry


@[target] theorem lequivCongrLeft_apply (h : ι ≃ κ) (f : ⨁ i, M i) (k : κ) :
    lequivCongrLeft R h f k = f (h.symm k) := by sorry


end CongrLeft

section Sigma

variable {α : ι → Type*} {δ : ∀ i, α i → Type w}
variable [DecidableEq ι] [∀ i j, AddCommMonoid (δ i j)] [∀ i j, Module R (δ i j)]

/-- `curry` as a linear map. -/
def sigmaLcurry : (⨁ i : Σ_, _, δ i.1 i.2) →ₗ[R] ⨁ (i) (j), δ i j :=
  { sigmaCurry with map_smul' := fun r ↦ by convert DFinsupp.sigmaCurry_smul (δ := δ) r }

@[target] theorem sigmaLcurry_apply (f : ⨁ i : Σ_, _, δ i.1 i.2) (i : ι) (j : α i) :
    sigmaLcurry R f i j = f ⟨i, j⟩ := by sorry


/-- `uncurry` as a linear map. -/
/-- `uncurry` as a linear map. -/
def sigmaLuncurry : (⨁ (i) (j), δ i j) →ₗ[R] ⨁ i : Σ_, _, δ i.1 i.2 := by sorry


@[simp]
theorem sigmaLuncurry_apply (f : ⨁ (i) (j), δ i j) (i : ι) (j : α i) :
    sigmaLuncurry R f ⟨i, j⟩ = f i j :=
  sigmaUncurry_apply f i j

/-- `curryEquiv` as a linear equiv. -/
/-- `curryEquiv` as a linear equiv. -/
def sigmaLcurryEquiv : (⨁ i : Σ_, _, δ i.1 i.2) ≃ₗ[R] ⨁ (i) (j), δ i j := by sorry


end Sigma

section Option

variable {α : Option ι → Type w} [∀ i, AddCommMonoid (α i)] [∀ i, Module R (α i)]

/-- Linear isomorphism obtained by separating the term of index `none` of a direct sum over
`Option ι`. -/
@[simps]
noncomputable def lequivProdDirectSum : (⨁ i, α i) ≃ₗ[R] α none × ⨁ i, α (some i) :=
  { addEquivProdDirectSum with map_smul' := DFinsupp.equivProdDFinsupp_smul }

end Option

end General

section Submodule

section Semiring

variable {R : Type u} [Semiring R]
variable {ι : Type v} [dec_ι : DecidableEq ι]
variable {M : Type*} [AddCommMonoid M] [Module R M]
variable (A : ι → Submodule R M)

/-- The canonical linear map from `⨁ i, A i` to `M` where `A` is a collection of `Submodule R M`
indexed by `ι`. This is `DirectSum.coeAddMonoidHom` as a `LinearMap`. -/
/-- The canonical linear map from `⨁ i, A i` to `M` where `A` is a collection of `Submodule R M`
indexed by `ι`. This is `DirectSum.coeAddMonoidHom` as a `LinearMap`. -/
def coeLinearMap : (⨁ i, A i) →ₗ[R] M := by sorry


@[target] theorem coeLinearMap_eq_dfinsupp_sum [DecidableEq M] (x : DirectSum ι fun i => A i) :
    coeLinearMap A x = DFinsupp.sum x fun i => (fun x : A i => ↑x) := by
  sorry


@[simp]
theorem coeLinearMap_of (i : ι) (x : A i) : DirectSum.coeLinearMap A (of (fun i ↦ A i) i x) = x :=
  -- Porting note: spelled out arguments. (I don't know how this works.)
  toAddMonoid_of (β := fun i => A i) (fun i ↦ ((A i).subtype : A i →+ M)) i x

variable {A}

@[target] theorem range_coeLinearMap : LinearMap.range (coeLinearMap A) = ⨆ i, A i := by sorry


@[simp]
theorem IsInternal.ofBijective_coeLinearMap_same (h : IsInternal A)
    {i : ι} (x : A i) :
    (LinearEquiv.ofBijective (coeLinearMap A) h).symm x i = x := by
  rw [← coeLinearMap_of, LinearEquiv.ofBijective_symm_apply_apply, of_eq_same]

@[simp]
theorem IsInternal.ofBijective_coeLinearMap_of_ne (h : IsInternal A)
    {i j : ι} (hij : i ≠ j) (x : A i) :
    (LinearEquiv.ofBijective (coeLinearMap A) h).symm x j = 0 := by
  rw [← coeLinearMap_of, LinearEquiv.ofBijective_symm_apply_apply, of_eq_of_ne i j _ hij]

theorem IsInternal.ofBijective_coeLinearMap_of_mem (h : IsInternal A)
    {i : ι} {x : M} (hx : x ∈ A i) :
    (LinearEquiv.ofBijective (coeLinearMap A) h).symm x i = ⟨x, hx⟩ :=
  h.ofBijective_coeLinearMap_same ⟨x, hx⟩

theorem IsInternal.ofBijective_coeLinearMap_of_mem_ne (h : IsInternal A)
    {i j : ι} (hij : i ≠ j) {x : M} (hx : x ∈ A i) :
    (LinearEquiv.ofBijective (coeLinearMap A) h).symm x j = 0 :=
  h.ofBijective_coeLinearMap_of_ne hij ⟨x, hx⟩

/-- If a direct sum of submodules is internal then the submodules span the module. -/
theorem IsInternal.submodule_iSup_eq_top (h : IsInternal A) : iSup A = ⊤ := by
  rw [Submodule.iSup_eq_range_dfinsupp_lsum, LinearMap.range_eq_top]
  exact Function.Bijective.surjective h

/-- If a direct sum of submodules is internal then the submodules are independent. -/
theorem IsInternal.submodule_iSupIndep (h : IsInternal A) : iSupIndep A :=
  iSupIndep_of_dfinsupp_lsum_injective _ h.injective

@[deprecated (since := "2024-11-24")]
alias IsInternal.submodule_independent := IsInternal.submodule_iSupIndep

/-- Given an internal direct sum decomposition of a module `M`, and a basis for each of the
components of the direct sum, the disjoint union of these bases is a basis for `M`. -/
noncomputable def IsInternal.collectedBasis (h : IsInternal A) {α : ι → Type*}
    (v : ∀ i, Basis (α i) R (A i)) : Basis (Σi, α i) R M where
  repr :=
    ((LinearEquiv.ofBijective (DirectSum.coeLinearMap A) h).symm ≪≫ₗ
        DFinsupp.mapRange.linearEquiv fun i ↦ (v i).repr) ≪≫ₗ
      (sigmaFinsuppLequivDFinsupp R).symm

@[simp]
theorem IsInternal.collectedBasis_coe (h : IsInternal A) {α : ι → Type*}
    (v : ∀ i, Basis (α i) R (A i)) : ⇑(h.collectedBasis v) = fun a : Σi, α i ↦ ↑(v a.1 a.2) := by
  funext a
  -- Porting note: was
  -- simp only [IsInternal.collectedBasis, toModule, coeLinearMap, Basis.coe_ofRepr,
  --   Basis.repr_symm_apply, DFinsupp.lsum_apply_apply, DFinsupp.mapRange.linearEquiv_apply,
  --   DFinsupp.mapRange.linearEquiv_symm, DFinsupp.mapRange_single, linearCombination_single,
  --   LinearEquiv.ofBijective_apply, LinearEquiv.symm_symm, LinearEquiv.symm_trans_apply, one_smul,
  --   sigmaFinsuppAddEquivDFinsupp_apply, sigmaFinsuppEquivDFinsupp_single,
  --   sigmaFinsuppLequivDFinsupp_apply]
  -- convert DFinsupp.sumAddHom_single (fun i ↦ (A i).subtype.toAddMonoidHom) a.1 (v a.1 a.2)
  simp only [IsInternal.collectedBasis, coeLinearMap, Basis.coe_ofRepr, LinearEquiv.trans_symm,
    LinearEquiv.symm_symm, LinearEquiv.trans_apply, sigmaFinsuppLequivDFinsupp_apply,
    sigmaFinsuppEquivDFinsupp_single, LinearEquiv.ofBijective_apply,
    sigmaFinsuppAddEquivDFinsupp_apply]
  rw [DFinsupp.mapRange.linearEquiv_symm]
  -- `DFunLike.coe (β := fun x ↦ ⨁ (i : ι), ↥(A i))`
  -- appears in the goal, but the lemma is expecting
  -- `DFunLike.coe (β := fun x ↦ Π₀ (i : ι), ↥(A i))`
  erw [DFinsupp.mapRange.linearEquiv_apply]
  simp only [DFinsupp.mapRange_single, Basis.repr_symm_apply, linearCombination_single, one_smul,
    toModule]
  -- Similarly here.
  erw [DFinsupp.lsum_single]
  simp only [Submodule.coe_subtype]

theorem IsInternal.collectedBasis_mem (h : IsInternal A) {α : ι → Type*}
    (v : ∀ i, Basis (α i) R (A i)) (a : Σi, α i) : h.collectedBasis v a ∈ A a.1 := by simp

theorem IsInternal.collectedBasis_repr_of_mem (h : IsInternal A) {α : ι → Type*}
    (v : ∀ i, Basis (α i) R (A i)) {x : M} {i : ι} {a : α i} (hx : x ∈ A i) :
    (h.collectedBasis v).repr x ⟨i, a⟩ = (v i).repr ⟨x, hx⟩ a := by
  change (sigmaFinsuppLequivDFinsupp R).symm (DFinsupp.mapRange _ (fun i ↦ map_zero _) _) _ = _
  simp [h.ofBijective_coeLinearMap_of_mem hx]

theorem IsInternal.collectedBasis_repr_of_mem_ne (h : IsInternal A) {α : ι → Type*}
    (v : ∀ i, Basis (α i) R (A i)) {x : M} {i j : ι} (hij : i ≠ j) {a : α j} (hx : x ∈ A i) :
    (h.collectedBasis v).repr x ⟨j, a⟩ = 0 := by
  change (sigmaFinsuppLequivDFinsupp R).symm (DFinsupp.mapRange _ (fun i ↦ map_zero _) _) _ = _
  simp [h.ofBijective_coeLinearMap_of_mem_ne hij hx]

/-- When indexed by only two distinct elements, `DirectSum.IsInternal` implies
the two submodules are complementary. Over a `Ring R`, this is true as an iff, as
`DirectSum.isInternal_submodule_iff_isCompl`. -/
theorem IsInternal.isCompl {A : ι → Submodule R M} {i j : ι} (hij : i ≠ j)
    (h : (Set.univ : Set ι) = {i, j}) (hi : IsInternal A) : IsCompl (A i) (A j) :=
  ⟨hi.submodule_iSupIndep.pairwiseDisjoint hij,
    codisjoint_iff.mpr <| Eq.symm <| hi.submodule_iSup_eq_top.symm.trans <| by
      rw [← sSup_pair, iSup, ← Set.image_univ, h, Set.image_insert_eq, Set.image_singleton]⟩

end Semiring

section Ring

variable {R : Type u} [Ring R]
variable {ι : Type v} [dec_ι : DecidableEq ι]
variable {M : Type*} [AddCommGroup M] [Module R M]

/-- Note that this is not generally true for `[Semiring R]`; see
`iSupIndep.dfinsupp_lsum_injective` for details. -/
/-- Note that this is not generally true for `[Semiring R]`; see
`iSupIndep.dfinsupp_lsum_injective` for details. -/
@[target] theorem isInternal_submodule_of_iSupIndep_of_iSup_eq_top {A : ι → Submodule R M}
    (hi : iSupIndep A) (hs : iSup A = ⊤) : IsInternal A := by sorry


@[deprecated (since := "2024-11-24")]
alias isInternal_submodule_of_independent_of_iSup_eq_top :=
  isInternal_submodule_of_iSupIndep_of_iSup_eq_top

/-- `iff` version of `DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top`,
`DirectSum.IsInternal.iSupIndep`, and `DirectSum.IsInternal.submodule_iSup_eq_top`. -/
/-- `iff` version of `DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top`,
`DirectSum.IsInternal.iSupIndep`, and `DirectSum.IsInternal.submodule_iSup_eq_top`. -/
@[target] theorem isInternal_submodule_iff_iSupIndep_and_iSup_eq_top (A : ι → Submodule R M) :
    IsInternal A ↔ iSupIndep A ∧ iSup A = ⊤ := by sorry


@[deprecated (since := "2024-11-24")]
alias isInternal_submodule_iff_independent_and_iSup_eq_top :=
  isInternal_submodule_iff_iSupIndep_and_iSup_eq_top

/-- If a collection of submodules has just two indices, `i` and `j`, then
`DirectSum.IsInternal` is equivalent to `isCompl`. -/
theorem isInternal_submodule_iff_isCompl (A : ι → Submodule R M) {i j : ι} (hij : i ≠ j)
    (h : (Set.univ : Set ι) = {i, j}) : IsInternal A ↔ IsCompl (A i) (A j) := by
  have : ∀ k, k = i ∨ k = j := fun k ↦ by simpa using Set.ext_iff.mp h k
  rw [isInternal_submodule_iff_iSupIndep_and_iSup_eq_top, iSup, ← Set.image_univ, h,
    Set.image_insert_eq, Set.image_singleton, sSup_pair, iSupIndep_pair hij this]
  exact ⟨fun ⟨hd, ht⟩ ↦ ⟨hd, codisjoint_iff.mpr ht⟩, fun ⟨hd, ht⟩ ↦ ⟨hd, ht.eq_top⟩⟩

@[target] theorem isInternal_ne_bot_iff {A : ι → Submodule R M} :
    IsInternal (fun i : {i // A i ≠ ⊥} ↦ A i) ↔ IsInternal A := by
  sorry


@[target] lemma isInternal_biSup_submodule_of_iSupIndep {A : ι → Submodule R M} (s : Set ι)
    (h : iSupIndep <| fun i : s ↦ A i) :
    IsInternal <| fun (i : s) ↦ (A i).comap (⨆ i ∈ s, A i).subtype := by
  sorry


@[deprecated (since := "2024-11-24")]
alias isInternal_biSup_submodule_of_independent := isInternal_biSup_submodule_of_iSupIndep

/-! Now copy the lemmas for subgroup and submonoids. -/


theorem IsInternal.addSubmonoid_iSupIndep {M : Type*} [AddCommMonoid M] {A : ι → AddSubmonoid M}
    (h : IsInternal A) : iSupIndep A :=
  iSupIndep_of_dfinsupp_sumAddHom_injective _ h.injective

@[deprecated (since := "2024-11-24")]
alias IsInternal.addSubmonoid_independent := IsInternal.addSubmonoid_iSupIndep

theorem IsInternal.addSubgroup_iSupIndep {G : Type*} [AddCommGroup G] {A : ι → AddSubgroup G}
    (h : IsInternal A) : iSupIndep A :=
  iSupIndep_of_dfinsupp_sumAddHom_injective' _ h.injective

@[deprecated (since := "2024-11-24")]
alias IsInternal.addSubgroup_independent := IsInternal.addSubgroup_iSupIndep

end Ring

end Submodule

end DirectSum
