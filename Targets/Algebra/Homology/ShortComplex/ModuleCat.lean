import VerifiedAgora.tagger
/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.ShortComplex.ConcreteCategory
import Mathlib.Algebra.Category.ModuleCat.Colimits

/-!
# Homology and exactness of short complexes of modules

In this file, the homology of a short complex `S` of abelian groups is identified
with the quotient of `LinearMap.ker S.g` by the image of the morphism
`S.moduleCatToCycles : S.X₁ →ₗ[R] LinearMap.ker S.g` induced by `S.f`.

-/

universe v u

variable {R : Type u} [Ring R]

namespace CategoryTheory

open Limits

namespace ShortComplex

noncomputable instance : (forget₂ (ModuleCat.{v} R) Ab).PreservesHomology where

/-- Constructor for short complexes in `ModuleCat.{v} R` taking as inputs
linear maps `f` and `g` and the vanishing of their composition. -/
@[simps]
def moduleCatMk {X₁ X₂ X₃ : Type v} [AddCommGroup X₁] [AddCommGroup X₂] [AddCommGroup X₃]
    [Module R X₁] [Module R X₂] [Module R X₃] (f : X₁ →ₗ[R] X₂) (g : X₂ →ₗ[R] X₃)
    (hfg : g.comp f = 0) : ShortComplex (ModuleCat.{v} R) :=
  ShortComplex.mk (ModuleCat.ofHom f) (ModuleCat.ofHom g) (ModuleCat.hom_ext hfg)

variable (S : ShortComplex (ModuleCat.{v} R))

@[target, simp]
lemma moduleCat_zero_apply (x : S.X₁) : S.g (S.f x) = 0 :=
  sorry

@[target]
lemma moduleCat_exact_iff :
    S.Exact ↔ ∀ (x₂ : S.X₂) (_ : S.g x₂ = 0), ∃ (x₁ : S.X₁), S.f x₁ = x₂ :=
  sorry

lemma moduleCat_exact_iff_ker_sub_range :
    S.Exact ↔ LinearMap.ker S.g.hom ≤ LinearMap.range S.f.hom := by
  rw [moduleCat_exact_iff]
  aesop

lemma moduleCat_exact_iff_range_eq_ker :
    S.Exact ↔ LinearMap.range S.f.hom = LinearMap.ker S.g.hom := by
  rw [moduleCat_exact_iff_ker_sub_range]
  aesop

variable {S}

lemma Exact.moduleCat_range_eq_ker (hS : S.Exact) :
    LinearMap.range S.f.hom = LinearMap.ker S.g.hom := by
  simpa only [moduleCat_exact_iff_range_eq_ker] using hS

lemma ShortExact.moduleCat_injective_f (hS : S.ShortExact) :
    Function.Injective S.f :=
  hS.injective_f

lemma ShortExact.moduleCat_surjective_g (hS : S.ShortExact) :
    Function.Surjective S.g :=
  hS.surjective_g

variable (S)

@[target]
lemma ShortExact.moduleCat_exact_iff_function_exact :
    S.Exact ↔ Function.Exact S.f S.g := by sorry
@[simps]
def moduleCatMkOfKerLERange {X₁ X₂ X₃ : ModuleCat.{v} R} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃)
    (hfg : LinearMap.range f.hom ≤ LinearMap.ker g.hom) : ShortComplex (ModuleCat.{v} R) :=
  ShortComplex.mk f g (by aesop)

@[target]
lemma Exact.moduleCat_of_range_eq_ker {X₁ X₂ X₃ : ModuleCat.{v} R}
    (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (hfg : LinearMap.range f.hom = LinearMap.ker g.hom) :
    (moduleCatMkOfKerLERange f g (by rw [hfg])).Exact := by sorry
@[simps]
def moduleCatToCycles : S.X₁ →ₗ[R] LinearMap.ker S.g.hom where
  toFun x := ⟨S.f x, S.moduleCat_zero_apply x⟩
  map_add' x y := by aesop
  map_smul' a x := by aesop

/-- The homology of `S`, defined as the quotient of the kernel of `S.g` by
the image of `S.moduleCatToCycles` -/
abbrev moduleCatHomology :=
  ModuleCat.of R (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles)

/-- The canonical map `ModuleCat.of R (LinearMap.ker S.g) ⟶ S.moduleCatHomology`. -/
abbrev moduleCatHomologyπ : ModuleCat.of R (LinearMap.ker S.g.hom) ⟶ S.moduleCatHomology :=
  ModuleCat.ofHom (LinearMap.range S.moduleCatToCycles).mkQ

/-- The explicit left homology data of a short complex of modules that is
given by a kernel and a quotient given by the `LinearMap` API. -/
@[simps K H i π]
def moduleCatLeftHomologyData : S.LeftHomologyData where
  K := ModuleCat.of R (LinearMap.ker S.g.hom)
  H := S.moduleCatHomology
  i := ModuleCat.ofHom (LinearMap.ker S.g.hom).subtype
  π := S.moduleCatHomologyπ
  wi := by aesop
  hi := ModuleCat.kernelIsLimit _
  wπ := by aesop
  hπ := ModuleCat.cokernelIsColimit (ModuleCat.ofHom S.moduleCatToCycles)

@[target, simp]
lemma moduleCatLeftHomologyData_f' :
    S.moduleCatLeftHomologyData.f' = ModuleCat.ofHom S.moduleCatToCycles := sorry

instance : Epi S.moduleCatHomologyπ :=
  (inferInstance : Epi S.moduleCatLeftHomologyData.π)

/-- Given a short complex `S` of modules, this is the isomorphism between
the abstract `S.cycles` of the homology API and the more concrete description as
`LinearMap.ker S.g`. -/
noncomputable def moduleCatCyclesIso : S.cycles ≅ ModuleCat.of R (LinearMap.ker S.g.hom) :=
  S.moduleCatLeftHomologyData.cyclesIso

@[target, reassoc (attr := sorry

@[target, reassoc (attr := sorry

@[target, reassoc (attr := by sorry

@[reassoc (attr := simp, elementwise)]
lemma π_moduleCatCyclesIso_hom :
    S.homologyπ ≫ S.moduleCatHomologyIso.hom =
      S.moduleCatCyclesIso.hom ≫ S.moduleCatHomologyπ :=
  S.moduleCatLeftHomologyData.homologyπ_comp_homologyIso_hom

@[reassoc (attr := simp, elementwise)]
lemma moduleCatCyclesIso_inv_π :
    S.moduleCatCyclesIso.inv ≫ S.homologyπ =
       S.moduleCatHomologyπ ≫ S.moduleCatHomologyIso.inv :=
  S.moduleCatLeftHomologyData.π_comp_homologyIso_inv

lemma exact_iff_surjective_moduleCatToCycles :
    S.Exact ↔ Function.Surjective S.moduleCatToCycles := by
  rw [S.moduleCatLeftHomologyData.exact_iff_epi_f', moduleCatLeftHomologyData_f',
    ModuleCat.epi_iff_surjective]
  rfl

end ShortComplex

end CategoryTheory
