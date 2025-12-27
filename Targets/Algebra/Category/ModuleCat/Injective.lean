import VerifiedAgora.tagger
/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import Mathlib.Algebra.Module.Injective
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-!
# Injective objects in the category of $R$-modules
-/

open CategoryTheory

universe u v
variable (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M]
namespace Module

@[target]
theorem injective_object_of_injective_module [inj : Injective R M] :
    CategoryTheory.Injective (ModuleCat.of R M) where
  factors g f m :=
    sorry

@[target]
theorem injective_module_of_injective_object
    [inj : CategoryTheory.Injective <| ModuleCat.of R M] :
    Module.Injective R M where
  out X Y _ _ _ _ f hf g := by sorry

@[target]
theorem injective_iff_injective_object :
    Module.Injective R M ↔
    CategoryTheory.Injective (ModuleCat.of R M) :=
  sorry

end Module


instance ModuleCat.ulift_injective_of_injective.{v'}
    [Small.{v} R] [AddCommGroup M] [Module R M]
    [CategoryTheory.Injective <| ModuleCat.of R M] :
    CategoryTheory.Injective <| ModuleCat.of R (ULift.{v'} M) :=
  Module.injective_object_of_injective_module
    (inj := Module.ulift_injective_of_injective
      (inj := Module.injective_module_of_injective_object _ _))
