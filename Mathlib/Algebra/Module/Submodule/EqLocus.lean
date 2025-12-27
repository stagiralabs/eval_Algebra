import VerifiedAgora.tagger
/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Module.Submodule.Ker

/-!
# The submodule of elements `x : M` such that `f x = g x`

## Main declarations

* `LinearMap.eqLocus`: the submodule of elements `x : M` such that `f x = g x`

## Tags
linear algebra, vector space, module

-/

variable {R : Type*} {R₂ : Type*}
variable {M : Type*} {M₂ : Type*}

/-! ### Properties of linear maps -/


namespace LinearMap

section AddCommMonoid

variable [Semiring R] [Semiring R₂]
variable [AddCommMonoid M] [AddCommMonoid M₂]
variable [Module R M] [Module R₂ M₂]

open Submodule

variable {τ₁₂ : R →+* R₂}

section

variable {F : Type*} [FunLike F M M₂] [SemilinearMapClass F τ₁₂ M M₂]

/-- A linear map version of `AddMonoidHom.eqLocusM` -/
/-- A linear map version of `AddMonoidHom.eqLocusM` -/
def eqLocus (f g : F) : Submodule R M :=
  { (f : M →+ M₂).eqLocusM g with
    carrier := { x | f x = g x }
    smul_mem' := fun {r} {x} (hx : _ = _) => show _ = _ by
      -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 changed `map_smulₛₗ` into `map_smulₛₗ _`
      sorry


@[target] theorem mem_eqLocus {x : M} {f g : F} : x ∈ eqLocus f g ↔ f x = g x := by sorry


@[target] theorem eqLocus_toAddSubmonoid (f g : F) :
    (eqLocus f g).toAddSubmonoid = (f : M →+ M₂).eqLocusM g := by sorry


@[simp]
theorem eqLocus_eq_top {f g : F} : eqLocus f g = ⊤ ↔ f = g := by
  simp [SetLike.ext_iff, DFunLike.ext_iff]

@[target] theorem eqLocus_same (f : F) : eqLocus f f = ⊤ := by sorry


@[target] theorem le_eqLocus {f g : F} {S : Submodule R M} : S ≤ eqLocus f g ↔ Set.EqOn f g S := by sorry

include τ₁₂ in
@[target] theorem eqOn_sup {f g : F} {S T : Submodule R M} (hS : Set.EqOn f g S) (hT : Set.EqOn f g T) :
    Set.EqOn f g ↑(S ⊔ T) := by
  sorry

@[target] theorem ext_on_codisjoint {f g : F} {S T : Submodule R M} (hST : Codisjoint S T)
    (hS : Set.EqOn f g S) (hT : Set.EqOn f g T) : f = g := by sorry


end

end AddCommMonoid

section Ring

variable [Ring R] [Ring R₂]
variable [AddCommGroup M] [AddCommGroup M₂]
variable [Module R M] [Module R₂ M₂]
variable {τ₁₂ : R →+* R₂}

open Submodule

@[target] theorem eqLocus_eq_ker_sub (f g : M →ₛₗ[τ₁₂] M₂) : eqLocus f g = ker (f - g) := by sorry


end Ring

end LinearMap
