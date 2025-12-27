import VerifiedAgora.tagger
/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# The exterior powers as functors on the category of modules

In this file, given `M : ModuleCat R` and `n : ℕ`, we define `M.exteriorPower n : ModuleCat R`,
and this extends to a functor `ModuleCat.exteriorPower.functor : ModuleCat R ⥤ ModuleCat R`.

-/

universe v u

open CategoryTheory

namespace ModuleCat

variable {R : Type u} [CommRing R]

/-- The exterior power of an object in `ModuleCat R`. -/
def exteriorPower (M : ModuleCat.{v} R) (n : ℕ) : ModuleCat.{max u v} R :=
  ModuleCat.of R (⋀[R]^n M)

-- this could be an abbrev, but using a def eases automation
/-- The type of `n`-alternating maps on `M : ModuleCat R` to `N : ModuleCat R`. -/
def AlternatingMap (M : ModuleCat.{v} R) (N : ModuleCat.{max u v} R) (n : ℕ) :=
  _root_.AlternatingMap R M N (Fin n)

instance (M : ModuleCat.{v} R) (N : ModuleCat.{max u v} R) (n : ℕ) :
    FunLike (M.AlternatingMap N n) (Fin n → M) N :=
  inferInstanceAs (FunLike (M [⋀^(Fin n)]→ₗ[R] N) (Fin n → M) N)

namespace AlternatingMap

variable {M : ModuleCat.{v} R} {N : ModuleCat.{max u v} R} {n : ℕ}

@[target, ext]
lemma ext {φ φ' : M.AlternatingMap N n} (h : ∀ (x : Fin n → M), φ x = φ' x ) :
    φ = φ' :=
  sorry

variable (φ : M.AlternatingMap N n) {N' : ModuleCat.{max u v} R} (g : N ⟶ N')

/-- The postcomposition of an alternating map by a linear map. -/
def postcomp : M.AlternatingMap N' n :=
  g.hom.compAlternatingMap φ

@[target, simp]
lemma postcomp_apply (x : Fin n → M) :
    φ.postcomp g x = g (φ x) := sorry

end AlternatingMap

namespace exteriorPower

/-- Constructor for elements in `M.exteriorPower n` when `M` is an object of `ModuleCat R`
and `n : ℕ`. -/
def mk {M : ModuleCat.{v} R} {n : ℕ} :
    M.AlternatingMap (M.exteriorPower n) n :=
  exteriorPower.ιMulti _ _

@[ext]
lemma hom_ext {M : ModuleCat.{v} R} {N : ModuleCat.{max u v} R} {n : ℕ}
    {f g : M.exteriorPower n ⟶ N}
    (h : mk.postcomp f = mk.postcomp g) : f = g := by
  ext : 1
  exact exteriorPower.linearMap_ext h

/-- The morphism `M.exteriorPower n ⟶ N` induced by an alternating map. -/
noncomputable def desc {M : ModuleCat.{v} R} {n : ℕ} {N : ModuleCat.{max u v} R}
    (φ : M.AlternatingMap N n) : M.exteriorPower n ⟶ N :=
  ofHom (exteriorPower.alternatingMapLinearEquiv φ)

@[target, simp]
lemma desc_mk {M : ModuleCat.{v} R} {n : ℕ} {N : ModuleCat.{max u v} R}
    (φ : M.AlternatingMap N n) (x : Fin n → M) :
    desc φ (mk x) = φ x := by sorry

@[target, simp]
lemma map_mk {M N : ModuleCat.{v} R} (f : M ⟶ N) {n : ℕ} (x : Fin n → M) :
    map f n (mk x) = mk (f ∘ x) := by sorry

variable (R) in
/-- The functor `ModuleCat R ⥤ ModuleCat R` which sends a module to its
`n`th exterior power. -/
@[simps]
noncomputable def functor (n : ℕ) : ModuleCat.{v} R ⥤ ModuleCat.{max u v} R where
  obj M := M.exteriorPower n
  map f := map f n

/-- The isomorphism `M.exteriorPower 0 ≅ ModuleCat.of R R`. -/
noncomputable def iso₀ (M : ModuleCat.{u} R) : M.exteriorPower 0 ≅ ModuleCat.of R R :=
  (exteriorPower.zeroEquiv R M).toModuleIso

@[simp]
lemma iso₀_hom_apply {M : ModuleCat.{u} R} (f : Fin 0 → M) :
    (iso₀ M).hom (mk f) = 1 :=
  exteriorPower.zeroEquiv_ιMulti _

@[target, reassoc (attr := sorry

@[target, simp]
lemma iso₁_hom_apply {M : ModuleCat.{u} R} (f : Fin 1 → M) :
    (iso₁ M).hom (mk f) = f 0 :=
  sorry

@[reassoc (attr := simp)]
lemma iso₁_hom_naturality {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    map f 1 ≫ (iso₁ N).hom = (iso₁ M).hom ≫ f :=
  ModuleCat.hom_ext (exteriorPower.oneEquiv_naturality f.hom)

variable (R)

/-- The natural isomorphism `M.exteriorPower 0 ≅ ModuleCat.of R R`. -/
noncomputable def natIso₀ : functor.{u} R 0 ≅ (Functor.const _).obj (ModuleCat.of R R) :=
  NatIso.ofComponents iso₀

/-- The natural isomorphism `M.exteriorPower 1 ≅ M`. -/
noncomputable def natIso₁ : functor.{u} R 1 ≅ 𝟭 _ :=
  NatIso.ofComponents iso₁

end exteriorPower

end ModuleCat
