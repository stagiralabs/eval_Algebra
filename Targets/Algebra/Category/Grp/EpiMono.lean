import VerifiedAgora.tagger
/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Monomorphisms and epimorphisms in `Group`
In this file, we prove monomorphisms in the category of groups are injective homomorphisms and
epimorphisms are surjective homomorphisms.
-/


noncomputable section

open scoped Pointwise

universe u v

namespace MonoidHom

open QuotientGroup

variable {A : Type u} {B : Type v}

section

variable [Group A] [Group B]

@[target, to_additive]
theorem ker_eq_bot_of_cancel {f : A →* B} (h : ∀ u v : f.ker →* A, f.comp u = f.comp v → u = v) :
    f.ker = ⊥ := by sorry

variable [CommGroup A] [CommGroup B]

@[target, to_additive]
theorem range_eq_top_of_cancel {f : A →* B}
    (h : ∀ u v : B →* B ⧸ f.range, u.comp f = v.comp f → u = v) : f.range = ⊤ := by sorry

end MonoidHom

section

open CategoryTheory

namespace Grp

variable {A B : Grp.{u}} (f : A ⟶ B)

@[to_additive]
theorem ker_eq_bot_of_mono [Mono f] : f.hom.ker = ⊥ :=
  MonoidHom.ker_eq_bot_of_cancel fun u v h => ConcreteCategory.ext_iff.mp <|
    (@cancel_mono _ _ _ _ _ f _ (ofHom u) (ofHom v)).1 <| ConcreteCategory.ext h

@[to_additive]
theorem mono_iff_ker_eq_bot : Mono f ↔ f.hom.ker = ⊥ :=
  ⟨fun _ => ker_eq_bot_of_mono f, fun h =>
    ConcreteCategory.mono_of_injective _ <| (MonoidHom.ker_eq_bot_iff f.hom).1 h⟩

@[to_additive]
theorem mono_iff_injective : Mono f ↔ Function.Injective f :=
  Iff.trans (mono_iff_ker_eq_bot f) <| MonoidHom.ker_eq_bot_iff f.hom

namespace SurjectiveOfEpiAuxs

local notation3 "X" => Set.range (· • (f.hom.range : Set B) : B → Set B)

/-- Define `X'` to be the set of all left cosets with an extra point at "infinity".
-/
inductive XWithInfinity
  | fromCoset : X → XWithInfinity
  | infinity : XWithInfinity

open XWithInfinity Equiv.Perm

local notation "X'" => XWithInfinity f

local notation "∞" => XWithInfinity.infinity

local notation "SX'" => Equiv.Perm X'

instance : SMul B X' where
  smul b x :=
    match x with
    | fromCoset y => fromCoset ⟨b • y, by
          rw [← y.2.choose_spec, leftCoset_assoc]
          let b' : B := y.2.choose
          use b * b'⟩
    | ∞ => ∞

theorem mul_smul (b b' : B) (x : X') : (b * b') • x = b • b' • x :=
  match x with
  | fromCoset y => by
    change fromCoset _ = fromCoset _
    simp only [leftCoset_assoc]
  | ∞ => rfl

@[target]
theorem one_smul (x : X') : (1 : B) • x = x :=
  sorry

@[target]
theorem fromCoset_eq_of_mem_range {b : B} (hb : b ∈ f.hom.range) :
    fromCoset ⟨b • ↑f.hom.range, b, rfl⟩ = fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩ := by sorry

theorem fromCoset_ne_of_nin_range {b : B} (hb : b ∉ f.hom.range) :
    fromCoset ⟨b • ↑f.hom.range, b, rfl⟩ ≠ fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩ := by
  intro r
  simp only [fromCoset.injEq, Subtype.mk.injEq] at r
  nth_rw 2 [show (f.hom.range : Set B) = (1 : B) • f.hom.range from (one_leftCoset _).symm] at r
  rw [leftCoset_eq_iff, mul_one] at r
  exact hb (inv_inv b ▸ Subgroup.inv_mem _ r)

instance : DecidableEq X' :=
  Classical.decEq _

/-- Let `τ` be the permutation on `X'` exchanging `f.hom.range` and the point at infinity.
-/
noncomputable def tau : SX' :=
  Equiv.swap (fromCoset ⟨↑f.hom.range, ⟨1, one_leftCoset _⟩⟩) ∞

local notation "τ" => tau f

theorem τ_apply_infinity : τ ∞ = fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩ :=
  Equiv.swap_apply_right _ _

theorem τ_apply_fromCoset : τ (fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩) = ∞ :=
  Equiv.swap_apply_left _ _

@[target]
theorem τ_apply_fromCoset' (x : B) (hx : x ∈ f.hom.range) :
    τ (fromCoset ⟨x • ↑f.hom.range, ⟨x, rfl⟩⟩) = ∞ :=
  sorry

theorem τ_symm_apply_fromCoset :
    Equiv.symm τ (fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩) = ∞ := by
  rw [tau, Equiv.symm_swap, Equiv.swap_apply_left]

theorem τ_symm_apply_infinity :
    Equiv.symm τ ∞ = fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩ := by
  rw [tau, Equiv.symm_swap, Equiv.swap_apply_right]

/-- Let `g : B ⟶ S(X')` be defined as such that, for any `β : B`, `g(β)` is the function sending
point at infinity to point at infinity and sending coset `y` to `β • y`.
-/
def g : B →* SX' where
  toFun β :=
    { toFun := fun x => β • x
      invFun := fun x => β⁻¹ • x
      left_inv := fun x => by
        dsimp only
        rw [← mul_smul, inv_mul_cancel, one_smul]
      right_inv := fun x => by
        dsimp only
        rw [← mul_smul, mul_inv_cancel, one_smul] }
  map_one' := by
    ext
    simp [one_smul]
  map_mul' b1 b2 := by
    ext
    simp [mul_smul]

local notation "g" => g f

/-- Define `h : B ⟶ S(X')` to be `τ g τ⁻¹`
-/
def h : B →* SX' where
  toFun β := ((τ).symm.trans (g β)).trans τ
  map_one' := by
    ext
    simp
  map_mul' b1 b2 := by
    ext
    simp

local notation "h" => h f

/-!
The strategy is the following: assuming `epi f`
* prove that `f.hom.range = {x | h x = g x}`;
* thus `f ≫ h = f ≫ g` so that `h = g`;
* but if `f` is not surjective, then some `x ∉ f.hom.range`, then `h x ≠ g x` at the coset
`f.hom.range`.
-/


theorem g_apply_fromCoset (x : B) (y : X) :
    g x (fromCoset y) = fromCoset ⟨x • ↑y,
      by obtain ⟨z, hz⟩ := y.2; exact ⟨x * z, by simp [← hz, smul_smul]⟩⟩ := rfl

theorem g_apply_infinity (x : B) : (g x) ∞ = ∞ := rfl

@[target]
theorem h_apply_infinity (x : B) (hx : x ∈ f.hom.range) : (h x) ∞ = ∞ := by sorry

theorem h_apply_fromCoset (x : B) :
    (h x) (fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩) =
      fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩ := by
    change ((τ).symm.trans (g x)).trans τ _ = _
    simp [-MonoidHom.coe_range, τ_symm_apply_fromCoset, g_apply_infinity, τ_apply_infinity]

@[target]
theorem h_apply_fromCoset' (x : B) (b : B) (hb : b ∈ f.hom.range) :
    h x (fromCoset ⟨b • f.hom.range, b, rfl⟩) = fromCoset ⟨b • ↑f.hom.range, b, rfl⟩ :=
  sorry

@[target]
theorem h_apply_fromCoset_nin_range (x : B) (hx : x ∈ f.hom.range) (b : B) (hb : b ∉ f.hom.range) :
    h x (fromCoset ⟨b • f.hom.range, b, rfl⟩) = fromCoset ⟨(x * b) • ↑f.hom.range, x * b, rfl⟩ := by sorry

@[target]
theorem agree : f.hom.range = { x | h x = g x } := by sorry

theorem comp_eq : (f ≫ ofHom g) = f ≫ ofHom h := by
  ext a
  simp only [hom_comp, hom_ofHom, MonoidHom.coe_comp, Function.comp_apply]
  have : f a ∈ { b | h b = g b } := by
    rw [← agree]
    use a
  rw [this]

theorem g_ne_h (x : B) (hx : x ∉ f.hom.range) : g ≠ h := by
  intro r
  replace r :=
    DFunLike.congr_fun (DFunLike.congr_fun r x) (fromCoset ⟨f.hom.range, ⟨1, one_leftCoset _⟩⟩)
  change _ = ((τ).symm.trans (g x)).trans τ _ at r
  rw [g_apply_fromCoset] at r
  simp only [MonoidHom.coe_range, Subtype.coe_mk, Equiv.symm_swap, Equiv.toFun_as_coe,
    Equiv.coe_trans, Function.comp_apply] at r
  erw [Equiv.swap_apply_left, g_apply_infinity, Equiv.swap_apply_right] at r
  exact fromCoset_ne_of_nin_range _ hx r

end SurjectiveOfEpiAuxs

@[target]
theorem surjective_of_epi [Epi f] : Function.Surjective f := by sorry

theorem epi_iff_surjective : Epi f ↔ Function.Surjective f :=
  ⟨fun _ => surjective_of_epi f, ConcreteCategory.epi_of_surjective f⟩

theorem epi_iff_range_eq_top : Epi f ↔ f.hom.range = ⊤ :=
  Iff.trans (epi_iff_surjective _) (Subgroup.eq_top_iff' f.hom.range).symm

end Grp

namespace AddGrp


variable {A B : AddGrp.{u}} (f : A ⟶ B)

theorem epi_iff_surjective : Epi f ↔ Function.Surjective f := by
  have i1 : Epi f ↔ Epi (groupAddGroupEquivalence.inverse.map f) := by
    refine ⟨?_, groupAddGroupEquivalence.inverse.epi_of_epi_map⟩
    intro e'
    apply groupAddGroupEquivalence.inverse.map_epi
  rwa [Grp.epi_iff_surjective] at i1

theorem epi_iff_range_eq_top : Epi f ↔ f.hom.range = ⊤ :=
  Iff.trans (epi_iff_surjective _) (AddSubgroup.eq_top_iff' f.hom.range).symm

end AddGrp

namespace Grp


variable {A B : Grp.{u}} (f : A ⟶ B)

@[to_additive AddGrp.forget_grp_preserves_mono]
instance forget_grp_preserves_mono : (forget Grp).PreservesMonomorphisms where
  preserves f e := by rwa [mono_iff_injective, ← CategoryTheory.mono_iff_injective] at e

@[to_additive AddGrp.forget_grp_preserves_epi]
instance forget_grp_preserves_epi : (forget Grp).PreservesEpimorphisms where
  preserves f e := by rwa [epi_iff_surjective, ← CategoryTheory.epi_iff_surjective] at e

end Grp

namespace CommGrp


variable {A B : CommGrp.{u}} (f : A ⟶ B)

@[target, to_additive]
theorem ker_eq_bot_of_mono [Mono f] : f.hom.ker = ⊥ :=
  sorry

@[target, to_additive]
theorem mono_iff_ker_eq_bot : Mono f ↔ f.hom.ker = ⊥ :=
  sorry

@[target, to_additive]
theorem mono_iff_injective : Mono f ↔ Function.Injective f :=
  sorry

@[to_additive]
theorem range_eq_top_of_epi [Epi f] : f.hom.range = ⊤ :=
  MonoidHom.range_eq_top_of_cancel fun u v h => ConcreteCategory.ext_iff.mp <|
    (@cancel_epi _ _ _ _ _ f _ (ofHom u) (ofHom v)).1 (ConcreteCategory.ext h)

@[target, to_additive]
theorem epi_iff_range_eq_top : Epi f ↔ f.hom.range = ⊤ :=
  sorry

@[target, to_additive]
theorem epi_iff_surjective : Epi f ↔ Function.Surjective f := by sorry

@[to_additive AddCommGrp.forget_commGrp_preserves_mono]
instance forget_commGrp_preserves_mono : (forget CommGrp).PreservesMonomorphisms where
  preserves f e := by rwa [mono_iff_injective, ← CategoryTheory.mono_iff_injective] at e

@[to_additive AddCommGrp.forget_commGrp_preserves_epi]
instance forget_commGrp_preserves_epi : (forget CommGrp).PreservesEpimorphisms where
  preserves f e := by rwa [epi_iff_surjective, ← CategoryTheory.epi_iff_surjective] at e

end CommGrp

end
