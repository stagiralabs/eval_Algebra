import VerifiedAgora.tagger
/-
Copyright (c) 2023 Wrenna Robson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/
import Mathlib.Algebra.Group.Submonoid.Operations
import Mathlib.Algebra.Group.Submonoid.Pointwise
import Mathlib.Algebra.Group.Subgroup.Lattice

/-!

# Submonoid of units

Given a submonoid `S` of a monoid `M`, we define the subgroup `S.units` as the units of `S` as a
subgroup of `Mˣ`. That is to say, `S.units` contains all members of `S` which have a
two-sided inverse within `S`, as terms of type `Mˣ`.

We also define, for subgroups `S` of `Mˣ`, `S.ofUnits`, which is `S` considered as a submonoid
of `M`. `Submonoid.units` and `Subgroup.ofUnits` form a Galois coinsertion.

We also make the equivalent additive definitions.

# Implementation details
There are a number of other constructions which are multiplicatively equivalent to `S.units` but
which have a different type.

| Definition           | Type          |
|----------------------|---------------|
| `S.units`            | `Subgroup Mˣ` |
| `Sˣ`                 | `Type u`      |
| `IsUnit.submonoid S` | `Submonoid S` |
| `S.units.ofUnits`    | `Submonoid M` |

All of these are distinct from `S.leftInv`, which is the submonoid of `M` which contains
every member of `M` with a right inverse in `S`.
-/

variable {M : Type*} [Monoid M]

open Units

open Pointwise in
/-- The units of `S`, packaged as a subgroup of `Mˣ`. -/
@[to_additive "The additive units of `S`, packaged as an additive subgroup of `AddUnits M`."]
def Submonoid.units (S : Submonoid M) : Subgroup Mˣ where
  toSubmonoid := S.comap (coeHom M) ⊓ (S.comap (coeHom M))⁻¹
  inv_mem' ha := ⟨ha.2, ha.1⟩

/-- A subgroup of units represented as a submonoid of `M`. -/
@[to_additive "A additive subgroup of additive units represented as a additive submonoid of `M`."]
def Subgroup.ofUnits (S : Subgroup Mˣ) : Submonoid M := S.toSubmonoid.map (coeHom M)

@[to_additive]
lemma Submonoid.units_mono : Monotone (Submonoid.units (M := M)) :=
  fun _ _ hST _ ⟨h₁, h₂⟩ => ⟨hST h₁, hST h₂⟩

@[target, to_additive (attr := sorry

@[to_additive]
lemma Subgroup.ofUnits_mono : Monotone (Subgroup.ofUnits (M := M)) :=
  fun _ _ hST _ ⟨x, hx, hy⟩ => ⟨x, hST hx, hy⟩

@[target, to_additive (attr := sorry
@[to_additive "A Galois coinsertion exists between the coercion from a additive subgroup of
additive units to a additive submonoid and the reduction from a additive submonoid to its unit
group."]
def ofUnits_units_gci : GaloisCoinsertion (Subgroup.ofUnits (M := M)) (Submonoid.units) :=
  GaloisCoinsertion.monotoneIntro Submonoid.units_mono Subgroup.ofUnits_mono
  Submonoid.ofUnits_units_le Subgroup.units_ofUnits_eq

@[target, to_additive]
lemma ofUnits_units_gc : GaloisConnection (Subgroup.ofUnits (M := sorry

@[target, to_additive]
lemma ofUnits_le_iff_le_units (S : Submonoid M) (H : Subgroup Mˣ) :
    H.ofUnits ≤ S ↔ H ≤ S.units := sorry

namespace Submonoid

section Units

@[target, to_additive]
lemma mem_units_iff (S : Submonoid M) (x : Mˣ) : x ∈ S.units ↔
    ((x : M) ∈ S ∧ ((x⁻¹ : Mˣ) : M) ∈ S) := sorry

@[to_additive]
lemma mem_units_of_val_mem_inv_val_mem (S : Submonoid M) {x : Mˣ} (h₁ : (x : M) ∈ S)
    (h₂ : ((x⁻¹ : Mˣ) : M) ∈ S) : x ∈ S.units := ⟨h₁, h₂⟩

@[to_additive]
lemma val_mem_of_mem_units (S : Submonoid M) {x : Mˣ} (h : x ∈ S.units) : (x : M) ∈ S := h.1

@[target, to_additive]
lemma inv_val_mem_of_mem_units (S : Submonoid M) {x : Mˣ} (h : x ∈ S.units) :
    ((x⁻¹ : Mˣ) : M) ∈ S := sorry

@[target, to_additive]
lemma coe_inv_val_mul_coe_val (S : Submonoid M) {x : Sˣ} :
    ((x⁻¹ : Sˣ) : M) * ((x : Sˣ) : M) = 1 := sorry

@[target, to_additive]
lemma coe_val_mul_coe_inv_val (S : Submonoid M) {x : Sˣ} :
    ((x : Sˣ) : M) * ((x⁻¹ : Sˣ) : M) = 1 := sorry

@[target, to_additive]
lemma mk_inv_mul_mk_eq_one (S : Submonoid M) {x : Mˣ} (h : x ∈ S.units) :
    (⟨_, h.2⟩ : S) * ⟨_, h.1⟩ = 1 := sorry

@[to_additive]
lemma mk_mul_mk_inv_eq_one (S : Submonoid M) {x : Mˣ} (h : x ∈ S.units) :
    (⟨_, h.1⟩ : S) * ⟨_, h.2⟩ = 1 := Subtype.ext x.mul_inv

@[to_additive]
lemma mul_mem_units (S : Submonoid M) {x y : Mˣ} (h₁ : x ∈ S.units) (h₂ : y ∈ S.units) :
    x * y ∈ S.units := mul_mem h₁ h₂

@[target, to_additive]
lemma inv_mem_units (S : Submonoid M) {x : Mˣ} (h : x ∈ S.units) : x⁻¹ ∈ S.units := sorry

@[target, to_additive]
lemma inv_mem_units_iff (S : Submonoid M) {x : Mˣ} : x⁻¹ ∈ S.units ↔ x ∈ S.units := sorry
@[to_additive "The equivalence between the additive subgroup of additive units of
`S` and the type of additive units of `S`."]
def unitsEquivUnitsType (S : Submonoid M) : S.units ≃* Sˣ where
  toFun := fun ⟨_, h⟩ => ⟨⟨_, h.1⟩, ⟨_, h.2⟩, S.mk_mul_mk_inv_eq_one h, S.mk_inv_mul_mk_eq_one h⟩
  invFun := fun x => ⟨⟨_, _, S.coe_val_mul_coe_inv_val, S.coe_inv_val_mul_coe_val⟩, ⟨x.1.2, x.2.2⟩⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_mul' := fun _ _ => rfl

@[target, to_additive (attr := sorry

@[target, to_additive]
lemma units_inf (S T : Submonoid M) : (S ⊓ T).units = S.units ⊓ T.units :=
  sorry

@[target, to_additive]
lemma units_sInf {s : Set (Submonoid M)} : (sInf s).units = ⨅ S ∈ s, S.units :=
  sorry

@[target, to_additive]
lemma units_iInf {ι : Sort*} (f : ι → Submonoid M) : (iInf f).units = ⨅ (i : ι), (f i).units :=
  sorry

@[target, to_additive]
lemma units_iInf₂ {ι : Sort*} {κ : ι → Sort*} (f : (i : ι) → κ i → Submonoid M) :
    (⨅ (i : ι), ⨅ (j : κ i), f i j).units = ⨅ (i : ι), ⨅ (j : κ i), (f i j).units :=
  sorry

@[target, to_additive (attr := sorry

@[to_additive]
lemma units_surjective : Function.Surjective (units (M := M)) :=
  ofUnits_units_gci.u_surjective

@[target, to_additive]
lemma units_left_inverse :
    Function.LeftInverse (units (M := sorry
@[to_additive "The equivalence between the additive subgroup of additive units of
`S` and the additive submonoid of additive unit elements of `S`."]
noncomputable def unitsEquivIsUnitSubmonoid (S : Submonoid M) : S.units ≃* IsUnit.submonoid S :=
S.unitsEquivUnitsType.trans unitsTypeEquivIsUnitSubmonoid

end Units

end Submonoid

namespace Subgroup

@[target, to_additive]
lemma mem_ofUnits_iff (S : Subgroup Mˣ) (x : M) : x ∈ S.ofUnits ↔ ∃ y ∈ S, y = x := sorry

@[to_additive]
lemma mem_ofUnits (S : Subgroup Mˣ) {x : M} {y : Mˣ} (h₁ : y ∈ S) (h₂ : y = x) : x ∈ S.ofUnits :=
  ⟨_, h₁, h₂⟩

@[target, to_additive]
lemma exists_mem_ofUnits_val_eq (S : Subgroup Mˣ) {x : M} (h : x ∈ S.ofUnits) :
    ∃ y ∈ S, y = x := sorry

@[to_additive]
lemma mem_of_mem_val_ofUnits (S : Subgroup Mˣ) {y : Mˣ} (hy : (y : M) ∈ S.ofUnits) : y ∈ S :=
  match hy with
  | ⟨_, hm, he⟩ => (Units.ext he) ▸ hm

@[target, to_additive]
lemma isUnit_of_mem_ofUnits (S : Subgroup Mˣ) {x : M} (hx : x ∈ S.ofUnits) : IsUnit x :=
  sorry
@[to_additive "Given some `x : M` which is a member of the additive submonoid of additive unit
elements corresponding to a subgroup of units, produce a unit of `M` whose coercion is equal to
`x`."]
noncomputable def unit_of_mem_ofUnits (S : Subgroup Mˣ) {x : M} (h : x ∈ S.ofUnits) : Mˣ :=
  (Classical.choose h).copy x (Classical.choose_spec h).2.symm _ rfl

@[target, to_additive]
lemma unit_of_mem_ofUnits_spec_eq_of_val_mem (S : Subgroup Mˣ) {x : Mˣ} (h : (x : M) ∈ S.ofUnits) :
    S.unit_of_mem_ofUnits h = x := sorry

@[to_additive]
lemma unit_of_mem_ofUnits_spec_val_eq_of_mem (S : Subgroup Mˣ) {x : M} (h : x ∈ S.ofUnits) :
    S.unit_of_mem_ofUnits h = x := rfl

@[target, to_additive]
lemma unit_of_mem_ofUnits_spec_mem (S : Subgroup Mˣ) {x : M} {h : x ∈ S.ofUnits} :
    S.unit_of_mem_ofUnits h ∈ S := sorry

@[to_additive]
lemma unit_eq_unit_of_mem_ofUnits (S : Subgroup Mˣ) {x : M} (h₁ : IsUnit x)
    (h₂ : x ∈ S.ofUnits) : h₁.unit = S.unit_of_mem_ofUnits h₂ := Units.ext rfl

@[target, to_additive]
lemma unit_mem_of_mem_ofUnits (S : Subgroup Mˣ) {x : M} {h₁ : IsUnit x}
    (h₂ : x ∈ S.ofUnits) : h₁.unit ∈ S :=
  sorry

@[target, to_additive]
lemma mem_ofUnits_of_isUnit_of_unit_mem (S : Subgroup Mˣ) {x : M} (h₁ : IsUnit x)
    (h₂ : h₁.unit ∈ S) : x ∈ S.ofUnits := sorry

@[target, to_additive]
lemma mem_ofUnits_iff_exists_isUnit (S : Subgroup Mˣ) (x : M) :
    x ∈ S.ofUnits ↔ ∃ h : IsUnit x, h.unit ∈ S :=
  sorry
@[to_additive "The equivalence between the coercion of an additive subgroup `S` of
`Mˣ` to an additive submonoid of `M` and the additive subgroup itself as a type."]
noncomputable def ofUnitsEquivType (S : Subgroup Mˣ) : S.ofUnits ≃* S where
  toFun := fun x => ⟨S.unit_of_mem_ofUnits x.2, S.unit_of_mem_ofUnits_spec_mem⟩
  invFun := fun x => ⟨x.1, ⟨x.1, x.2, rfl⟩⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => Subtype.ext (Units.ext rfl)
  map_mul' := fun _ _ => Subtype.ext (Units.ext rfl)

@[target, to_additive (attr := sorry

@[to_additive]
lemma ofUnits_inf (S T : Subgroup Mˣ) : (S ⊔ T).ofUnits = S.ofUnits ⊔ T.ofUnits :=
ofUnits_units_gc.l_sup

@[target, to_additive]
lemma ofUnits_sSup (s : Set (Subgroup Mˣ)) : (sSup s).ofUnits = ⨆ S ∈ s, S.ofUnits :=
sorry

@[target, to_additive]
lemma ofUnits_iSup {ι : Sort*} {f : ι → Subgroup Mˣ} :
    (iSup f).ofUnits = ⨆ (i : ι), (f i).ofUnits := sorry

@[target, to_additive]
lemma ofUnits_iSup₂ {ι : Sort*} {κ : ι → Sort*} (f : (i : ι) → κ i → Subgroup Mˣ) :
    (⨆ (i : ι), ⨆ (j : κ i), f i j).ofUnits = ⨆ (i : ι), ⨆ (j : κ i), (f i j).ofUnits :=
  sorry

@[target, to_additive]
lemma ofUnits_injective : Function.Injective (ofUnits (M := sorry

@[target, to_additive (attr := sorry

@[target, to_additive (attr := sorry

@[target, to_additive]
lemma ofUnits_right_inverse :
    Function.RightInverse (ofUnits (M := sorry

@[target, to_additive]
lemma ofUnits_strictMono : StrictMono (ofUnits (M := sorry

@[target]
lemma ofUnits_le_ofUnits_iff {S T : Subgroup Mˣ} : S.ofUnits ≤ T.ofUnits ↔ S ≤ T :=
  sorry
@[to_additive "The equivalence between the additive subgroup of additive units of
`S` and the additive submonoid of additive unit elements of `S`."]
noncomputable def ofUnitsTopEquiv : (⊤ : Subgroup Mˣ).ofUnits ≃* Mˣ :=
  (⊤ : Subgroup Mˣ).ofUnitsEquivType.trans topEquiv

variable {G : Type*}  [Group G]

@[target, to_additive]
lemma mem_units_iff_val_mem (H : Subgroup G) (x : Gˣ) : x ∈ H.units ↔ (x : G) ∈ H := by sorry

@[target, to_additive]
lemma mem_ofUnits_iff_toUnits_mem (H : Subgroup Gˣ) (x : G) : x ∈ H.ofUnits ↔ (toUnits x) ∈ H := by sorry

@[target, to_additive (attr := by sorry

@[target, to_additive (attr := by sorry
@[to_additive "The equivalence between the greatest subgroup of additive units
contained within `T` and `T` itself."]
def unitsEquivSelf (H : Subgroup G) : H.units ≃* H :=
  H.unitsEquivUnitsType.trans (toUnits (G := H)).symm

end Subgroup
