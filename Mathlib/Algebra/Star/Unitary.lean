import VerifiedAgora.tagger
/-
Copyright (c) 2022 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam, Frédéric Dupuis
-/
import Mathlib.Algebra.Group.Submonoid.Operations
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Algebra.Algebra.Spectrum

/-!
# Unitary elements of a star monoid

This file defines `unitary R`, where `R` is a star monoid, as the submonoid made of the elements
that satisfy `star U * U = 1` and `U * star U = 1`, and these form a group.
This includes, for instance, unitary operators on Hilbert spaces.

See also `Matrix.UnitaryGroup` for specializations to `unitary (Matrix n n R)`.

## Tags

unitary
-/


/-- In a *-monoid, `unitary R` is the submonoid consisting of all the elements `U` of
`R` such that `star U * U = 1` and `U * star U = 1`.
-/
def unitary (R : Type*) [Monoid R] [StarMul R] : Submonoid R where
  carrier := { U | star U * U = 1 ∧ U * star U = 1 }
  one_mem' := by simp only [mul_one, and_self_iff, Set.mem_setOf_eq, star_one]
  mul_mem' := @fun U B ⟨hA₁, hA₂⟩ ⟨hB₁, hB₂⟩ => by
    refine ⟨?_, ?_⟩
    · calc
        star (U * B) * (U * B) = star B * star U * U * B := by simp only [mul_assoc, star_mul]
        _ = star B * (star U * U) * B := by rw [← mul_assoc]
        _ = 1 := by rw [hA₁, mul_one, hB₁]
    · calc
        U * B * star (U * B) = U * B * (star B * star U) := by rw [star_mul]
        _ = U * (B * star B) * star U := by simp_rw [← mul_assoc]
        _ = 1 := by rw [hB₂, mul_one, hA₂]

variable {R : Type*}

namespace unitary

section Monoid

variable [Monoid R] [StarMul R]

theorem mem_iff {U : R} : U ∈ unitary R ↔ star U * U = 1 ∧ U * star U = 1 :=
  Iff.rfl

@[target] theorem star_mul_self_of_mem {U : R} (hU : U ∈ unitary R) : star U * U = 1 := by sorry


@[simp]
theorem mul_star_self_of_mem {U : R} (hU : U ∈ unitary R) : U * star U = 1 :=
  hU.2

theorem star_mem {U : R} (hU : U ∈ unitary R) : star U ∈ unitary R :=
  ⟨by rw [star_star, mul_star_self_of_mem hU], by rw [star_star, star_mul_self_of_mem hU]⟩

@[simp]
theorem star_mem_iff {U : R} : star U ∈ unitary R ↔ U ∈ unitary R :=
  ⟨fun h => star_star U ▸ star_mem h, star_mem⟩

instance : Star (unitary R) :=
  ⟨fun U => ⟨star U, star_mem U.prop⟩⟩

@[simp, norm_cast]
theorem coe_star {U : unitary R} : ↑(star U) = (star U : R) :=
  rfl

@[target] theorem coe_star_mul_self (U : unitary R) : (star U : R) * U = 1 := by sorry


@[target] theorem coe_mul_star_self (U : unitary R) : (U : R) * star U = 1 := by sorry


@[target] theorem star_mul_self (U : unitary R) : star U * U = 1 := by sorry


@[target] theorem mul_star_self (U : unitary R) : U * star U = 1 := by sorry


instance : Group (unitary R) :=
  { Submonoid.toMonoid _ with
    inv := star
    inv_mul_cancel := star_mul_self }

instance : InvolutiveStar (unitary R) :=
  ⟨by
    intro x
    ext
    rw [coe_star, coe_star, star_star]⟩

instance : StarMul (unitary R) :=
  ⟨by
    intro x y
    ext
    rw [coe_star, Submonoid.coe_mul, Submonoid.coe_mul, coe_star, coe_star, star_mul]⟩

instance : Inhabited (unitary R) :=
  ⟨1⟩

@[target] theorem star_eq_inv (U : unitary R) : star U = U⁻¹ := by sorry


theorem star_eq_inv' : (star : unitary R → unitary R) = Inv.inv :=
  rfl

/-- The unitary elements embed into the units. -/
/-- The unitary elements embed into the units. -/
@[simps]
def toUnits : unitary R →* Rˣ where
  toFun x := by sorry


@[target] theorem toUnits_injective : Function.Injective (toUnits : unitary R → Rˣ) := by sorry


theorem _root_.IsUnit.mem_unitary_of_star_mul_self  {u : R} (hu : IsUnit u)
    (h_mul : star u * u = 1) : u ∈ unitary R := by
  refine unitary.mem_iff.mpr ⟨h_mul, ?_⟩
  lift u to Rˣ using hu
  exact left_inv_eq_right_inv h_mul u.mul_inv ▸ u.mul_inv

theorem _root_.IsUnit.mem_unitary_of_mul_star_self {u : R} (hu : IsUnit u)
    (h_mul : u * star u = 1) : u ∈ unitary R :=
  star_star u ▸
    (hu.star.mem_unitary_of_star_mul_self ((star_star u).symm ▸ h_mul) |> unitary.star_mem)

instance instIsStarNormal (u : unitary R) : IsStarNormal u where
  star_comm_self := star_mul_self u |>.trans <| (mul_star_self u).symm

instance coe_isStarNormal (u : unitary R) : IsStarNormal (u : R) where
  star_comm_self := congr(Subtype.val $(star_comm_self' u))

lemma _root_.isStarNormal_of_mem_unitary {u : R} (hu : u ∈ unitary R) : IsStarNormal u :=
  coe_isStarNormal ⟨u, hu⟩

end Monoid

section Map

variable {F R S : Type*} [Monoid R] [StarMul R] [Monoid S] [StarMul S]
variable [FunLike F R S] [StarHomClass F R S] [MonoidHomClass F R S] (f : F)

lemma map_mem {r : R} (hr : r ∈ unitary R) : f r ∈ unitary S := by
  rw [unitary.mem_iff] at hr
  simpa [map_star, map_mul] using And.intro congr(f $(hr.1)) congr(f $(hr.2))

/-- The group homomorphism between unitary subgroups of star monoids induced by a star
homomorphism -/
/-- The unique monoid homomorphism `FreeMonoid α →* FreeMonoid β` that sends
each `of x` to `of (f x)`. -/
@[to_additive "The unique additive monoid homomorphism `FreeAddMonoid α →+ FreeAddMonoid β`
that sends each `of x` to `of (f x)`."]
def map (f : α → β) : FreeMonoid α →* FreeMonoid β where
  toFun l := by sorry


@[target] lemma toUnits_comp_map : toUnits.comp (map f) = (Units.map f).comp toUnits := by sorry


end Map

section CommMonoid

variable [CommMonoid R] [StarMul R]

instance : CommGroup (unitary R) :=
  { inferInstanceAs (Group (unitary R)), Submonoid.toCommMonoid _ with }

@[target] theorem mem_iff_star_mul_self {U : R} : U ∈ unitary R ↔ star U * U = 1 := by sorry


theorem mem_iff_self_mul_star {U : R} : U ∈ unitary R ↔ U * star U = 1 :=
  mem_iff.trans <| and_iff_right_of_imp fun h => mul_comm U (star U) ▸ h

end CommMonoid

section GroupWithZero

variable [GroupWithZero R] [StarMul R]

@[target] theorem coe_inv (r : R) : ↑r⁻¹ = ((↑r)⁻¹ : A) := by sorry


@[target] theorem coe_div (r s : R) : ↑(r / s) = (↑r / ↑s : A) := by sorry


@[target] theorem coe_zpow (r : R) (z : ℤ) : ↑(r ^ z) = (r : A) ^ z := by sorry


end GroupWithZero

section Ring

variable [Ring R] [StarRing R]

instance : Neg (unitary R) where
  neg U :=
    ⟨-U, by simp [mem_iff, star_neg, neg_mul_neg]⟩

@[norm_cast]
theorem coe_neg (U : unitary R) : ↑(-U) = (-U : R) :=
  rfl

instance : HasDistribNeg (unitary R) :=
  Subtype.coe_injective.hasDistribNeg _ coe_neg (unitary R).coe_mul

end Ring

section UnitaryConjugate

universe u

variable {R A : Type*} [CommSemiring R] [Ring A] [Algebra R A] [StarMul A]

/-- Unitary conjugation preserves the spectrum, star on left. -/
@[simp]
lemma spectrum.unitary_conjugate {a : A} {u : unitary A} :
    spectrum R (u * a * (star u : A)) = spectrum R a :=
  spectrum.units_conjugate (u := unitary.toUnits u)

/-- Unitary conjugation preserves the spectrum, star on right. -/
@[simp]
lemma spectrum.unitary_conjugate' {a : A} {u : unitary A} :
    spectrum R ((star u : A) * a * u) = spectrum R a := by
  simpa using spectrum.unitary_conjugate (u := star u)

end UnitaryConjugate

end unitary
