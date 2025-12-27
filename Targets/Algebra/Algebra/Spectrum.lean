import VerifiedAgora.tagger
/-
Copyright (c) 2021 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Star.Pointwise
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Nonunits
import Mathlib.Tactic.NoncommRing

/-!
# Spectrum of an element in an algebra
This file develops the basic theory of the spectrum of an element of an algebra.
This theory will serve as the foundation for spectral theory in Banach algebras.

## Main definitions

* `resolventSet a : Set R`: the resolvent set of an element `a : A` where
  `A` is an `R`-algebra.
* `spectrum a : Set R`: the spectrum of an element `a : A` where
  `A` is an `R`-algebra.
* `resolvent : R → A`: the resolvent function is `fun r ↦ Ring.inverse (↑ₐr - a)`, and hence
  when `r ∈ resolvent R A`, it is actually the inverse of the unit `(↑ₐr - a)`.

## Main statements

* `spectrum.unit_smul_eq_smul` and `spectrum.smul_eq_smul`: units in the scalar ring commute
  (multiplication) with the spectrum, and over a field even `0` commutes with the spectrum.
* `spectrum.left_add_coset_eq`: elements of the scalar ring commute (addition) with the spectrum.
* `spectrum.unit_mem_mul_comm` and `spectrum.preimage_units_mul_comm`: the
  units (of `R`) in `σ (a*b)` coincide with those in `σ (b*a)`.
* `spectrum.scalar_eq`: in a nontrivial algebra over a field, the spectrum of a scalar is
  a singleton.

## Notations

* `σ a` : `spectrum R a` of `a : A`
-/


open Set

open scoped Pointwise

universe u v

section Defs

variable (R : Type u) {A : Type v}
variable [CommSemiring R] [Ring A] [Algebra R A]

local notation "↑ₐ" => algebraMap R A

-- definition and basic properties
/-- Given a commutative ring `R` and an `R`-algebra `A`, the *resolvent set* of `a : A`
is the `Set R` consisting of those `r : R` for which `r•1 - a` is a unit of the
algebra `A`. -/
def resolventSet (a : A) : Set R :=
  {r : R | IsUnit (↑ₐ r - a)}

/-- Given a commutative ring `R` and an `R`-algebra `A`, the *spectrum* of `a : A`
is the `Set R` consisting of those `r : R` for which `r•1 - a` is not a unit of the
algebra `A`.

The spectrum is simply the complement of the resolvent set. -/
def spectrum (a : A) : Set R :=
  (resolventSet R a)ᶜ

variable {R}

/-- Given an `a : A` where `A` is an `R`-algebra, the *resolvent* is
    a map `R → A` which sends `r : R` to `(algebraMap R A r - a)⁻¹` when
    `r ∈ resolvent R A` and `0` when `r ∈ spectrum R A`. -/
noncomputable def resolvent (a : A) (r : R) : A :=
  Ring.inverse (↑ₐ r - a)

/-- The unit `1 - r⁻¹ • a` constructed from `r • 1 - a` when the latter is a unit. -/
@[simps]
noncomputable def IsUnit.subInvSMul {r : Rˣ} {s : R} {a : A} (h : IsUnit <| r • ↑ₐ s - a) : Aˣ where
  val := ↑ₐ s - r⁻¹ • a
  inv := r • ↑h.unit⁻¹
  val_inv := by rw [mul_smul_comm, ← smul_mul_assoc, smul_sub, smul_inv_smul, h.mul_val_inv]
  inv_val := by rw [smul_mul_assoc, ← mul_smul_comm, smul_sub, smul_inv_smul, h.val_inv_mul]

end Defs

namespace spectrum

section ScalarSemiring

variable {R : Type u} {A : Type v}
variable [CommSemiring R] [Ring A] [Algebra R A]

local notation "σ" => spectrum R

local notation "↑ₐ" => algebraMap R A

@[target]
theorem mem_iff {r : R} {a : A} : r ∈ σ a ↔ ¬IsUnit (↑ₐ r - a) :=
  sorry

@[target]
theorem not_mem_iff {r : R} {a : A} : r ∉ σ a ↔ IsUnit (↑ₐ r - a) := by sorry

variable (R)

@[target]
theorem zero_mem_iff {a : A} : (0 : R) ∈ σ a ↔ ¬IsUnit a := by sorry

theorem zero_not_mem_iff {a : A} : (0 : R) ∉ σ a ↔ IsUnit a := by
  rw [zero_mem_iff, Classical.not_not]

alias ⟨isUnit_of_zero_not_mem, zero_not_mem⟩ := spectrum.zero_not_mem_iff

@[target, simp]
lemma _root_.Units.zero_not_mem_spectrum (a : Aˣ) : 0 ∉ spectrum R (a : A) :=
  sorry

@[target]
lemma subset_singleton_zero_compl {a : A} (ha : IsUnit a) : spectrum R a ⊆ {0}ᶜ :=
  sorry

variable {R}

@[target]
theorem mem_resolventSet_of_left_right_inverse {r : R} {a b c : A} (h₁ : (↑ₐ r - a) * b = 1)
    (h₂ : c * (↑ₐ r - a) = 1) : r ∈ resolventSet R a :=
  sorry

theorem mem_resolventSet_iff {r : R} {a : A} : r ∈ resolventSet R a ↔ IsUnit (↑ₐ r - a) :=
  Iff.rfl

@[target, simp]
theorem algebraMap_mem_iff (S : Type*) {R A : Type*} [CommSemiring R] [CommSemiring S]
    [Ring A] [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A] {a : A} {r : R} :
    algebraMap R S r ∈ spectrum S a ↔ r ∈ spectrum R a := by sorry

@[simp]
theorem preimage_algebraMap (S : Type*) {R A : Type*} [CommSemiring R] [CommSemiring S]
    [Ring A] [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A] {a : A} :
    algebraMap R S ⁻¹' spectrum S a = spectrum R a :=
  Set.ext fun _ => spectrum.algebraMap_mem_iff _

@[simp]
theorem resolventSet_of_subsingleton [Subsingleton A] (a : A) : resolventSet R a = Set.univ := by
  simp_rw [resolventSet, Subsingleton.elim (algebraMap R A _ - a) 1, isUnit_one, Set.setOf_true]

@[target, simp]
theorem of_subsingleton [Subsingleton A] (a : A) : spectrum R a = ∅ := by sorry

theorem resolvent_eq {a : A} {r : R} (h : r ∈ resolventSet R a) : resolvent a r = ↑h.unit⁻¹ :=
  Ring.inverse_unit h.unit

@[target]
theorem units_smul_resolvent {r : Rˣ} {s : R} {a : A} :
    r • resolvent a (s : R) = resolvent (r⁻¹ • a) (r⁻¹ • s : R) := by sorry

theorem units_smul_resolvent_self {r : Rˣ} {a : A} :
    r • resolvent a (r : R) = resolvent (r⁻¹ • a) (1 : R) := by
  simpa only [Units.smul_def, Algebra.id.smul_eq_mul, Units.inv_mul] using
    @units_smul_resolvent _ _ _ _ _ r r a

/-- The resolvent is a unit when the argument is in the resolvent set. -/
theorem isUnit_resolvent {r : R} {a : A} : r ∈ resolventSet R a ↔ IsUnit (resolvent a r) :=
  isUnit_ring_inverse.symm

@[target]
theorem inv_mem_resolventSet {r : Rˣ} {a : Aˣ} (h : (r : R) ∈ resolventSet R (a : A)) :
    (↑r⁻¹ : R) ∈ resolventSet R (↑a⁻¹ : A) := by sorry

@[target]
theorem inv_mem_iff {r : Rˣ} {a : Aˣ} : (r : R) ∈ σ (a : A) ↔ (↑r⁻¹ : R) ∈ σ (↑a⁻¹ : A) :=
  sorry

theorem zero_mem_resolventSet_of_unit (a : Aˣ) : 0 ∈ resolventSet R (a : A) := by
  simpa only [mem_resolventSet_iff, ← not_mem_iff, zero_not_mem_iff] using a.isUnit

theorem ne_zero_of_mem_of_unit {a : Aˣ} {r : R} (hr : r ∈ σ (a : A)) : r ≠ 0 := fun hn =>
  (hn ▸ hr) (zero_mem_resolventSet_of_unit a)

@[target]
theorem add_mem_iff {a : A} {r s : R} : r + s ∈ σ a ↔ r ∈ σ (-↑ₐ s + a) := by sorry

@[target]
theorem add_mem_add_iff {a : A} {r s : R} : r + s ∈ σ (↑ₐ s + a) ↔ r ∈ σ a := by sorry

theorem smul_mem_smul_iff {a : A} {s : R} {r : Rˣ} : r • s ∈ σ (r • a) ↔ s ∈ σ a := by
  simp only [mem_iff, not_iff_not, Algebra.algebraMap_eq_smul_one, smul_assoc, ← smul_sub,
    isUnit_smul_iff]

@[target]
theorem unit_smul_eq_smul (a : A) (r : Rˣ) : σ (r • a) = r • σ a := by sorry

-- `r ∈ σ(a*b) ↔ r ∈ σ(b*a)` for any `r : Rˣ`
theorem unit_mem_mul_comm {a b : A} {r : Rˣ} : ↑r ∈ σ (a * b) ↔ ↑r ∈ σ (b * a) := by
  have h₁ : ∀ x y : A, IsUnit (1 - x * y) → IsUnit (1 - y * x) := by
    refine fun x y h => ⟨⟨1 - y * x, 1 + y * h.unit.inv * x, ?_, ?_⟩, rfl⟩
    · calc
        (1 - y * x) * (1 + y * (IsUnit.unit h).inv * x) =
            1 - y * x + y * ((1 - x * y) * h.unit.inv) * x := by noncomm_ring
        _ = 1 := by simp only [Units.inv_eq_val_inv, IsUnit.mul_val_inv, mul_one, sub_add_cancel]
    · calc
        (1 + y * (IsUnit.unit h).inv * x) * (1 - y * x) =
            1 - y * x + y * (h.unit.inv * (1 - x * y)) * x := by noncomm_ring
        _ = 1 := by simp only [Units.inv_eq_val_inv, IsUnit.val_inv_mul, mul_one, sub_add_cancel]
  have := Iff.intro (h₁ (r⁻¹ • a) b) (h₁ b (r⁻¹ • a))
  rw [mul_smul_comm r⁻¹ b a] at this
  simpa only [mem_iff, not_iff_not, Algebra.algebraMap_eq_smul_one, ← Units.smul_def,
    IsUnit.smul_sub_iff_sub_inv_smul, smul_mul_assoc]

@[deprecated (since := "2025-01-29")] alias unit_mem_mul_iff_mem_swap_mul := unit_mem_mul_comm

@[target]
theorem preimage_units_mul_comm (a b : A) :
    ((↑) : Rˣ → R) ⁻¹' σ (a * b) = (↑) ⁻¹' σ (b * a) :=
  sorry

@[deprecated (since := "2025-01-29")]
alias preimage_units_mul_eq_swap_mul := preimage_units_mul_comm

theorem setOf_isUnit_inter_mul_comm (a b : A) :
    {r | IsUnit r} ∩ σ (a * b) = {r | IsUnit r} ∩ σ (b * a) := by
  ext r
  simpa using fun hr : IsUnit r ↦ unit_mem_mul_comm (r := hr.unit)

section Star

variable [InvolutiveStar R] [StarRing A] [StarModule R A]

@[target]
theorem star_mem_resolventSet_iff {r : R} {a : A} :
    star r ∈ resolventSet R a ↔ r ∈ resolventSet R (star a) := by sorry

end Star

end ScalarSemiring

section ScalarRing

variable {R : Type u} {A : Type v}
variable [CommRing R] [Ring A] [Algebra R A]

local notation "σ" => spectrum R

local notation "↑ₐ" => algebraMap R A

@[target]
theorem subset_subalgebra {S R A : Type*} [CommSemiring R] [Ring A] [Algebra R A]
    [SetLike S A] [SubringClass S A] [SMulMemClass S R A] {s : S} (a : s) :
    spectrum R (a : A) ⊆ spectrum R a :=
  sorry

theorem singleton_add_eq (a : A) (r : R) : {r} + σ a = σ (↑ₐ r + a) :=
  ext fun x => by
    rw [singleton_add, image_add_left, mem_preimage, add_comm, add_mem_iff, map_neg, neg_neg]

theorem add_singleton_eq (a : A) (r : R) : σ a + {r} = σ (a + ↑ₐ r) :=
  add_comm {r} (σ a) ▸ add_comm (algebraMap R A r) a ▸ singleton_add_eq a r

theorem vadd_eq (a : A) (r : R) : r +ᵥ σ a = σ (↑ₐ r + a) :=
  singleton_add.symm.trans <| singleton_add_eq a r

theorem neg_eq (a : A) : -σ a = σ (-a) :=
  Set.ext fun x => by
    simp only [mem_neg, mem_iff, map_neg, ← neg_add', IsUnit.neg_iff, sub_neg_eq_add]

@[target]
theorem singleton_sub_eq (a : A) (r : R) : {r} - σ a = σ (↑ₐ r - a) := by sorry

theorem sub_singleton_eq (a : A) (r : R) : σ a - {r} = σ (a - ↑ₐ r) := by
  simpa only [neg_sub, neg_eq] using congr_arg Neg.neg (singleton_sub_eq a r)

end ScalarRing

section ScalarSemifield

variable {R : Type u} {A : Type v} [Semifield R] [Ring A] [Algebra R A]

@[target, simp]
lemma inv₀_mem_iff {r : R} {a : Aˣ} :
    r⁻¹ ∈ spectrum R (a : A) ↔ r ∈ spectrum R (↑a⁻¹ : A) := by sorry

@[target]
lemma inv₀_mem_inv_iff {r : R} {a : Aˣ} :
    r⁻¹ ∈ spectrum R (↑a⁻¹ : A) ↔ r ∈ spectrum R (a : A) := by sorry

end ScalarSemifield

section ScalarField

variable {𝕜 : Type u} {A : Type v}
variable [Field 𝕜] [Ring A] [Algebra 𝕜 A]

local notation "σ" => spectrum 𝕜

local notation "↑ₐ" => algebraMap 𝕜 A

/-- Without the assumption `Nontrivial A`, then `0 : A` would be invertible. -/
@[target, simp]
theorem zero_eq [Nontrivial A] : σ (0 : A) = {0} := by sorry

@[simp]
theorem scalar_eq [Nontrivial A] (k : 𝕜) : σ (↑ₐ k) = {k} := by
  rw [← add_zero (↑ₐ k), ← singleton_add_eq, zero_eq, Set.singleton_add_singleton, add_zero]

@[target, simp]
theorem one_eq [Nontrivial A] : σ (1 : A) = {1} :=
  sorry
@[target]
theorem smul_eq_smul [Nontrivial A] (k : 𝕜) (a : A) (ha : (σ a).Nonempty) :
    σ (k • a) = k • σ a := by sorry

theorem nonzero_mul_comm (a b : A) : σ (a * b) \ {0} = σ (b * a) \ {0} := by
  suffices h : ∀ x y : A, σ (x * y) \ {0} ⊆ σ (y * x) \ {0} from
    Set.eq_of_subset_of_subset (h a b) (h b a)
  rintro _ _ k ⟨k_mem, k_neq⟩
  change ((Units.mk0 k k_neq) : 𝕜) ∈ _ at k_mem
  exact ⟨unit_mem_mul_comm.mp k_mem, k_neq⟩

protected theorem map_inv (a : Aˣ) : (σ (a : A))⁻¹ = σ (↑a⁻¹ : A) := by
  refine Set.eq_of_subset_of_subset (fun k hk => ?_) fun k hk => ?_
  · rw [Set.mem_inv] at hk
    have : k ≠ 0 := by simpa only [inv_inv] using inv_ne_zero (ne_zero_of_mem_of_unit hk)
    lift k to 𝕜ˣ using isUnit_iff_ne_zero.mpr this
    rw [← Units.val_inv_eq_inv_val k] at hk
    exact inv_mem_iff.mp hk
  · lift k to 𝕜ˣ using isUnit_iff_ne_zero.mpr (ne_zero_of_mem_of_unit hk)
    simpa only [Units.val_inv_eq_inv_val] using inv_mem_iff.mp hk

end ScalarField

end spectrum

namespace AlgHom

section CommSemiring

variable {F R A B : Type*} [CommSemiring R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]
variable [FunLike F A B] [AlgHomClass F R A B]

local notation "σ" => spectrum R

local notation "↑ₐ" => algebraMap R A

@[target]
theorem mem_resolventSet_apply (φ : F) {a : A} {r : R} (h : r ∈ resolventSet R a) :
    r ∈ resolventSet R ((φ : A → B) a) := by sorry

@[target]
theorem spectrum_apply_subset (φ : F) (a : A) : σ ((φ : A → B) a) ⊆ σ a := sorry

end CommSemiring

section CommRing

variable {F R A : Type*} [CommRing R] [Ring A] [Algebra R A]
variable [FunLike F A R] [AlgHomClass F R A R]

local notation "σ" => spectrum R

local notation "↑ₐ" => algebraMap R A

theorem apply_mem_spectrum [Nontrivial R] (φ : F) (a : A) : φ a ∈ σ a := by
  have h : ↑ₐ (φ a) - a ∈ RingHom.ker (φ : A →+* R) := by
    simp only [RingHom.mem_ker, map_sub, RingHom.coe_coe, AlgHomClass.commutes,
      Algebra.id.map_eq_id, RingHom.id_apply, sub_self]
  simp only [spectrum.mem_iff, ← mem_nonunits_iff,
    coe_subset_nonunits (RingHom.ker_ne_top (φ : A →+* R)) h]

end CommRing

end AlgHom

@[target, simp]
theorem AlgEquiv.spectrum_eq {F R A B : Type*} [CommSemiring R] [Ring A] [Ring B] [Algebra R A]
    [Algebra R B] [EquivLike F A B] [AlgEquivClass F R A B] (f : F) (a : A) :
    spectrum R (f a) = spectrum R a :=
  sorry

section ConjugateUnits

variable {R A : Type*} [CommSemiring R] [Ring A] [Algebra R A]

/-- Conjugation by a unit preserves the spectrum, inverse on right. -/
@[simp]
lemma spectrum.units_conjugate {a : A} {u : Aˣ} :
    spectrum R (u * a * u⁻¹) = spectrum R a := by
  suffices ∀ (b : A) (v : Aˣ), spectrum R (v * b * v⁻¹) ⊆ spectrum R b by
    refine le_antisymm (this a u) ?_
    apply le_of_eq_of_le ?_ <| this (u * a * u⁻¹) u⁻¹
    simp [mul_assoc]
  intro a u μ hμ
  rw [spectrum.mem_iff] at hμ ⊢
  contrapose! hμ
  simpa [mul_sub, sub_mul, Algebra.right_comm] using u.isUnit.mul hμ |>.mul u⁻¹.isUnit

/-- Conjugation by a unit preserves the spectrum, inverse on left. -/
@[target, simp]
lemma spectrum.units_conjugate' {a : A} {u : Aˣ} :
    spectrum R (u⁻¹ * a * u) = spectrum R a := by sorry

end ConjugateUnits
