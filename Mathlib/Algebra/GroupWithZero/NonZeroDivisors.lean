import VerifiedAgora.tagger
/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Devon Tuma, Oliver Nash
-/
import Mathlib.Algebra.Group.Action.Opposite
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Associated
import Mathlib.Algebra.GroupWithZero.Opposite

/-!
# Non-zero divisors and smul-divisors

In this file we define the submonoid `nonZeroDivisors` and `nonZeroSMulDivisors` of a
`MonoidWithZero`. We also define `nonZeroDivisorsLeft` and `nonZeroDivisorsRight` for
non-commutative monoids.

## Notations

This file declares the notations:
- `M₀⁰` for the submonoid of non-zero-divisors of `M₀`, in the locale `nonZeroDivisors`.
- `M₀⁰[M]` for the submonoid of non-zero smul-divisors of `M₀` with respect to `M`, in the locale
  `nonZeroSMulDivisors`

Use the statement `open scoped nonZeroDivisors nonZeroSMulDivisors` to access this notation in
your own code.

-/

assert_not_exists Ring

open Function

section
variable (M₀ : Type*) [MonoidWithZero M₀] {x : M₀}

/-- The collection of elements of a `MonoidWithZero` that are not left zero divisors form a
`Submonoid`. -/
/-- The collection of elements of a `MonoidWithZero` that are not left zero divisors form a
`Submonoid`. -/
def nonZeroDivisorsLeft : Submonoid M₀ where
  carrier := {x | ∀ y, y * x = 0 → y = 0}
  one_mem' := by sorry


@[target] lemma mem_nonZeroDivisorsLeft_iff : x ∈ nonZeroDivisorsLeft M₀ ↔ ∀ y, y * x = 0 → y = 0 := by sorry


@[target] lemma nmem_nonZeroDivisorsLeft_iff :
    x ∉ nonZeroDivisorsLeft M₀ ↔ {y | y * x = 0 ∧ y ≠ 0}.Nonempty := by
  sorry


/-- The collection of elements of a `MonoidWithZero` that are not right zero divisors form a
`Submonoid`. -/
/-- The collection of elements of a `MonoidWithZero` that are not right zero divisors form a
`Submonoid`. -/
def nonZeroDivisorsRight : Submonoid M₀ where
  carrier := {x | ∀ y, x * y = 0 → y = 0}
  one_mem' := by sorry


@[simp]
lemma mem_nonZeroDivisorsRight_iff : x ∈ nonZeroDivisorsRight M₀ ↔ ∀ y, x * y = 0 → y = 0 := .rfl

@[target] lemma nmem_nonZeroDivisorsRight_iff :
    x ∉ nonZeroDivisorsRight M₀ ↔ {y | x * y = 0 ∧ y ≠ 0}.Nonempty := by
  sorry


@[target] lemma nonZeroDivisorsLeft_eq_right (M₀ : Type*) [CommMonoidWithZero M₀] :
    nonZeroDivisorsLeft M₀ = nonZeroDivisorsRight M₀ := by
  sorry


@[target] lemma coe_nonZeroDivisorsLeft_eq [NoZeroDivisors M₀] [Nontrivial M₀] :
    nonZeroDivisorsLeft M₀ = {x : M₀ | x ≠ 0} := by
  sorry


@[target] lemma coe_nonZeroDivisorsRight_eq [NoZeroDivisors M₀] [Nontrivial M₀] :
    nonZeroDivisorsRight M₀ = {x : M₀ | x ≠ 0} := by
  sorry


end

/-- The submonoid of non-zero-divisors of a `MonoidWithZero` `M₀`. -/
/-- The submonoid of non-zero-divisors of a `MonoidWithZero` `M₀`. -/
def nonZeroDivisors (M₀ : Type*) [MonoidWithZero M₀] : Submonoid M₀ where
  carrier := { x | ∀ z, z * x = 0 → z = 0 }
  one_mem' _ hz := by rwa [mul_one] at hz
  mul_mem' hx₁ hx₂ _ hz := by
    sorry


/-- The notation for the submonoid of non-zero divisors. -/
scoped[nonZeroDivisors] notation:9000 M₀ "⁰" => nonZeroDivisors M₀

/-- Let `M₀` be a monoid with zero and `M` an additive monoid with an `M₀`-action, then the
collection of non-zero smul-divisors forms a submonoid.

These elements are also called `M`-regular. -/
/-- Let `M₀` be a monoid with zero and `M` an additive monoid with an `M₀`-action, then the
collection of non-zero smul-divisors forms a submonoid.

These elements are also called `M`-regular. -/
def nonZeroSMulDivisors (M₀ : Type*) [MonoidWithZero M₀] (M : Type*) [Zero M] [MulAction M₀ M] :
    Submonoid M₀ where
  carrier := by sorry


/-- The notation for the submonoid of non-zero smul-divisors. -/
scoped[nonZeroSMulDivisors] notation:9000 M₀ "⁰[" M "]" => nonZeroSMulDivisors M₀ M

open nonZeroDivisors

section MonoidWithZero
variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

theorem mem_nonZeroDivisors_iff : r ∈ M₀⁰ ↔ ∀ x, x * r = 0 → x = 0 := Iff.rfl

@[target] lemma nmem_nonZeroDivisors_iff : r ∉ M₀⁰ ↔ {s | s * r = 0 ∧ s ≠ 0}.Nonempty := by
  sorry


@[target] theorem mul_right_mem_nonZeroDivisors_eq_zero_iff (hr : r ∈ M₀⁰) : x * r = 0 ↔ x = 0 :=
  ⟨hr _, by sorry


@[target] theorem mul_right_coe_nonZeroDivisors_eq_zero_iff {c : M₀⁰} : x * c = 0 ↔ x = 0 := by sorry


lemma IsUnit.mem_nonZeroDivisors (hx : IsUnit x) : x ∈ M₀⁰ := fun _ ↦ hx.mul_left_eq_zero.mp

section Nontrivial
variable [Nontrivial M₀]

@[target] theorem zero_not_mem_nonZeroDivisors : 0 ∉ M₀⁰ := by sorry


theorem nonZeroDivisors.ne_zero (hx : x ∈ M₀⁰) : x ≠ 0 :=
  ne_of_mem_of_not_mem hx zero_not_mem_nonZeroDivisors

@[simp]
theorem nonZeroDivisors.coe_ne_zero (x : M₀⁰) : (x : M₀) ≠ 0 := nonZeroDivisors.ne_zero x.2

end Nontrivial

section NoZeroDivisors
variable [NoZeroDivisors M₀]

@[target] theorem eq_zero_of_ne_zero_of_mul_right_eq_zero (hx : x ≠ 0) (hxy : y * x = 0) : y = 0 := by sorry


@[target] theorem eq_zero_of_ne_zero_of_mul_left_eq_zero (hx : x ≠ 0) (hxy : x * y = 0) : y = 0 := by sorry


@[target] theorem mem_nonZeroDivisors_of_ne_zero (hx : x ≠ 0) : x ∈ M₀⁰ := by sorry


@[target] lemma mem_nonZeroDivisors_iff_ne_zero [Nontrivial M₀] : x ∈ M₀⁰ ↔ x ≠ 0 := by sorry


@[target] theorem le_nonZeroDivisors_of_noZeroDivisors {S : Submonoid M₀} (hS : (0 : M₀) ∉ S) :
    S ≤ M₀⁰ := by sorry


theorem powers_le_nonZeroDivisors_of_noZeroDivisors (hx : x ≠ 0) : Submonoid.powers x ≤ M₀⁰ :=
  le_nonZeroDivisors_of_noZeroDivisors fun h ↦ hx (h.recOn fun _ ↦ pow_eq_zero)

end NoZeroDivisors

variable [FunLike F M₀ M₀']

@[target] theorem map_ne_zero_of_mem_nonZeroDivisors [Nontrivial M₀] [ZeroHomClass F M₀ M₀'] (g : F)
    (hg : Injective (g : M₀ → M₀')) {x : M₀} (h : x ∈ M₀⁰) : g x ≠ 0 := by sorry


theorem map_mem_nonZeroDivisors [Nontrivial M₀] [NoZeroDivisors M₀'] [ZeroHomClass F M₀ M₀'] (g : F)
    (hg : Injective g) {x : M₀} (h : x ∈ M₀⁰) : g x ∈ M₀'⁰ := fun _ hz ↦
  eq_zero_of_ne_zero_of_mul_right_eq_zero (map_ne_zero_of_mem_nonZeroDivisors g hg h) hz

theorem MulEquivClass.map_nonZeroDivisors {M₀ S F : Type*} [MonoidWithZero M₀] [MonoidWithZero S]
    [EquivLike F M₀ S] [MulEquivClass F M₀ S] (h : F) :
    Submonoid.map h (nonZeroDivisors M₀) = nonZeroDivisors S := by
  let h : M₀ ≃* S := h
  show Submonoid.map h.toMonoidHom _ = _
  ext
  simp_rw [Submonoid.map_equiv_eq_comap_symm, Submonoid.mem_comap, mem_nonZeroDivisors_iff,
    ← h.symm.forall_congr_right, h.symm.coe_toMonoidHom, h.symm.toEquiv_eq_coe, h.symm.coe_toEquiv,
    ← map_mul, map_eq_zero_iff _ h.symm.injective]

@[target] theorem map_le_nonZeroDivisors_of_injective [NoZeroDivisors M₀'] [MonoidWithZeroHomClass F M₀ M₀']
    (f : F) (hf : Injective f) {S : Submonoid M₀} (hS : S ≤ M₀⁰) : S.map f ≤ M₀'⁰ := by
  sorry


@[target] theorem nonZeroDivisors_le_comap_nonZeroDivisors_of_injective [NoZeroDivisors M₀']
    [MonoidWithZeroHomClass F M₀ M₀'] (f : F) (hf : Injective f) : M₀⁰ ≤ M₀'⁰.comap f := by sorry


/-- If an element maps to a non-zero-divisor via injective homomorphism,
then it is a non-zero-divisor. -/
/-- If an element maps to a non-zero-divisor via injective homomorphism,
then it is a non-zero-divisor. -/
@[target] theorem mem_nonZeroDivisors_of_injective [MonoidWithZeroHomClass F M₀ M₀'] {f : F}
    (hf : Injective f) (hx : f x ∈ M₀'⁰) : x ∈ M₀⁰ := by sorry


@[deprecated (since := "2025-02-03")]
alias mem_nonZeroDivisor_of_injective := mem_nonZeroDivisors_of_injective

@[target] theorem comap_nonZeroDivisors_le_of_injective [MonoidWithZeroHomClass F M₀ M₀'] {f : F}
    (hf : Injective f) : M₀'⁰.comap f ≤ M₀⁰ := by sorry


@[deprecated (since := "2025-02-03")]
alias comap_nonZeroDivisor_le_of_injective := comap_nonZeroDivisors_le_of_injective

end MonoidWithZero

section CommMonoidWithZero
variable {M₀ : Type*} [CommMonoidWithZero M₀] {a b r x : M₀}

@[target] lemma mul_left_mem_nonZeroDivisors_eq_zero_iff (hr : r ∈ M₀⁰) : r * x = 0 ↔ x = 0 := by
  sorry


@[target] lemma mul_left_coe_nonZeroDivisors_eq_zero_iff {c : M₀⁰} : (c : M₀) * x = 0 ↔ x = 0 := by sorry


@[target] lemma mul_mem_nonZeroDivisors : a * b ∈ M₀⁰ ↔ a ∈ M₀⁰ ∧ b ∈ M₀⁰ where
  mp h := by
    sorry


end CommMonoidWithZero

section GroupWithZero
variable {G₀ : Type*} [GroupWithZero G₀] {x : G₀}

/-- Canonical isomorphism between the non-zero-divisors and units of a group with zero. -/
@[simps]
noncomputable def nonZeroDivisorsEquivUnits : G₀⁰ ≃* G₀ˣ where
  toFun u := .mk0 _ <| mem_nonZeroDivisors_iff_ne_zero.1 u.2
  invFun u := ⟨u, u.isUnit.mem_nonZeroDivisors⟩
  left_inv u := rfl
  right_inv u := by simp
  map_mul' u v := by simp

lemma isUnit_of_mem_nonZeroDivisors (hx : x ∈ nonZeroDivisors G₀) : IsUnit x :=
  (nonZeroDivisorsEquivUnits ⟨x, hx⟩).isUnit

end GroupWithZero

section nonZeroSMulDivisors

open nonZeroSMulDivisors nonZeroDivisors

variable {M₀ M : Type*} [MonoidWithZero M₀] [Zero M] [MulAction M₀ M] {x : M₀}

@[target] lemma mem_nonZeroSMulDivisors_iff : x ∈ M₀⁰[M] ↔ ∀ (m : M), x • m = 0 → m = 0 := by sorry


variable (M₀)

@[simp]
lemma unop_nonZeroSMulDivisors_mulOpposite_eq_nonZeroDivisors :
    (M₀ᵐᵒᵖ ⁰[M₀]).unop = M₀⁰ := rfl

/-- The non-zero `•`-divisors with `•` as right multiplication correspond with the non-zero
divisors. Note that the `MulOpposite` is needed because we defined `nonZeroDivisors` with
multiplication on the right. -/
/-- The non-zero `•`-divisors with `•` as right multiplication correspond with the non-zero
divisors. Note that the `MulOpposite` is needed because we defined `nonZeroDivisors` with
multiplication on the right. -/
@[target] lemma nonZeroSMulDivisors_mulOpposite_eq_op_nonZeroDivisors :
    M₀ᵐᵒᵖ ⁰[M₀] = M₀⁰.op := by sorry


end nonZeroSMulDivisors

open scoped nonZeroDivisors

variable {M₀}

section MonoidWithZero
variable [MonoidWithZero M₀] {a b : M₀⁰}

/-- The units of the monoid of non-zero divisors of `M₀` are equivalent to the units of `M₀`. -/
/-- The units of the monoid of non-zero divisors of `M₀` are equivalent to the units of `M₀`. -/
@[simps]
def unitsNonZeroDivisorsEquiv : M₀⁰ˣ ≃* M₀ˣ where
  __ := Units.map M₀⁰.subtype
  invFun u := ⟨⟨u, u.isUnit.mem_nonZeroDivisors⟩, ⟨(u⁻¹ : M₀ˣ), u⁻¹.isUnit.mem_nonZeroDivisors⟩,
    by sorry


@[simp, norm_cast] lemma nonZeroDivisors.associated_coe : Associated (a : M₀) b ↔ Associated a b :=
  unitsNonZeroDivisorsEquiv.symm.exists_congr_left.trans <| by simp [Associated]; norm_cast

end MonoidWithZero

section CommMonoidWithZero
variable {M₀ : Type*} [CommMonoidWithZero M₀] {a : M₀}

@[target] theorem mk_mem_nonZeroDivisors_associates : Associates.mk a ∈ (Associates M₀)⁰ ↔ a ∈ M₀⁰ := by
  sorry


/-- The non-zero divisors of associates of a monoid with zero `M₀` are isomorphic to the associates
of the non-zero divisors of `M₀` under the map `⟨⟦a⟧, _⟩ ↦ ⟦⟨a, _⟩⟧`. -/
/-- The non-zero divisors of associates of a monoid with zero `M₀` are isomorphic to the associates
of the non-zero divisors of `M₀` under the map `⟨⟦a⟧, _⟩ ↦ ⟦⟨a, _⟩⟧`. -/
def associatesNonZeroDivisorsEquiv : (Associates M₀)⁰ ≃* Associates M₀⁰ where
  toEquiv := .subtypeQuotientEquivQuotientSubtype _ (s₂ := Associated.setoid _)
    (· ∈ nonZeroDivisors _)
    (by sorry


@[target] lemma associatesNonZeroDivisorsEquiv_mk_mk (a : M₀) (ha) :
    associatesNonZeroDivisorsEquiv ⟨⟦a⟧, ha⟩ = ⟦⟨a, mk_mem_nonZeroDivisors_associates.1 ha⟩⟧ := by sorry


@[target] lemma associatesNonZeroDivisorsEquiv_symm_mk_mk (a : M₀) (ha) :
    associatesNonZeroDivisorsEquiv.symm ⟦⟨a, ha⟩⟧ = ⟨⟦a⟧, mk_mem_nonZeroDivisors_associates.2 ha⟩ := by sorry


end CommMonoidWithZero
