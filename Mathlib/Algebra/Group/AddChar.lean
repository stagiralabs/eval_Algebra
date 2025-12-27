import VerifiedAgora.tagger
/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.Algebra.Ring.Regular
import Mathlib.Algebra.Equiv.TransferInstance
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Characters from additive to multiplicative monoids

Let `A` be an additive monoid, and `M` a multiplicative one. An *additive character* of `A` with
values in `M` is simply a map `A → M` which intertwines the addition operation on `A` with the
multiplicative operation on `M`.

We define these objects, using the namespace `AddChar`, and show that if `A` is a commutative group
under addition, then the additive characters are also a group (written multiplicatively). Note that
we do not need `M` to be a group here.

We also include some constructions specific to the case when `A = R` is a ring; then we define
`mulShift ψ r`, where `ψ : AddChar R M` and `r : R`, to be the character defined by
`x ↦ ψ (r * x)`.

For more refined results of a number-theoretic nature (primitive characters, Gauss sums, etc)
see `Mathlib.NumberTheory.LegendreSymbol.AddCharacter`.

# Implementation notes

Due to their role as the dual of an additive group, additive characters must themselves be an
additive group. This contrasts to their pointwise operations which make them a multiplicative group.
We simply define both the additive and multiplicative group structures and prove them equal.

For more information on this design decision, see the following zulip thread:
https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Additive.20characters

## Tags

additive character
-/

/-!
### Definitions related to and results on additive characters
-/

open Function Multiplicative
open Finset hiding card
open Fintype (card)

section AddCharDef

-- The domain of our additive characters
variable (A : Type*) [AddMonoid A]

-- The target
variable (M : Type*) [Monoid M]

/-- `AddChar A M` is the type of maps `A → M`, for `A` an additive monoid and `M` a multiplicative
monoid, which intertwine addition in `A` with multiplication in `M`.

We only put the typeclasses needed for the definition, although in practice we are usually
interested in much more specific cases (e.g. when `A` is a group and `M` a commutative ring).
-/
structure AddChar where
  /-- The underlying function.

  Do not use this function directly. Instead use the coercion coming from the `FunLike`
  instance. -/
  toFun : A → M
  /-- The function maps `0` to `1`.

  Do not use this directly. Instead use `AddChar.map_zero_eq_one`. -/
  map_zero_eq_one' : toFun 0 = 1
  /-- The function maps addition in `A` to multiplication in `M`.

  Do not use this directly. Instead use `AddChar.map_add_eq_mul`. -/
  map_add_eq_mul' : ∀ a b : A, toFun (a + b) = toFun a * toFun b

end AddCharDef

namespace AddChar

section Basic
-- results which don't require commutativity or inverses

variable {A B M N : Type*} [AddMonoid A] [AddMonoid B] [Monoid M] [Monoid N] {ψ : AddChar A M}

/-- Define coercion to a function. -/
instance instFunLike : FunLike (AddChar A M) A M where
  coe := AddChar.toFun
  coe_injective' φ ψ h := by cases φ; cases ψ; congr

@[target] theorem Algebra.ext {S : Type u} {A : Type v} [CommSemiring S] [Semiring A] (h1 h2 : Algebra S A)
    (h : ∀ (r : S) (x : A), (by sorry


@[target] theorem coe_mk (f : A → B) (h₁ h₂ h₃ h₄) : ⇑(⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩ : A →ₛₙₐ[φ] B) = f := by sorry


/-- An additive character maps `0` to `1`. -/
/-- An additive character maps `0` to `1`. -/
@[target] lemma map_zero_eq_one (ψ : AddChar A M) : ψ 0 = 1 := by sorry


/-- An additive character maps sums to products. -/
/-- An additive character maps sums to products. -/
@[target] lemma map_add_eq_mul (ψ : AddChar A M) (x y : A) : ψ (x + y) = ψ x * ψ y := by sorry


/-- Interpret an additive character as a monoid homomorphism. -/
/-- Reinterpret a ring equivalence as a monoid homomorphism. -/
abbrev toMonoidHom (e : R ≃+* S) : R →* S := by sorry


@[target] lemma toMonoidHom_apply (ψ : AddChar A M) (a : Multiplicative A) :
  ψ.toMonoidHom a = ψ a.toAdd := by sorry


/-- An additive character maps multiples by natural numbers to powers. -/
/-- An additive character maps multiples by natural numbers to powers. -/
@[target] lemma map_nsmul_eq_pow (ψ : AddChar A M) (n : ℕ) (x : A) : ψ (n • x) = ψ x ^ n := by sorry


/-- Additive characters `A → M` are the same thing as monoid homomorphisms from `Multiplicative A`
to `M`. -/
/-- Additive characters `A → M` are the same thing as monoid homomorphisms from `Multiplicative A`
to `M`. -/
def toMonoidHomEquiv : AddChar A M ≃ (Multiplicative A →* M) where
  toFun φ := by sorry


@[target] lemma coe_toMonoidHomEquiv (ψ : AddChar A M) :
    ⇑(toMonoidHomEquiv ψ) = ψ ∘ Multiplicative.toAdd := by sorry


@[target] lemma coe_toMonoidHomEquiv_symm (ψ : Multiplicative A →* M) :
    ⇑(toMonoidHomEquiv.symm ψ) = ψ ∘ Multiplicative.ofAdd := by sorry


@[target] lemma toMonoidHomEquiv_apply (ψ : AddChar A M) (a : Multiplicative A) :
    toMonoidHomEquiv ψ a = ψ a.toAdd := by sorry


@[target] lemma toMonoidHomEquiv_symm_apply (ψ : Multiplicative A →* M) (a : A) :
    toMonoidHomEquiv.symm ψ a = ψ (Multiplicative.ofAdd a) := by sorry


/-- Interpret an additive character as a monoid homomorphism. -/
def toAddMonoidHom (φ : AddChar A M) : A →+ Additive M where
  toFun := φ.toFun
  map_zero' := φ.map_zero_eq_one'
  map_add' := φ.map_add_eq_mul'

@[target] theorem coe_toAddMonoidHom (f : A →ₐ[R] B) : ⇑(f : A →+ B) = f := by sorry


@[target] lemma toAddMonoidHom_apply (ψ : AddChar A M) (a : A) :
    ψ.toAddMonoidHom a = Additive.ofMul (ψ a) := by sorry


/-- Additive characters `A → M` are the same thing as additive homomorphisms from `A` to
`Additive M`. -/
/-- Additive characters `A → M` are the same thing as additive homomorphisms from `A` to
`Additive M`. -/
def toAddMonoidHomEquiv : AddChar A M ≃ (A →+ Additive M) where
  toFun φ := by sorry


@[target] lemma coe_toAddMonoidHomEquiv (ψ : AddChar A M) :
    ⇑(toAddMonoidHomEquiv ψ) = Additive.ofMul ∘ ψ := by sorry


@[target] lemma coe_toAddMonoidHomEquiv_symm (ψ : A →+ Additive M) :
    ⇑(toAddMonoidHomEquiv.symm ψ) = Additive.toMul ∘ ψ := by sorry


@[simp] lemma toAddMonoidHomEquiv_apply (ψ : AddChar A M) (a : A) :
    toAddMonoidHomEquiv ψ a = Additive.ofMul (ψ a) := rfl

@[target] lemma toAddMonoidHomEquiv_symm_apply (ψ : A →+ Additive M) (a : A) :
    toAddMonoidHomEquiv.symm ψ a = (ψ a).toMul  := by sorry


/-- The trivial additive character (sending everything to `1`). -/
instance instOne : One (AddChar A M) := toMonoidHomEquiv.one

/-- The trivial additive character (sending everything to `1`). -/
instance instZero : Zero (AddChar A M) := ⟨1⟩

@[target] theorem coe_one : (↑(1 : R) : A) = 1 := by sorry

@[target] theorem coe_zero : (↑(0 : R) : A) = 0 := by sorry

@[target] theorem one_apply (a : A) : (1 : A →ₙₐ[R] A) a = a := by sorry

@[simp] lemma zero_apply (a : A) : (0 : AddChar A M) a = 1 := rfl

@[target] lemma one_eq_zero : (1 : AddChar A M) = (0 : AddChar A M) := by sorry


@[simp, norm_cast] lemma coe_eq_one : ⇑ψ = 1 ↔ ψ = 0 := by rw [← coe_zero, DFunLike.coe_fn_eq]

@[target] lemma toMonoidHomEquiv_zero : toMonoidHomEquiv (0 : AddChar A M) = 1 := by sorry

@[target] lemma toMonoidHomEquiv_symm_one :
    toMonoidHomEquiv.symm (1 : Multiplicative A →* M) = 0 := by sorry


@[target] lemma toAddMonoidHomEquiv_zero : toAddMonoidHomEquiv (0 : AddChar A M) = 0 := by sorry

@[target] lemma toAddMonoidHomEquiv_symm_zero :
    toAddMonoidHomEquiv.symm (0 : A →+ Additive M) = 0 := by sorry


instance instInhabited : Inhabited (AddChar A M) := ⟨1⟩

/-- Composing a `MonoidHom` with an `AddChar` yields another `AddChar`. -/
def _root_.MonoidHom.compAddChar {N : Type*} [Monoid N] (f : M →* N) (φ : AddChar A M) :
    AddChar A N := toMonoidHomEquiv.symm (f.comp φ.toMonoidHom)

@[simp, norm_cast]
lemma _root_.MonoidHom.coe_compAddChar {N : Type*} [Monoid N] (f : M →* N) (φ : AddChar A M) :
    f.compAddChar φ = f ∘ φ :=
  rfl

@[simp, norm_cast]
lemma _root_.MonoidHom.compAddChar_apply (f : M →* N) (φ : AddChar A M) : f.compAddChar φ = f ∘ φ :=
  rfl

lemma _root_.MonoidHom.compAddChar_injective_left (ψ : AddChar A M) (hψ : Surjective ψ) :
    Injective fun f : M →* N ↦ f.compAddChar ψ := by
  rintro f g h; rw [DFunLike.ext'_iff] at h ⊢; exact hψ.injective_comp_right h

lemma _root_.MonoidHom.compAddChar_injective_right (f : M →* N) (hf : Injective f) :
    Injective fun ψ : AddChar B M ↦ f.compAddChar ψ := by
  rintro ψ χ h; rw [DFunLike.ext'_iff] at h ⊢; exact hf.comp_left h

/-- Composing an `AddChar` with an `AddMonoidHom` yields another `AddChar`. -/
/-- Composing an `AddChar` with an `AddMonoidHom` yields another `AddChar`. -/
def compAddMonoidHom (φ : AddChar B M) (f : A →+ B) : AddChar A M := by sorry


@[simp, norm_cast]
lemma coe_compAddMonoidHom (φ : AddChar B M) (f : A →+ B) : φ.compAddMonoidHom f = φ ∘ f := rfl

@[simp] lemma compAddMonoidHom_apply (ψ : AddChar B M) (f : A →+ B)
    (a : A) : ψ.compAddMonoidHom f a = ψ (f a) := rfl

@[target] lemma compAddMonoidHom_injective_left (f : A →+ B) (hf : Surjective f) :
    Injective fun ψ : AddChar B M ↦ ψ.compAddMonoidHom f := by
  sorry


@[target] lemma compAddMonoidHom_injective_right (ψ : AddChar B M) (hψ : Injective ψ) :
    Injective fun f : A →+ B ↦ ψ.compAddMonoidHom f := by
  sorry


@[target] lemma eq_one_iff : ψ = 1 ↔ ∀ x, ψ x = 1 := by sorry

@[target] theorem Associated.eq_zero_iff [MonoidWithZero M] {a b : M} (h : a ~ᵤ b) : a = 0 ↔ b = 0 := by
  sorry

@[target] lemma ne_one_iff : ψ ≠ 1 ↔ ∃ x, ψ x ≠ 1 := by sorry

@[target] theorem Associated.ne_zero_iff [MonoidWithZero M] {a b : M} (h : a ~ᵤ b) : a ≠ 0 ↔ b ≠ 0 := by sorry


noncomputable instance : DecidableEq (AddChar A M) := Classical.decEq _

end Basic

section toCommMonoid

variable {ι A M : Type*} [AddMonoid A] [CommMonoid M]

/-- When `M` is commutative, `AddChar A M` is a commutative monoid. -/
instance instCommMonoid : CommMonoid (AddChar A M) := toMonoidHomEquiv.commMonoid
/-- When `M` is commutative, `AddChar A M` is an additive commutative monoid. -/
instance instAddCommMonoid : AddCommMonoid (AddChar A M) := Additive.addCommMonoid

@[simp, norm_cast] lemma coe_mul (ψ χ : AddChar A M) : ⇑(ψ * χ) = ψ * χ := rfl
@[target] theorem coe_add (a b : R) : (↑(a + b : R) : A) = ↑a + ↑b := by sorry

@[target] theorem coe_pow (a : R) (n : ℕ) : (↑(a ^ n : R) : A) = (a : A) ^ n := by sorry

@[target] lemma coe_nsmul (n : ℕ) (ψ : AddChar A M) : ⇑(n • ψ) = ψ ^ n := by sorry


@[target] theorem coe_prod (f : A →ₐ[R] B) (g : A →ₐ[R] C) : ⇑(f.prod g) = Pi.prod f g := by sorry


@[target] theorem coe_sum (a : ι → R) : ↑(∑ i ∈ s, a i) = ∑ i ∈ s, (↑(a i) : A) := by sorry


@[target] theorem mul_apply (φ ψ : A →ₐ[R] A) (x : A) : (φ * ψ) x = φ (ψ x) := by sorry

@[target] theorem add_apply (f g : CentroidHom α) (a : α) : (f + g) a = f a + g a := by sorry

@[target] lemma pow_apply (ψ : AddChar A M) (n : ℕ) (a : A) : (ψ ^ n) a = (ψ a) ^ n := by sorry

@[target] lemma nsmul_apply (ψ : AddChar A M) (n : ℕ) (a : A) : (n • ψ) a = (ψ a) ^ n := by sorry


/-- The `Pi.prod` of two morphisms is a morphism. -/
@[simps!]
def prod (f : A →ₐ[R] B) (g : A →ₐ[R] C) : A →ₐ[R] B × C :=
  { f.toRingHom.prod g.toRingHom with
    commutes' := fun r => by
      sorry


lemma sum_apply (s : Finset ι) (ψ : ι → AddChar A M) (a : A) :
    (∑ i ∈ s, ψ i) a = ∏ i ∈ s, ψ i a := by rw [coe_sum, Finset.prod_apply]

@[target] lemma mul_eq_add (ψ χ : AddChar A M) : ψ * χ = ψ + χ := by sorry

@[target] lemma pow_eq_nsmul (ψ : AddChar A M) (n : ℕ) : ψ ^ n = n • ψ := by sorry

@[target] lemma prod_eq_sum (s : Finset ι) (ψ : ι → AddChar A M) : ∏ i ∈ s, ψ i = ∑ i ∈ s, ψ i := by sorry


@[simp] lemma toMonoidHomEquiv_add (ψ φ : AddChar A M) :
    toMonoidHomEquiv (ψ + φ) = toMonoidHomEquiv ψ * toMonoidHomEquiv φ := rfl
@[target] lemma toMonoidHomEquiv_symm_mul (ψ φ : Multiplicative A →* M) :
    toMonoidHomEquiv.symm (ψ * φ) = toMonoidHomEquiv.symm ψ + toMonoidHomEquiv.symm φ := by sorry


/-- The natural equivalence to `(Multiplicative A →* M)` is a monoid isomorphism. -/
/-- The natural equivalence to `(Multiplicative A →* M)` is a monoid isomorphism. -/
def toMonoidHomMulEquiv : AddChar A M ≃* (Multiplicative A →* M) :=
  { toMonoidHomEquiv with map_mul' := fun φ ψ ↦ by sorry


/-- Additive characters `A → M` are the same thing as additive homomorphisms from `A` to
`Additive M`. -/
def toAddMonoidAddEquiv : Additive (AddChar A M) ≃+ (A →+ Additive M) :=
  { toAddMonoidHomEquiv with map_add' := fun φ ψ ↦ by rfl }

/-- The double dual embedding. -/
/-- The double dual embedding. -/
def doubleDualEmb : A →+ AddChar (AddChar A M) M where
  toFun a := { toFun := fun ψ ↦ ψ a
               map_zero_eq_one' := by sorry


@[target] lemma doubleDualEmb_apply (a : A) (ψ : AddChar A M) : doubleDualEmb a ψ = ψ a := by sorry


end toCommMonoid

section CommSemiring
variable {A R : Type*} [AddGroup A] [Fintype A] [CommSemiring R] [IsDomain R]
  {ψ : AddChar A R}

@[target] lemma sum_eq_ite (ψ : AddChar A R) [Decidable (ψ = 0)] :
    ∑ a, ψ a = if ψ = 0 then ↑(card A) else 0 := by
  sorry


variable [CharZero R]

@[target] lemma sum_eq_zero_iff_ne_zero : ∑ x, ψ x = 0 ↔ ψ ≠ 0 := by
  sorry

  classical
  rw [sum_eq_ite, Ne.ite_eq_right_iff]; exact Nat.cast_ne_zero.2 Fintype.card_ne_zero

@[target] lemma sum_ne_zero_iff_eq_zero : ∑ x, ψ x ≠ 0 ↔ ψ = 0 := by sorry


end CommSemiring

/-!
## Additive characters of additive abelian groups
-/
section fromAddCommGroup

variable {A M : Type*} [AddCommGroup A] [CommMonoid M]

/-- The additive characters on a commutative additive group form a commutative group.

Note that the inverse is defined using negation on the domain; we do not assume `M` has an
inversion operation for the definition (but see `AddChar.map_neg_eq_inv` below). -/
instance instCommGroup : CommGroup (AddChar A M) :=
  { instCommMonoid with
    inv := fun ψ ↦ ψ.compAddMonoidHom negAddMonoidHom
    inv_mul_cancel := fun ψ ↦ by ext1 x; simp [negAddMonoidHom, ← map_add_eq_mul]}

/-- The additive characters on a commutative additive group form a commutative group. -/
instance : AddCommGroup (AddChar A M) := Additive.addCommGroup

@[target] lemma inv_apply (ψ : AddChar A M) (a : A) : ψ⁻¹ a = ψ (-a) := by sorry

@[target] theorem neg_apply (f : CentroidHom α) (a : α) : (-f) a = -f a := by sorry

@[target] lemma div_apply (ψ χ : AddChar A M) (a : A) : (ψ / χ) a = ψ a * χ (-a) := by sorry

@[target] theorem sub_apply (f g : CentroidHom α) (a : α) : (f - g) a = f a - g a := by sorry


end fromAddCommGroup

section fromAddGrouptoCommMonoid

/-- The values of an additive character on an additive group are units. -/
/-- The values of an additive character on an additive group are units. -/
@[target] lemma val_isUnit {A M} [AddGroup A] [Monoid M] (φ : AddChar A M) (a : A) : IsUnit (φ a) := by sorry


end fromAddGrouptoCommMonoid

section fromAddGrouptoDivisionMonoid

variable {A M : Type*} [AddGroup A] [DivisionMonoid M]

/-- An additive character maps negatives to inverses (when defined) -/
/-- An additive character maps negatives to inverses (when defined) -/
@[target] lemma map_neg_eq_inv (ψ : AddChar A M) (a : A) : ψ (-a) = (ψ a)⁻¹ := by
  sorry


/-- An additive character maps integer scalar multiples to integer powers. -/
/-- An additive character maps integer scalar multiples to integer powers. -/
@[target] lemma map_zsmul_eq_zpow (ψ : AddChar A M) (n : ℤ) (a : A) : ψ (n • a) = (ψ a) ^ n := by sorry


end fromAddGrouptoDivisionMonoid

section fromAddCommGrouptoDivisionCommMonoid
variable {A M : Type*} [AddCommGroup A] [DivisionCommMonoid M]

lemma inv_apply' (ψ : AddChar A M) (a : A) : ψ⁻¹ a = (ψ a)⁻¹ := by rw [inv_apply, map_neg_eq_inv]
lemma neg_apply' (ψ : AddChar A M) (a : A) : (-ψ) a = (ψ a)⁻¹ := map_neg_eq_inv _ _

lemma div_apply' (ψ χ : AddChar A M) (a : A) : (ψ / χ) a = ψ a / χ a := by
  rw [div_apply, map_neg_eq_inv, div_eq_mul_inv]

lemma sub_apply' (ψ χ : AddChar A M) (a : A) : (ψ - χ) a = ψ a / χ a := by
  rw [sub_apply, map_neg_eq_inv, div_eq_mul_inv]

@[target] lemma zsmul_apply (n : ℤ) (ψ : AddChar A M) (a : A) : (n • ψ) a = ψ a ^ n := by
  sorry


@[target] lemma zpow_apply (ψ : AddChar A M) (n : ℤ) (a : A) : (ψ ^ n) a = ψ a ^ n := by sorry


@[target] lemma map_sub_eq_div (ψ : AddChar A M) (a b : A) : ψ (a - b) = ψ a / ψ b := by sorry


@[target] lemma injective_iff {ψ : AddChar A M} : Injective ψ ↔ ∀ ⦃x⦄, ψ x = 1 → x = 0 := by sorry


end fromAddCommGrouptoDivisionCommMonoid

section MonoidWithZero
variable {A M₀ : Type*} [AddGroup A] [MonoidWithZero M₀] [Nontrivial M₀]

@[target] theorem nonZeroDivisors.coe_ne_zero (x : M₀⁰) : (x : M₀) ≠ 0 := by sorry


end MonoidWithZero

/-!
## Additive characters of rings
-/
section Ring

-- The domain and target of our additive characters. Now we restrict to a ring in the domain.
variable {R M : Type*} [Ring R] [CommMonoid M]

/-- Define the multiplicative shift of an additive character.
This satisfies `mulShift ψ a x = ψ (a * x)`. -/
/-- Define the multiplicative shift of an additive character.
This satisfies `mulShift ψ a x = ψ (a * x)`. -/
def mulShift (ψ : AddChar R M) (r : R) : AddChar R M := by sorry


@[simp] lemma mulShift_apply {ψ : AddChar R M} {r : R} {x : R} : mulShift ψ r x = ψ (r * x) :=
  rfl

/-- `ψ⁻¹ = mulShift ψ (-1))`. -/
/-- `ψ⁻¹ = mulShift ψ (-1))`. -/
@[target] theorem inv_mulShift (ψ : AddChar R M) : ψ⁻¹ = mulShift ψ (-1) := by
  sorry


/-- If `n` is a natural number, then `mulShift ψ n x = (ψ x) ^ n`. -/
theorem mulShift_spec' (ψ : AddChar R M) (n : ℕ) (x : R) : mulShift ψ n x = ψ x ^ n := by
  rw [mulShift_apply, ← nsmul_eq_mul, map_nsmul_eq_pow]

/-- If `n` is a natural number, then `ψ ^ n = mulShift ψ n`. -/
/-- If `n` is a natural number, then `ψ ^ n = mulShift ψ n`. -/
@[target] theorem pow_mulShift (ψ : AddChar R M) (n : ℕ) : ψ ^ n = mulShift ψ n := by
  sorry


/-- The product of `mulShift ψ r` and `mulShift ψ s` is `mulShift ψ (r + s)`. -/
theorem mulShift_mul (ψ : AddChar R M) (r s : R) :
    mulShift ψ r * mulShift ψ s = mulShift ψ (r + s) := by
  ext
  rw [mulShift_apply, right_distrib, map_add_eq_mul]; norm_cast

@[target] lemma mulShift_mulShift (ψ : AddChar R M) (r s : R) :
    mulShift (mulShift ψ r) s = mulShift ψ (r * s) := by
  sorry


/-- `mulShift ψ 0` is the trivial character. -/
/-- `mulShift ψ 0` is the trivial character. -/
@[target] theorem mulShift_zero (ψ : AddChar R M) : mulShift ψ 0 = 1 := by
  sorry


@[simp]
lemma mulShift_one (ψ : AddChar R M) : mulShift ψ 1 = ψ := by
  ext; rw [mulShift_apply, one_mul]

lemma mulShift_unit_eq_one_iff (ψ : AddChar R M) {u : R} (hu : IsUnit u) :
    ψ.mulShift u = 1 ↔ ψ = 1 := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · ext1 y
    rw [show y = u * (hu.unit⁻¹ * y) by rw [← mul_assoc, IsUnit.mul_val_inv, one_mul]]
    simpa only [mulShift_apply] using DFunLike.ext_iff.mp h (hu.unit⁻¹ * y)
  · rintro rfl
    ext1 y
    rw [mulShift_apply, one_apply, one_apply]

end Ring

end AddChar
