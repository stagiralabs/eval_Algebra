import VerifiedAgora.tagger
/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
import Mathlib.Algebra.Algebra.NonUnitalHom
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Facts about algebras involving bilinear maps and tensor products

We move a few basic statements about algebras out of `Algebra.Algebra.Basic`,
in order to avoid importing `LinearAlgebra.BilinearMap` and
`LinearAlgebra.TensorProduct` unnecessarily.
-/

open TensorProduct Module

namespace LinearMap

section NonUnitalNonAssoc
variable (R A : Type*)

section one_side
variable [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]

section left
variable {A} [SMulCommClass R A A]

/-- The multiplication on the left in a algebra is a linear map.

Note that this only assumes `SMulCommClass R A A`, so that it also works for `R := Aᵐᵒᵖ`.

When `A` is unital and associative, this is the same as `DistribMulAction.toLinearMap R A a` -/
def mulLeft (a : A) : A →ₗ[R] A where
  toFun := (a * ·)
  map_add' := mul_add _
  map_smul' _ := mul_smul_comm _ _

@[target] theorem mulLeft_apply (a b : A) : mulLeft R a b = a * b := by sorry


@[target] theorem mulLeft_toAddMonoidHom (a : A) : (mulLeft R a : A →+ A) = AddMonoidHom.mulLeft a := by sorry


variable (A) in
variable (A) in
@[target] theorem mulLeft_zero_eq_zero : mulLeft R (0 : A) = 0 := by sorry


end left

section right
variable {A} [IsScalarTower R A A]

/-- The multiplication on the right in an algebra is a linear map.

Note that this only assumes `IsScalarTower R A A`, so that it also works for `R := A`.

When `A` is unital and associative, this is the same as
`DistribMulAction.toLinearMap R A (MulOpposite.op b)`. -/
/-- The multiplication on the right in an algebra is a linear map.

Note that this only assumes `IsScalarTower R A A`, so that it also works for `R := by sorry


@[target] theorem mulRight_apply (a b : A) : mulRight R a b = b * a := by sorry


@[simp]
theorem mulRight_toAddMonoidHom (a : A) : (mulRight R a : A →+ A) = AddMonoidHom.mulRight a := rfl

variable (A) in
variable (A) in
@[target] theorem mulRight_zero_eq_zero : mulRight R (0 : A) = 0 := by sorry


end right

end one_side

variable [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]
variable [SMulCommClass R A A] [IsScalarTower R A A]

/-- The multiplication in a non-unital non-associative algebra is a bilinear map.

A weaker version of this for semirings exists as `AddMonoidHom.mul`. -/
/-- The multiplication in a non-unital non-associative algebra is a bilinear map.

A weaker version of this for semirings exists as `AddMonoidHom.mul`. -/
@[simps!]
def mul : A →ₗ[R] A →ₗ[R] A := by sorry


/-- The multiplication map on a non-unital algebra, as an `R`-linear map from `A ⊗[R] A` to `A`. -/
-- TODO: upgrade to A-linear map if A is a semiring.
noncomputable def mul' : A ⊗[R] A →ₗ[R] A :=
  TensorProduct.lift (mul R A)

variable {A}

/-- Simultaneous multiplication on the left and right is a linear map. -/
/-- Simultaneous multiplication on the left and right is a linear map. -/
def mulLeftRight (ab : A × A) : A →ₗ[R] A := by sorry


variable {R}

@[target] theorem mul_apply (φ ψ : A →ₐ[R] A) (x : A) : (φ * ψ) x = φ (ψ x) := by sorry


@[target] theorem mulLeftRight_apply (a b x : A) : mulLeftRight R (a, b) x = a * x * b := by sorry


@[simp]
theorem mul'_apply {a b : A} : mul' R A (a ⊗ₜ b) = a * b :=
  rfl

end NonUnitalNonAssoc

section NonUnital
variable (R A B : Type*)

section one_side
variable [Semiring R] [NonUnitalSemiring A] [NonUnitalSemiring B] [Module R B] [Module R A]

@[target] theorem mulLeft_mul [SMulCommClass R A A] (a b : A) :
    mulLeft R (a * b) = (mulLeft R a).comp (mulLeft R b) := by
  sorry


@[target] theorem mulRight_mul [IsScalarTower R A A] (a b : A) :
    mulRight R (a * b) = (mulRight R b).comp (mulRight R a) := by
  sorry


end one_side

variable [CommSemiring R] [NonUnitalSemiring A] [NonUnitalSemiring B] [Module R B] [Module R A]
variable [SMulCommClass R A A] [IsScalarTower R A A]
variable [SMulCommClass R B B] [IsScalarTower R B B]

/-- The multiplication in a non-unital algebra is a bilinear map.

A weaker version of this for non-unital non-associative algebras exists as `LinearMap.mul`. -/
def _root_.NonUnitalAlgHom.lmul : A →ₙₐ[R] End R A where
  __ := mul R A
  map_mul' := mulLeft_mul _ _
  map_zero' := mulLeft_zero_eq_zero _ _

variable {R A B}

@[simp]
theorem _root_.NonUnitalAlgHom.coe_lmul_eq_mul : ⇑(NonUnitalAlgHom.lmul R A) = mul R A :=
  rfl

@[target] theorem commute_mulLeft_right (a b : A) : Commute (mulLeft R a) (mulRight R b) := by
  sorry


/-- A `LinearMap` preserves multiplication if pre- and post- composition with `LinearMap.mul` are
equivalent. By converting the statement into an equality of `LinearMap`s, this lemma allows various
specialized `ext` lemmas about `→ₗ[R]` to then be applied.

This is the `LinearMap` version of `AddMonoidHom.map_mul_iff`. -/
/-- A `LinearMap` preserves multiplication if pre- and post- composition with `LinearMap.mul` are
equivalent. By converting the statement into an equality of `LinearMap`s, this lemma allows various
specialized `ext` lemmas about `→ₗ[R]` to then be applied.

This is the `LinearMap` version of `AddMonoidHom.map_mul_iff`. -/
@[target] theorem map_mul_iff (f : A →ₗ[R] B) :
    (∀ x y, f (x * y) = f x * f y) ↔
      (LinearMap.mul R A).compr₂ f = (LinearMap.mul R B ∘ₗ f).compl₂ f := by sorry


end NonUnital

section Semiring

variable (R A : Type*)
section one_side
variable [Semiring R] [Semiring A]

section left
variable [Module R A] [SMulCommClass R A A]

@[target] theorem mulLeft_one : mulLeft R (1 : A) = LinearMap.id := by sorry


@[target] theorem mulLeft_eq_zero_iff (a : A) : mulLeft R a = 0 ↔ a = 0 := by
  sorry


@[target] theorem pow_mulLeft (a : A) (n : ℕ) : mulLeft R a ^ n = mulLeft R (a ^ n) :=
  match n with
  | 0 => by sorry


end left

section right
variable [Module R A] [IsScalarTower R A A]

@[target] theorem mulRight_one : mulRight R (1 : A) = LinearMap.id := by sorry


@[target] theorem mulRight_eq_zero_iff (a : A) : mulRight R a = 0 ↔ a = 0 := by
  sorry


@[target] theorem pow_mulRight (a : A) (n : ℕ) : mulRight R a ^ n = mulRight R (a ^ n) :=
  match n with
  | 0 => by sorry


end right

end one_side

variable [CommSemiring R] [Semiring A] [Algebra R A]

/-- The multiplication in an algebra is an algebra homomorphism into the endomorphisms on
the algebra.

A weaker version of this for non-unital algebras exists as `NonUnitalAlgHom.lmul`. -/
def _root_.Algebra.lmul : A →ₐ[R] End R A where
  __ := NonUnitalAlgHom.lmul R A
  map_one' := mulLeft_one _ _
  commutes' r := ext fun a => (Algebra.smul_def r a).symm

variable {R A}

@[simp]
theorem _root_.Algebra.coe_lmul_eq_mul : ⇑(Algebra.lmul R A) = mul R A :=
  rfl

theorem _root_.Algebra.lmul_injective : Function.Injective (Algebra.lmul R A) :=
  fun a₁ a₂ h ↦ by simpa using DFunLike.congr_fun h 1

theorem _root_.Algebra.lmul_isUnit_iff {x : A} :
    IsUnit (Algebra.lmul R A x) ↔ IsUnit x := by
  rw [Module.End_isUnit_iff, Iff.comm]
  exact IsUnit.isUnit_iff_mulLeft_bijective

@[target] theorem toSpanSingleton_eq_algebra_linearMap : toSpanSingleton R A 1 = Algebra.linearMap R A := by
  sorry


end Semiring

section Ring

variable {R A : Type*} [CommSemiring R] [Ring A] [Algebra R A]

@[deprecated mul_right_injective₀ (since := by sorry


@[deprecated mul_right_injective₀ (since := by sorry


end Ring

end LinearMap
