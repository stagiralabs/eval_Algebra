import VerifiedAgora.tagger
/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Quaternion
import Mathlib.Tactic.Ring

/-!
# Basis on a quaternion-like algebra

## Main definitions

* `QuaternionAlgebra.Basis A c₁ c₂ c₃`: a basis for a subspace of an `R`-algebra `A` that has the
  same algebra structure as `ℍ[R,c₁,c₂,c₃]`.
* `QuaternionAlgebra.Basis.self R`: the canonical basis for `ℍ[R,c₁,c₂,c₃]`.
* `QuaternionAlgebra.Basis.compHom b f`: transform a basis `b` by an AlgHom `f`.
* `QuaternionAlgebra.lift`: Define an `AlgHom` out of `ℍ[R,c₁,c₂,c₃]` by its action on the basis
  elements `i`, `j`, and `k`. In essence, this is a universal property. Analogous to `Complex.lift`,
  but takes a bundled `QuaternionAlgebra.Basis` instead of just a `Subtype` as the amount of
  data / proves is non-negligible.
-/


open Quaternion

namespace QuaternionAlgebra

/-- A quaternion basis contains the information both sufficient and necessary to construct an
`R`-algebra homomorphism from `ℍ[R,c₁,c₂,c₃]` to `A`; or equivalently, a surjective
`R`-algebra homomorphism from `ℍ[R,c₁,c₂,c₃]` to an `R`-subalgebra of `A`.

Note that for definitional convenience, `k` is provided as a field even though `i_mul_j` fully
determines it. -/
structure Basis {R : Type*} (A : Type*) [CommRing R] [Ring A] [Algebra R A] (c₁ c₂ c₃ : R) where
  /-- The first imaginary unit -/
  i : A
  /-- The second imaginary unit -/
  j : A
  /-- The third imaginary unit -/
  k : A
  i_mul_i : i * i = c₁ • (1 : A) + c₂ • i
  j_mul_j : j * j = c₃ • (1 : A)
  i_mul_j : i * j = k
  j_mul_i : j * i = c₂ • j - k

variable {R : Type*} {A B : Type*} [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
variable {c₁ c₂ c₃: R}

namespace Basis

/-- Since `k` is redundant, it is not necessary to show `q₁.k = q₂.k` when showing `q₁ = q₂`. -/
@[ext]
protected theorem ext ⦃q₁ q₂ : Basis A c₁ c₂ c₃⦄ (hi : q₁.i = q₂.i)
    (hj : q₁.j = q₂.j) : q₁ = q₂ := by
  cases q₁; rename_i q₁_i_mul_j _
  cases q₂; rename_i q₂_i_mul_j _
  congr
  rw [← q₁_i_mul_j, ← q₂_i_mul_j]
  congr

variable (R) in
/-- There is a natural quaternionic basis for the `QuaternionAlgebra`. -/
@[simps i j k]
protected def self : Basis ℍ[R,c₁,c₂,c₃] c₁ c₂ c₃ where
  i := ⟨0, 1, 0, 0⟩
  i_mul_i := by ext <;> simp
  j := ⟨0, 0, 1, 0⟩
  j_mul_j := by ext <;> simp
  k := ⟨0, 0, 0, 1⟩
  i_mul_j := by ext <;> simp
  j_mul_i := by ext <;> simp

instance : Inhabited (Basis ℍ[R,c₁,c₂,c₃] c₁ c₂ c₃) :=
  ⟨Basis.self R⟩

variable (q : Basis A c₁ c₂ c₃)

attribute [simp] i_mul_i j_mul_j i_mul_j j_mul_i

@[target] theorem i_mul_k : q.i * q.k = c₁ • q.j + c₂ • q.k := by
  sorry


@[target] theorem k_mul_i : q.k * q.i = -c₁ • q.j := by
  sorry


@[target] theorem k_mul_j : q.k * q.j = c₃ • q.i := by
  sorry


@[target] theorem j_mul_k : q.j * q.k = (c₂ * c₃) • 1 - c₃ • q.i := by
  sorry


@[simp]
theorem k_mul_k : q.k * q.k = -((c₁ * c₃) • (1 : A)) := by
  rw [← i_mul_j, mul_assoc, ← mul_assoc q.j _ _, j_mul_i, ← i_mul_j, ← mul_assoc, mul_sub, ←
    mul_assoc, i_mul_i, add_mul, smul_mul_assoc, one_mul, sub_mul, smul_mul_assoc, mul_smul_comm,
    smul_mul_assoc, mul_assoc, j_mul_j, add_mul, smul_mul_assoc, j_mul_j, smul_smul,
    smul_mul_assoc, mul_assoc, j_mul_j]
  linear_combination (norm := module)


/-- Intermediate result used to define `QuaternionAlgebra.Basis.liftHom`. -/
def lift (x : ℍ[R,c₁,c₂,c₃]) : A :=
  algebraMap R _ x.re + x.imI • q.i + x.imJ • q.j + x.imK • q.k

@[target] theorem lift_zero : q.lift (0 : ℍ[R,c₁,c₂,c₃]) = 0 := by sorry


theorem lift_one : q.lift (1 : ℍ[R,c₁,c₂,c₃]) = 1 := by simp [lift]

@[target] theorem lift_add (x y : ℍ[R,c₁,c₂,c₃]) : q.lift (x + y) = q.lift x + q.lift y := by
  sorry


@[target] theorem lift_mul (x y : ℍ[R,c₁,c₂,c₃]) : q.lift (x * y) = q.lift x * q.lift y := by
  sorry


set_option linter.unusedVariables false in
/-- Scaling on the left is sent by `DualNumber.lift` to multiplication on the left -/
@[target] theorem lift_smul (fe : {fe : (A →ₐ[R] B) × B // _}) (a : A) (ad : A[ε]) :
    lift fe (a • ad) = fe.val.1 a * lift fe ad := by
  sorry


/-- A `QuaternionAlgebra.Basis` implies an `AlgHom` from the quaternions. -/
/-- A `QuaternionAlgebra.Basis` implies an `AlgHom` from the quaternions. -/
@[simps!]
def liftHom : ℍ[R,c₁,c₂,c₃] →ₐ[R] A := by sorry


/-- Transform a `QuaternionAlgebra.Basis` through an `AlgHom`. -/
@[simps i j k]
def compHom (F : A →ₐ[R] B) : Basis B c₁ c₂ c₃ where
  i := F q.i
  i_mul_i := by rw [← map_mul, q.i_mul_i, map_add, map_smul, map_smul, map_one]
  j := F q.j
  j_mul_j := by rw [← map_mul, q.j_mul_j, map_smul, map_one]
  k := F q.k
  i_mul_j := by rw [← map_mul, q.i_mul_j]
  j_mul_i := by rw [← map_mul, q.j_mul_i, map_sub, map_smul]

end Basis

/-- A quaternionic basis on `A` is equivalent to a map from the quaternion algebra to `A`. -/
@[simps]
def lift : Basis A c₁ c₂ c₃ ≃ (ℍ[R,c₁,c₂,c₃] →ₐ[R] A) where
  toFun := Basis.liftHom
  invFun := (Basis.self R).compHom
  left_inv q := by ext <;> simp [Basis.lift]
  right_inv F := by
    ext
    dsimp [Basis.lift]
    rw [← F.commutes]
    simp only [← F.commutes, ← map_smul, ← map_add, mk_add_mk, smul_mk, smul_zero,
      algebraMap_eq]
    congr <;> simp

/-- Two `R`-algebra morphisms from a quaternion algebra are equal if they agree on `i` and `j`. -/
@[target] lemma hom_ext {R S : BoolRing} {f g : R ⟶ S} (hf : f.hom = g.hom) : f = g := by sorry


end QuaternionAlgebra

namespace Quaternion
variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

open QuaternionAlgebra (Basis)

/-- Two `R`-algebra morphisms from the quaternions are equal if they agree on `i` and `j`. -/
@[ext]
theorem hom_ext ⦃f g : ℍ[R] →ₐ[R] A⦄
    (hi : f (Basis.self R).i = g (Basis.self R).i) (hj : f (Basis.self R).j = g (Basis.self R).j) :
    f = g :=
  QuaternionAlgebra.hom_ext hi hj

end Quaternion
