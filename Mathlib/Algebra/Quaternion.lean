import VerifiedAgora.tagger
/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# Quaternions

In this file we define quaternions `ℍ[R]` over a commutative ring `R`, and define some
algebraic structures on `ℍ[R]`.

## Main definitions

* `QuaternionAlgebra R a b c`, `ℍ[R, a, b, c]` :
  [Bourbaki, *Algebra I*][bourbaki1989] with coefficients `a`, `b`, `c`
  (Many other references such as Wikipedia assume $\operatorname{char} R ≠ 2$ therefore one can
  complete the square and WLOG assume $b = 0$.)
* `Quaternion R`, `ℍ[R]` : the space of quaternions, a.k.a.
  `QuaternionAlgebra R (-1) (0) (-1)`;
* `Quaternion.normSq` : square of the norm of a quaternion;

We also define the following algebraic structures on `ℍ[R]`:

* `Ring ℍ[R, a, b, c]`, `StarRing ℍ[R, a, b, c]`, and `Algebra R ℍ[R, a, b, c]` :
  for any commutative ring `R`;
* `Ring ℍ[R]`, `StarRing ℍ[R]`, and `Algebra R ℍ[R]` : for any commutative ring `R`;
* `IsDomain ℍ[R]` : for a linear ordered commutative ring `R`;
* `DivisionRing ℍ[R]` : for a linear ordered field `R`.

## Notation

The following notation is available with `open Quaternion` or `open scoped Quaternion`.

* `ℍ[R, c₁, c₂, c₃]` : `QuaternionAlgebra R c₁ c₂ c₃`
* `ℍ[R, c₁, c₂]` : `QuaternionAlgebra R c₁ 0 c₂`
* `ℍ[R]` : quaternions over `R`.

## Implementation notes

We define quaternions over any ring `R`, not just `ℝ` to be able to deal with, e.g., integer
or rational quaternions without using real numbers. In particular, all definitions in this file
are computable.

## Tags

quaternion
-/


/-- Quaternion algebra over a type with fixed coefficients where $i^2 = a + bi$ and $j^2 = c$,
denoted as `ℍ[R,a,b]`.
Implemented as a structure with four fields: `re`, `imI`, `imJ`, and `imK`. -/
@[ext]
structure QuaternionAlgebra (R : Type*) (a b c : R) where
  /-- Real part of a quaternion. -/
  re : R
  /-- First imaginary part (i) of a quaternion. -/
  imI : R
  /-- Second imaginary part (j) of a quaternion. -/
  imJ : R
  /-- Third imaginary part (k) of a quaternion. -/
  imK : R

@[inherit_doc]
scoped[Quaternion] notation "ℍ[" R "," a "," b "," c "]" =>
    QuaternionAlgebra R a b c

@[inherit_doc]
scoped[Quaternion] notation "ℍ[" R "," a "," b "]" => QuaternionAlgebra R a 0 b

namespace QuaternionAlgebra
open Quaternion

/-- The equivalence between a quaternion algebra over `R` and `R × R × R × R`. -/
/-- The equivalence between a quaternion algebra over `R` and `R × R × R × R`. -/
@[simps]
def equivProd {R : Type*} (c₁ c₂ c₃: R) : ℍ[R,c₁,c₂,c₃] ≃ R × R × R × R where
  toFun a := by sorry


/-- The equivalence between a quaternion algebra over `R` and `Fin 4 → R`. -/
@[simps symm_apply]
def equivTuple {R : Type*} (c₁ c₂ c₃: R) : ℍ[R,c₁,c₂,c₃] ≃ (Fin 4 → R) where
  toFun a := ![a.1, a.2, a.3, a.4]
  invFun a := ⟨a 0, a 1, a 2, a 3⟩
  left_inv _ := rfl
  right_inv f := by ext ⟨_, _ | _ | _ | _ | _ | ⟨⟩⟩ <;> rfl

@[simp]
theorem equivTuple_apply {R : Type*} (c₁ c₂ c₃: R) (x : ℍ[R,c₁,c₂,c₃]) :
    equivTuple c₁ c₂ c₃ x = ![x.re, x.imI, x.imJ, x.imK] :=
  rfl

@[simp]
theorem mk.eta {R : Type*} {c₁ c₂ c₃} (a : ℍ[R,c₁,c₂,c₃]) : mk a.1 a.2 a.3 a.4 = a := rfl

variable {S T R : Type*} {c₁ c₂ c₃ : R} (r x y : R) (a b : ℍ[R,c₁,c₂,c₃])

instance [Subsingleton R] : Subsingleton ℍ[R, c₁, c₂, c₃] := (equivTuple c₁ c₂ c₃).subsingleton
instance [Nontrivial R] : Nontrivial ℍ[R, c₁, c₂, c₃] := (equivTuple c₁ c₂ c₃).surjective.nontrivial

section Zero
variable [Zero R]

/-- The imaginary part of a quaternion.

Note that unless `c₂ = 0`, this definition is not particularly well-behaved;
for instance, `QuaternionAlgebra.star_im` only says that the star of an imaginary quaternion
is imaginary under this condition. -/
def im (x : ℍ[R,c₁,c₂,c₃]) : ℍ[R,c₁,c₂,c₃] :=
  ⟨0, x.imI, x.imJ, x.imK⟩

@[target] theorem im_re : a.im.re = 0 := by sorry


@[target] theorem im_imI : a.im.imI = a.imI := by sorry


@[target] theorem im_imJ : a.im.imJ = a.imJ := by sorry


@[target] theorem im_imK : a.im.imK = a.imK := by sorry


@[target] theorem im_idem : a.im.im = a.im := by sorry


/-- Coercion `R → ℍ[R,c₁,c₂,c₃]`. -/
/-- Coercion `R → ℍ[R,c₁,c₂,c₃]`. -/
@[coe] def coe (x : R) : ℍ[R,c₁,c₂,c₃] := by sorry


instance : CoeTC R ℍ[R,c₁,c₂,c₃] := ⟨coe⟩

@[target] theorem coe_re : (x : ℍ[R,c₁,c₂,c₃]).re = x := by sorry


@[target] theorem coe_imI : (x : ℍ[R,c₁,c₂,c₃]).imI = 0 := by sorry


@[target] theorem coe_imJ : (x : ℍ[R,c₁,c₂,c₃]).imJ = 0 := by sorry


@[target] theorem coe_imK : (x : ℍ[R,c₁,c₂,c₃]).imK = 0 := by sorry


@[target] theorem coe_injective : @Function.Injective (A →ₛₙₐ[φ] B) (A → B) (↑) := by
  sorry


@[target] theorem coe_inj {a b : R} : (↑a : A) = ↑b ↔ a = b := by sorry

instance : Zero ℍ[R,c₁,c₂,c₃] := ⟨⟨0, 0, 0, 0⟩⟩

@[scoped simp] theorem zero_re : (0 : ℍ[R,c₁,c₂,c₃]).re = 0 := rfl

@[target] theorem zero_imI : (0 : ℍ[R,c₁,c₂,c₃]).imI = 0 := by sorry


@[target] theorem zero_imJ : (0 : ℍ[R,c₁,c₂,c₃]).imJ = 0 := by sorry


@[target] theorem zero_imK : (0 : ℍ[R,c₁,c₂,c₃]).imK = 0 := by sorry


@[target] theorem zero_im : (0 : ℍ[R,c₁,c₂,c₃]).im = 0 := by sorry


@[target] theorem coe_zero : (↑(0 : R) : A) = 0 := by sorry


instance : Inhabited ℍ[R,c₁,c₂,c₃] := ⟨0⟩

section One
variable [One R]

-- Porting note: removed `simps`, added simp lemmas manually. Should adjust `simps` to name properly
instance : One ℍ[R,c₁,c₂,c₃] := ⟨⟨1, 0, 0, 0⟩⟩

@[target] theorem one_re : (1 : ℍ[R,c₁,c₂,c₃]).re = 1 := by sorry


@[target] theorem one_imI : (1 : ℍ[R,c₁,c₂,c₃]).imI = 0 := by sorry


@[target] theorem one_imJ : (1 : ℍ[R,c₁,c₂,c₃]).imJ = 0 := by sorry


@[target] theorem one_imK : (1 : ℍ[R,c₁,c₂,c₃]).imK = 0 := by sorry


@[target] theorem one_im : (1 : ℍ[R,c₁,c₂,c₃]).im = 0 := by sorry


@[target] theorem coe_one : (↑(1 : R) : A) = 1 := by sorry


end One
end Zero
section Add
variable [Add R]

-- Porting note: removed `simps`, added simp lemmas manually. Should adjust `simps` to name properly
instance : Add ℍ[R,c₁,c₂,c₃] :=
  ⟨fun a b => ⟨a.1 + b.1, a.2 + b.2, a.3 + b.3, a.4 + b.4⟩⟩

@[target] theorem add_re : (a + b).re = a.re + b.re := by sorry


@[target] theorem add_imI : (a + b).imI = a.imI + b.imI := by sorry


@[target] theorem add_imJ : (a + b).imJ = a.imJ + b.imJ := by sorry


@[target] theorem add_imK : (a + b).imK = a.imK + b.imK := by sorry


@[simp]
theorem mk_add_mk (a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : R) :
    (mk a₁ a₂ a₃ a₄ : ℍ[R,c₁,c₂,c₃]) + mk b₁ b₂ b₃ b₄ =
    mk (a₁ + b₁) (a₂ + b₂) (a₃ + b₃) (a₄ + b₄) :=
  rfl

end Add

section AddZeroClass
variable [AddZeroClass R]

@[target] theorem add_im : (a + b).im = a.im + b.im := by sorry


@[target] theorem coe_add (a b : R) : (↑(a + b : R) : A) = ↑a + ↑b := by sorry


end AddZeroClass

section Neg
variable [Neg R]

-- Porting note: removed `simps`, added simp lemmas manually. Should adjust `simps` to name properly
instance : Neg ℍ[R,c₁,c₂,c₃] := ⟨fun a => ⟨-a.1, -a.2, -a.3, -a.4⟩⟩

@[target] theorem neg_re : (-a).re = -a.re := by sorry


@[target] theorem neg_imI : (-a).imI = -a.imI := by sorry


@[target] theorem neg_imJ : (-a).imJ = -a.imJ := by sorry


@[target] theorem neg_imK : (-a).imK = -a.imK := by sorry


@[target] theorem neg_mk (a₁ a₂ a₃ a₄ : R) : -(mk a₁ a₂ a₃ a₄ : ℍ[R,c₁,c₂,c₃]) = ⟨-a₁, -a₂, -a₃, -a₄⟩ := by sorry


end Neg

section AddGroup
variable [AddGroup R]

@[target] theorem neg_im : (-a).im = -a.im := by sorry


@[target] theorem coe_neg (x : R) : (↑(-x : R) : A) = -↑x := by sorry


instance : Sub ℍ[R,c₁,c₂,c₃] :=
  ⟨fun a b => ⟨a.1 - b.1, a.2 - b.2, a.3 - b.3, a.4 - b.4⟩⟩

@[target] theorem sub_re : (a - b).re = a.re - b.re := by sorry


@[target] theorem sub_imI : (a - b).imI = a.imI - b.imI := by sorry


@[target] theorem sub_imJ : (a - b).imJ = a.imJ - b.imJ := by sorry


@[target] theorem sub_imK : (a - b).imK = a.imK - b.imK := by sorry


@[target] theorem sub_im : (a - b).im = a.im - b.im := by sorry


@[target] theorem mk_sub_mk (a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : R) :
    (mk a₁ a₂ a₃ a₄ : ℍ[R,c₁,c₂,c₃]) - mk b₁ b₂ b₃ b₄ =
    mk (a₁ - b₁) (a₂ - b₂) (a₃ - b₃) (a₄ - b₄) := by sorry


@[target] theorem coe_im : (x : ℍ[R,c₁,c₂,c₃]).im = 0 := by sorry


@[target] theorem re_add_im : ↑a.re + a.im = a := by sorry


@[target] theorem sub_self_im : a - a.im = a.re := by sorry


@[target] theorem sub_self_re : a - a.re = a.im := by sorry


end AddGroup

section Ring
variable [Ring R]

/-- Multiplication is given by

* `1 * x = x * 1 = x`;
* `i * i = c₁ + c₂ * i`;
* `j * j = c₃`;
* `i * j = k`, `j * i = c₂ * j - k`;
* `k * k = - c₁ * c₃`;
* `i * k = c₁ * j + c₂ * k`, `k * i = -c₁ * j`;
* `j * k = c₂ * c₃ - c₃ * i`, `k * j = c₃ * i`. -/
instance : Mul ℍ[R,c₁,c₂,c₃] :=
  ⟨fun a b =>
    ⟨a.1 * b.1 + c₁ * a.2 * b.2 + c₃ * a.3 * b.3 + c₂ * c₃ * a.3 * b.4 - c₁ * c₃ * a.4 * b.4,
      a.1 * b.2 + a.2 * b.1 + c₂ * a.2 * b.2 - c₃ * a.3 * b.4 + c₃ * a.4 * b.3,
      a.1 * b.3 + c₁ * a.2 * b.4 + a.3 * b.1 + c₂ * a.3 * b.2 - c₁ * a.4 * b.2,
      a.1 * b.4 + a.2 * b.3 + c₂ * a.2 * b.4 - a.3 * b.2 + a.4 * b.1⟩⟩

@[target] theorem mul_re : (a * b).re = a.1 * b.1 + c₁ * a.2 * b.2 + c₃ * a.3 * b.3 +
    c₂ * c₃ * a.3 * b.4 - c₁ * c₃ * a.4 * b.4 := by sorry


@[target] theorem mul_imI : (a * b).imI = a.1 * b.2 + a.2 * b.1 +
    c₂ * a.2 * b.2 - c₃ * a.3 * b.4 + c₃ * a.4 * b.3 := by sorry


@[target] theorem mul_imJ : (a * b).imJ = a.1 * b.3 + c₁ * a.2 * b.4 + a.3 * b.1 +
    c₂ * a.3 * b.2 - c₁ * a.4 * b.2 := by sorry


@[target] theorem mul_imK : (a * b).imK = a.1 * b.4 + a.2 * b.3 +
    c₂ * a.2 * b.4 - a.3 * b.2 + a.4 * b.1 := by sorry


@[target] theorem mk_mul_mk {x y : M} : Associates.mk x * Associates.mk y = Associates.mk (x * y) := by sorry


end Ring
section SMul

variable [SMul S R] [SMul T R] (s : S)

instance : SMul S ℍ[R,c₁,c₂,c₃] where smul s a := ⟨s • a.1, s • a.2, s • a.3, s • a.4⟩

instance [SMul S T] [IsScalarTower S T R] : IsScalarTower S T ℍ[R,c₁,c₂,c₃] where
  smul_assoc s t x := by ext <;> exact smul_assoc _ _ _

instance [SMulCommClass S T R] : SMulCommClass S T ℍ[R,c₁,c₂,c₃] where
  smul_comm s t x := by ext <;> exact smul_comm _ _ _

@[target] theorem smul_re : (s • a).re = s • a.re := by sorry


@[simp] theorem smul_imI : (s • a).imI = s • a.imI := rfl

@[target] theorem smul_imJ : (s • a).imJ = s • a.imJ := by sorry


@[target] theorem smul_imK : (s • a).imK = s • a.imK := by sorry


@[target] theorem smul_im {S} [CommRing R] [SMulZeroClass S R] (s : S) : (s • a).im = s • a.im := by sorry


@[simp]
theorem smul_mk (re im_i im_j im_k : R) :
    s • (⟨re, im_i, im_j, im_k⟩ : ℍ[R,c₁,c₂,c₃]) = ⟨s • re, s • im_i, s • im_j, s • im_k⟩ :=
  rfl

end SMul

@[target] theorem algebraMap.coe_smul (A B C : Type*) [SMul A B] [CommSemiring B] [Semiring C] [Algebra B C]
    [SMul A C] [IsScalarTower A B C] (a : A) (b : B) : (a • b : B) = a • (b : C) := by sorry


instance [AddCommGroup R] : AddCommGroup ℍ[R,c₁,c₂,c₃] :=
  (equivProd c₁ c₂ c₃).injective.addCommGroup _ rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

section AddCommGroupWithOne
variable [AddCommGroupWithOne R]

instance : AddCommGroupWithOne ℍ[R,c₁,c₂,c₃] where
  natCast n := ((n : R) : ℍ[R,c₁,c₂,c₃])
  natCast_zero := by simp
  natCast_succ := by simp
  intCast n := ((n : R) : ℍ[R,c₁,c₂,c₃])
  intCast_ofNat _ := congr_arg coe (Int.cast_natCast _)
  intCast_negSucc n := by
    change coe _ = -coe _
    rw [Int.cast_negSucc, coe_neg]

@[target] theorem natCast_re (n : ℕ) : (n : ℍ[R,c₁,c₂,c₃]).re = n := by sorry


@[target] theorem natCast_imI (n : ℕ) : (n : ℍ[R,c₁,c₂,c₃]).imI = 0 := by sorry


@[target] theorem natCast_imJ (n : ℕ) : (n : ℍ[R,c₁,c₂,c₃]).imJ = 0 := by sorry


@[target] theorem natCast_imK (n : ℕ) : (n : ℍ[R,c₁,c₂,c₃]).imK = 0 := by sorry


@[target] theorem natCast_im (n : ℕ) : (n : ℍ[R,c₁,c₂,c₃]).im = 0 := by sorry


@[target] theorem coe_natCast (a : ℕ) : (↑(a : R) : A) = a := by sorry


@[target] theorem intCast_re (z : ℤ) : (z : ℍ[R,c₁,c₂,c₃]).re = z := by sorry


@[target] theorem ofNat_re (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : ℍ[R,c₁,c₂,c₃]).re = ofNat(n) := by sorry


@[target] theorem ofNat_imI (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : ℍ[R,c₁,c₂,c₃]).imI = 0 := by sorry


@[scoped simp]
theorem ofNat_imJ (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : ℍ[R,c₁,c₂,c₃]).imJ = 0 := rfl

@[scoped simp]
theorem ofNat_imK (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : ℍ[R,c₁,c₂,c₃]).imK = 0 := rfl

@[target] theorem ofNat_im (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : ℍ[R,c₁,c₂,c₃]).im = 0 := by sorry


@[target] theorem intCast_imI (z : ℤ) : (z : ℍ[R,c₁,c₂,c₃]).imI = 0 := by sorry


@[target] theorem intCast_imJ (z : ℤ) : (z : ℍ[R,c₁,c₂,c₃]).imJ = 0 := by sorry


@[target] theorem intCast_imK (z : ℤ) : (z : ℍ[R,c₁,c₂,c₃]).imK = 0 := by sorry


@[target] theorem intCast_im (z : ℤ) : (z : ℍ[R,c₁,c₂,c₃]).im = 0 := by sorry


@[target] theorem coe_intCast (z : ℤ) : ⇑(z : CentroidHom α) = z • (CentroidHom.id α) := by sorry


end AddCommGroupWithOne

-- For the remainder of the file we assume `CommRing R`.
variable [CommRing R]

instance instRing : Ring ℍ[R,c₁,c₂,c₃] where
  __ := inferInstanceAs (AddCommGroupWithOne ℍ[R,c₁,c₂,c₃])
  left_distrib _ _ _ := by ext <;> simp <;> ring
  right_distrib _ _ _ := by ext <;> simp <;> ring
  zero_mul _ := by ext <;> simp
  mul_zero _ := by ext <;> simp
  mul_assoc _ _ _ := by ext <;> simp <;> ring
  one_mul _ := by ext <;> simp
  mul_one _ := by ext <;> simp

@[norm_cast, simp]
theorem coe_mul : ((x * y : R) : ℍ[R,c₁,c₂,c₃]) = x * y := by ext <;> simp

@[target] theorem coe_ofNat (n : ℕ) [n.AtLeastTwo] :
    (ofNat(n) : A 0) = (ofNat(n) : R) := by sorry

instance [CommSemiring S] [Algebra S R] : Algebra S ℍ[R,c₁,c₂,c₃] where
  smul := (· • ·)
  algebraMap :=
  { toFun s := coe (algebraMap S R s)
    map_one' := by simp only [map_one, coe_one]
    map_zero' := by simp only [map_zero, coe_zero]
    map_mul' x y := by simp only [map_mul, coe_mul]
    map_add' x y := by simp only [map_add, coe_add] }
  smul_def' s x := by ext <;> simp [Algebra.smul_def]
  commutes' s x := by ext <;> simp [Algebra.commutes]

@[target] theorem algebraMap_eq : algebraMap R A = (algebraMap S A).comp (algebraMap R S) :=
  RingHom.ext fun x => by
    sorry


@[target] lemma algebraMap_injective : Injective (algebraMap R A) := by sorry


instance [NoZeroDivisors R] : NoZeroSMulDivisors R ℍ[R,c₁,c₂,c₃] := ⟨by
  rintro t ⟨a, b, c, d⟩ h
  rw [or_iff_not_imp_left]
  intro ht
  simpa [QuaternionAlgebra.ext_iff, ht] using h⟩

section

variable (c₁ c₂ c₃)

/-- `QuaternionAlgebra.re` as a `LinearMap` -/
@[simps]
def reₗ : ℍ[R,c₁,c₂,c₃] →ₗ[R] R where
  toFun := re
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `QuaternionAlgebra.imI` as a `LinearMap` -/
@[simps]
def imIₗ : ℍ[R,c₁,c₂,c₃] →ₗ[R] R where
  toFun := imI
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `QuaternionAlgebra.imJ` as a `LinearMap` -/
@[simps]
def imJₗ : ℍ[R,c₁,c₂,c₃] →ₗ[R] R where
  toFun := imJ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `QuaternionAlgebra.imK` as a `LinearMap` -/
@[simps]
def imKₗ : ℍ[R,c₁,c₂,c₃] →ₗ[R] R where
  toFun := imK
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `QuaternionAlgebra.equivTuple` as a linear equivalence. -/
/-- `QuaternionAlgebra.equivTuple` as a linear equivalence. -/
def linearEquivTuple : ℍ[R,c₁,c₂,c₃] ≃ₗ[R] Fin 4 → R := by sorry


@[target] theorem coe_linearEquivTuple :
    ⇑(linearEquivTuple c₁ c₂ c₃) = equivTuple c₁ c₂ c₃ := by sorry


@[simp]
theorem coe_linearEquivTuple_symm :
    ⇑(linearEquivTuple c₁ c₂ c₃).symm = (equivTuple c₁ c₂ c₃).symm := rfl

/-- `ℍ[R, c₁, c₂, c₃]` has a basis over `R` given by `1`, `i`, `j`, and `k`. -/
noncomputable def basisOneIJK : Basis (Fin 4) R ℍ[R,c₁,c₂,c₃] :=
  .ofEquivFun <| linearEquivTuple c₁ c₂ c₃

@[target] theorem coe_basisOneIJK_repr (q : ℍ[R,c₁,c₂,c₃]) :
    ((basisOneIJK c₁ c₂ c₃).repr q) = ![q.re, q.imI, q.imJ, q.imK] := by sorry


instance : Module.Finite R ℍ[R,c₁,c₂,c₃] := .of_basis (basisOneIJK c₁ c₂ c₃)

instance : Module.Free R ℍ[R,c₁,c₂,c₃] := .of_basis (basisOneIJK c₁ c₂ c₃)

@[target] theorem rank_eq_four [StrongRankCondition R] : Module.rank R ℍ[R,c₁,c₂,c₃] = 4 := by
  sorry


@[target] theorem finrank_eq_four [StrongRankCondition R] : Module.finrank R ℍ[R,c₁,c₂,c₃] = 4 := by
  sorry


/-- There is a natural equivalence when swapping the first and third coefficients of a
  quaternion algebra if `c₂` is 0. -/
/-- There is a natural equivalence when swapping the first and third coefficients of a
  quaternion algebra if `c₂` is 0. -/
@[simps]
def swapEquiv : ℍ[R,c₁,0,c₃] ≃ₐ[R] ℍ[R,c₃,0,c₁] where
  toFun t := ⟨t.1, t.3, t.2, -t.4⟩
  invFun t := ⟨t.1, t.3, t.2, -t.4⟩
  left_inv _ := by sorry


end

@[target] theorem coe_sub (a b : R) :
    (↑(a - b : R) : A) = ↑a - ↑b := by sorry


@[target] theorem coe_pow (a : R) (n : ℕ) : (↑(a ^ n : R) : A) = (a : A) ^ n := by sorry


@[target] theorem coe_commutes : ↑r * a = a * r := by sorry


@[target] theorem coe_commute : Commute (↑r) a := by sorry


@[target] theorem coe_mul_eq_smul : ↑r * a = r • a := by sorry


@[target] theorem mul_coe_eq_smul : a * r = r • a := by sorry


@[target] theorem coe_algebraMap {A : Type*} [CommSemiring k] [Semiring A] [Algebra k A] [Monoid G] :
    ⇑(algebraMap k (MonoidAlgebra A G)) = single 1 ∘ algebraMap k A := by sorry


@[target] theorem smul_coe : x • (y : ℍ[R,c₁,c₂,c₃]) = ↑(x * y) := by sorry


/-- Quaternion conjugate. -/
instance instStarQuaternionAlgebra : Star ℍ[R,c₁,c₂,c₃] where star a :=
  ⟨a.1 + c₂ * a.2, -a.2, -a.3, -a.4⟩

@[simp] theorem re_star : (star a).re = a.re + c₂ * a.imI := rfl

@[simp]
theorem imI_star : (star a).imI = -a.imI :=
  rfl

@[target] theorem imJ_star : (star a).imJ = -a.imJ := by sorry


@[simp]
theorem imK_star : (star a).imK = -a.imK :=
  rfl

@[target] theorem im_star : (star a).im = -a.im := by sorry


@[target] theorem star_mk (a₁ a₂ a₃ a₄ : R) : star (mk a₁ a₂ a₃ a₄ : ℍ[R,c₁,c₂,c₃]) =
    ⟨a₁ + c₂ * a₂, -a₂, -a₃, -a₄⟩ := by sorry


instance instStarRing : StarRing ℍ[R,c₁,c₂,c₃] where
  star_involutive x := by simp [Star.star]
  star_add a b := by ext <;> simp [add_comm] ; ring
  star_mul a b := by ext <;> simp <;> ring

@[target] theorem self_add_star : a + star a = 2 * a.re + c₂ * a.imI := by sorry


theorem self_add_star : a + star a = 2 * a.re + c₂ * a.imI := by simp [self_add_star']

@[target] theorem star_add_self (x : R) : IsSelfAdjoint (star x + x) := by
  sorry


theorem star_add_self : star a + a = 2 * a.re + c₂ * a.imI := by rw [add_comm, self_add_star]

@[target] theorem star_eq_two_re_sub : star a = ↑(2 * a.re + c₂ * a.imI) - a := by sorry


protected theorem comm [Monoid M] {x y : M} : x ~ᵤ y ↔ y ~ᵤ x := by sorry


instance : IsStarNormal a :=
  ⟨by
    rw [commute_iff_eq, a.star_eq_two_re_sub];
    ext <;> simp <;> ring⟩

@[target] theorem star_coe : star (x : ℍ[R,c₁,c₂,c₃]) = x := by sorry


@[target] theorem star_im : star a.im = -a.im + c₂ * a.imI := by sorry


@[target] theorem star_smul [Monoid S] [DistribMulAction S R] [SMulCommClass S R R]
    (s : S) (a : ℍ[R,c₁,c₂,c₃]) :
    star (s • a) = s • star a :=
  QuaternionAlgebra.ext
    (by sorry


/-- A version of `star_smul` for the special case when `c₂ = 0`, without `SMulCommClass S R R`. -/
theorem star_smul' [Monoid S] [DistribMulAction S R] (s : S) (a : ℍ[R,c₁,0,c₃]) :
    star (s • a) = s • star a :=
  QuaternionAlgebra.ext (by simp) (smul_neg _ _).symm (smul_neg _ _).symm (smul_neg _ _).symm

@[target] theorem eq_re_of_eq_coe {a : ℍ[R,c₁,c₂,c₃]} {x : R} (h : a = x) : a = a.re := by sorry


@[target] theorem eq_re_iff_mem_range_coe {a : ℍ[R,c₁,c₂,c₃]} :
    a = a.re ↔ a ∈ Set.range (coe : R → ℍ[R,c₁,c₂,c₃]) := by sorry


section CharZero

variable [NoZeroDivisors R] [CharZero R]

@[target] theorem star_eq_self {c₁ c₂ : R} {a : ℍ[R,c₁,c₂,c₃]} : star a = a ↔ a = a.re := by
  sorry


@[target] theorem star_eq_neg {c₁ : R} {a : ℍ[R,c₁,0,c₃]} : star a = -a ↔ a.re = 0 := by
  sorry


end CharZero

-- Can't use `rw ← star_eq_self` in the proof without additional assumptions
@[target] theorem star_mul_eq_coe : star a * a = (star a * a).re := by sorry


theorem mul_star_eq_coe : a * star a = (a * star a).re := by
  rw [← star_comm_self']
  exact a.star_mul_eq_coe

open MulOpposite

/-- Quaternion conjugate as an `AlgEquiv` to the opposite ring. -/
/-- Quaternion conjugate as an `AlgEquiv` to the opposite ring. -/
def starAe : ℍ[R,c₁,c₂,c₃] ≃ₐ[R] ℍ[R,c₁,c₂,c₃]ᵐᵒᵖ :=
  { starAddEquiv.trans opAddEquiv with
    toFun := op ∘ star
    invFun := star ∘ unop
    map_mul' := fun x y => by sorry


@[target] theorem coe_starAe : ⇑(starAe : ℍ[R,c₁,c₂,c₃] ≃ₐ[R] _) = op ∘ star := by sorry


end QuaternionAlgebra

/-- Space of quaternions over a type, denoted as `ℍ[R]`.
Implemented as a structure with four fields: `re`, `im_i`, `im_j`, and `im_k`. -/
/-- Space of quaternions over a type, denoted as `ℍ[R]`.
Implemented as a structure with four fields: `re`, `im_i`, `im_j`, and `im_k`. -/
def Quaternion (R : Type*) [Zero R] [One R] [Neg R] := by sorry


@[inherit_doc]
scoped[Quaternion] notation "ℍ[" R "]" => Quaternion R

open Quaternion

/-- The equivalence between the quaternions over `R` and `R × R × R × R`. -/
@[simps!]
def Quaternion.equivProd (R : Type*) [Zero R] [One R] [Neg R] : ℍ[R] ≃ R × R × R × R :=
  QuaternionAlgebra.equivProd _ _ _

/-- The equivalence between the quaternions over `R` and `Fin 4 → R`. -/
@[simps! symm_apply]
def Quaternion.equivTuple (R : Type*) [Zero R] [One R] [Neg R] : ℍ[R] ≃ (Fin 4 → R) :=
  QuaternionAlgebra.equivTuple _ _ _

@[simp]
theorem Quaternion.equivTuple_apply (R : Type*) [Zero R] [One R] [Neg R] (x : ℍ[R]) :
    Quaternion.equivTuple R x = ![x.re, x.imI, x.imJ, x.imK] :=
  rfl

instance {R : Type*} [Zero R] [One R] [Neg R] [Subsingleton R] : Subsingleton ℍ[R] :=
  inferInstanceAs (Subsingleton <| ℍ[R, -1, 0, -1])
instance {R : Type*} [Zero R] [One R] [Neg R] [Nontrivial R] : Nontrivial ℍ[R] :=
  inferInstanceAs (Nontrivial <| ℍ[R, -1, 0, -1])

namespace Quaternion

variable {S T R : Type*} [CommRing R] (r x y : R) (a b : ℍ[R])

/-- Coercion `R → ℍ[R]`. -/
@[coe] def coe : R → ℍ[R] := QuaternionAlgebra.coe

instance : CoeTC R ℍ[R] := ⟨coe⟩

instance instRing : Ring ℍ[R] := QuaternionAlgebra.instRing

instance : Inhabited ℍ[R] := inferInstanceAs <| Inhabited ℍ[R,-1, 0, -1]

instance [SMul S R] : SMul S ℍ[R] := inferInstanceAs <| SMul S ℍ[R,-1, 0, -1]

instance [SMul S T] [SMul S R] [SMul T R] [IsScalarTower S T R] : IsScalarTower S T ℍ[R] :=
  inferInstanceAs <| IsScalarTower S T ℍ[R,-1,0,-1]

instance [SMul S R] [SMul T R] [SMulCommClass S T R] : SMulCommClass S T ℍ[R] :=
  inferInstanceAs <| SMulCommClass S T ℍ[R,-1,0,-1]

protected instance algebra [CommSemiring S] [Algebra S R] : Algebra S ℍ[R] :=
  inferInstanceAs <| Algebra S ℍ[R,-1,0,-1]

instance : Star ℍ[R] := QuaternionAlgebra.instStarQuaternionAlgebra
instance : StarRing ℍ[R] := QuaternionAlgebra.instStarRing
instance : IsStarNormal a := inferInstanceAs <| IsStarNormal (R := ℍ[R,-1,0,-1]) a

@[target] theorem Algebra.ext {S : Type u} {A : Type v} [CommSemiring S] [Semiring A] (h1 h2 : Algebra S A)
    (h : ∀ (r : S) (x : A), (by sorry


/-- The imaginary part of a quaternion. -/
nonrec def im (x : ℍ[R]) : ℍ[R] := x.im

@[simp] theorem im_re : a.im.re = 0 := rfl

@[simp] theorem im_imI : a.im.imI = a.imI := rfl

@[simp] theorem im_imJ : a.im.imJ = a.imJ := rfl

@[simp] theorem im_imK : a.im.imK = a.imK := rfl

@[simp] theorem im_idem : a.im.im = a.im := rfl

@[simp] nonrec theorem re_add_im : ↑a.re + a.im = a := a.re_add_im

@[simp] nonrec theorem sub_self_im : a - a.im = a.re := a.sub_self_im

@[simp] nonrec theorem sub_self_re : a - ↑a.re = a.im := a.sub_self_re

@[simp, norm_cast]
theorem coe_re : (x : ℍ[R]).re = x := rfl

@[simp, norm_cast]
theorem coe_imI : (x : ℍ[R]).imI = 0 := rfl

@[simp, norm_cast]
theorem coe_imJ : (x : ℍ[R]).imJ = 0 := rfl

@[simp, norm_cast]
theorem coe_imK : (x : ℍ[R]).imK = 0 := rfl

@[simp, norm_cast]
theorem coe_im : (x : ℍ[R]).im = 0 := rfl

@[scoped simp] theorem zero_re : (0 : ℍ[R]).re = 0 := rfl

@[scoped simp] theorem zero_imI : (0 : ℍ[R]).imI = 0 := rfl

@[scoped simp] theorem zero_imJ : (0 : ℍ[R]).imJ = 0 := rfl

@[scoped simp] theorem zero_imK : (0 : ℍ[R]).imK = 0 := rfl

@[scoped simp] theorem zero_im : (0 : ℍ[R]).im = 0 := rfl

@[simp, norm_cast]
theorem coe_zero : ((0 : R) : ℍ[R]) = 0 := rfl

@[scoped simp] theorem one_re : (1 : ℍ[R]).re = 1 := rfl

@[scoped simp] theorem one_imI : (1 : ℍ[R]).imI = 0 := rfl

@[scoped simp] theorem one_imJ : (1 : ℍ[R]).imJ = 0 := rfl

@[scoped simp] theorem one_imK : (1 : ℍ[R]).imK = 0 := rfl

@[scoped simp] theorem one_im : (1 : ℍ[R]).im = 0 := rfl

@[simp, norm_cast]
theorem coe_one : ((1 : R) : ℍ[R]) = 1 := rfl

@[simp] theorem add_re : (a + b).re = a.re + b.re := rfl

@[simp] theorem add_imI : (a + b).imI = a.imI + b.imI := rfl

@[simp] theorem add_imJ : (a + b).imJ = a.imJ + b.imJ := rfl

@[simp] theorem add_imK : (a + b).imK = a.imK + b.imK := rfl

@[simp] nonrec theorem add_im : (a + b).im = a.im + b.im := a.add_im b

@[simp, norm_cast]
theorem coe_add : ((x + y : R) : ℍ[R]) = x + y :=
  QuaternionAlgebra.coe_add x y

@[simp] theorem neg_re : (-a).re = -a.re := rfl

@[simp] theorem neg_imI : (-a).imI = -a.imI := rfl

@[simp] theorem neg_imJ : (-a).imJ = -a.imJ := rfl

@[simp] theorem neg_imK : (-a).imK = -a.imK := rfl

@[simp] nonrec theorem neg_im : (-a).im = -a.im := a.neg_im

@[simp, norm_cast]
theorem coe_neg : ((-x : R) : ℍ[R]) = -x :=
  QuaternionAlgebra.coe_neg x

@[simp] theorem sub_re : (a - b).re = a.re - b.re := rfl

@[simp] theorem sub_imI : (a - b).imI = a.imI - b.imI := rfl

@[simp] theorem sub_imJ : (a - b).imJ = a.imJ - b.imJ := rfl

@[simp] theorem sub_imK : (a - b).imK = a.imK - b.imK := rfl

@[simp] nonrec theorem sub_im : (a - b).im = a.im - b.im := a.sub_im b

@[simp, norm_cast]
theorem coe_sub : ((x - y : R) : ℍ[R]) = x - y :=
  QuaternionAlgebra.coe_sub x y

@[simp]
theorem mul_re : (a * b).re = a.re * b.re - a.imI * b.imI - a.imJ * b.imJ - a.imK * b.imK :=
  (QuaternionAlgebra.mul_re a b).trans <| by simp [one_mul, neg_mul, sub_eq_add_neg, neg_neg]

@[simp]
theorem mul_imI : (a * b).imI = a.re * b.imI + a.imI * b.re + a.imJ * b.imK - a.imK * b.imJ :=
  (QuaternionAlgebra.mul_imI a b).trans <| by ring

@[simp]
theorem mul_imJ : (a * b).imJ = a.re * b.imJ - a.imI * b.imK + a.imJ * b.re + a.imK * b.imI :=
  (QuaternionAlgebra.mul_imJ a b).trans <| by ring

@[simp]
theorem mul_imK : (a * b).imK = a.re * b.imK + a.imI * b.imJ - a.imJ * b.imI + a.imK * b.re :=
  (QuaternionAlgebra.mul_imK a b).trans <| by ring

@[simp, norm_cast]
theorem coe_mul : ((x * y : R) : ℍ[R]) = x * y := QuaternionAlgebra.coe_mul x y

@[norm_cast, simp]
theorem coe_pow (n : ℕ) : (↑(x ^ n) : ℍ[R]) = (x : ℍ[R]) ^ n :=
  QuaternionAlgebra.coe_pow x n

@[simp, norm_cast]
theorem natCast_re (n : ℕ) : (n : ℍ[R]).re = n := rfl

@[simp, norm_cast]
theorem natCast_imI (n : ℕ) : (n : ℍ[R]).imI = 0 := rfl

@[simp, norm_cast]
theorem natCast_imJ (n : ℕ) : (n : ℍ[R]).imJ = 0 := rfl

@[simp, norm_cast]
theorem natCast_imK (n : ℕ) : (n : ℍ[R]).imK = 0 := rfl

@[simp, norm_cast]
theorem natCast_im (n : ℕ) : (n : ℍ[R]).im = 0 := rfl

@[norm_cast]
theorem coe_natCast (n : ℕ) : ↑(n : R) = (n : ℍ[R]) := rfl

@[simp, norm_cast]
theorem intCast_re (z : ℤ) : (z : ℍ[R]).re = z := rfl

@[simp, norm_cast]
theorem intCast_imI (z : ℤ) : (z : ℍ[R]).imI = 0 := rfl

@[simp, norm_cast]
theorem intCast_imJ (z : ℤ) : (z : ℍ[R]).imJ = 0 := rfl

@[simp, norm_cast]
theorem intCast_imK (z : ℤ) : (z : ℍ[R]).imK = 0 := rfl

@[simp, norm_cast]
theorem intCast_im (z : ℤ) : (z : ℍ[R]).im = 0 := rfl

@[norm_cast]
theorem coe_intCast (z : ℤ) : ↑(z : R) = (z : ℍ[R]) := rfl

theorem coe_injective : Function.Injective (coe : R → ℍ[R]) :=
  QuaternionAlgebra.coe_injective

@[simp]
theorem coe_inj {x y : R} : (x : ℍ[R]) = y ↔ x = y :=
  coe_injective.eq_iff

@[simp]
theorem smul_re [SMul S R] (s : S) : (s • a).re = s • a.re :=
  rfl

@[simp] theorem smul_imI [SMul S R] (s : S) : (s • a).imI = s • a.imI := rfl

@[simp] theorem smul_imJ [SMul S R] (s : S) : (s • a).imJ = s • a.imJ := rfl

@[simp] theorem smul_imK [SMul S R] (s : S) : (s • a).imK = s • a.imK := rfl

@[simp]
nonrec theorem smul_im [SMulZeroClass S R] (s : S) : (s • a).im = s • a.im :=
  a.smul_im s

@[simp, norm_cast]
theorem coe_smul [SMulZeroClass S R] (s : S) (r : R) : (↑(s • r) : ℍ[R]) = s • (r : ℍ[R]) :=
  QuaternionAlgebra.coe_smul _ _

theorem coe_commutes : ↑r * a = a * r :=
  QuaternionAlgebra.coe_commutes r a

theorem coe_commute : Commute (↑r) a :=
  QuaternionAlgebra.coe_commute r a

theorem coe_mul_eq_smul : ↑r * a = r • a :=
  QuaternionAlgebra.coe_mul_eq_smul r a

theorem mul_coe_eq_smul : a * r = r • a :=
  QuaternionAlgebra.mul_coe_eq_smul r a

@[simp]
theorem algebraMap_def : ⇑(algebraMap R ℍ[R]) = coe :=
  rfl

theorem algebraMap_injective : (algebraMap R ℍ[R] : _ → _).Injective :=
  QuaternionAlgebra.algebraMap_injective

theorem smul_coe : x • (y : ℍ[R]) = ↑(x * y) :=
  QuaternionAlgebra.smul_coe x y

instance : Module.Finite R ℍ[R] := inferInstanceAs <| Module.Finite R ℍ[R,-1,0,-1]
instance : Module.Free R ℍ[R] := inferInstanceAs <| Module.Free R ℍ[R,-1,0,-1]

theorem rank_eq_four [StrongRankCondition R] : Module.rank R ℍ[R] = 4 :=
  QuaternionAlgebra.rank_eq_four _ _ _

theorem finrank_eq_four [StrongRankCondition R] : Module.finrank R ℍ[R] = 4 :=
  QuaternionAlgebra.finrank_eq_four _ _ _

@[target] theorem star_re : (star a).re = a.re := by
  sorry


@[target] theorem star_imI : (star a).imI = -a.imI := by sorry


@[target] theorem star_imJ : (star a).imJ = -a.imJ := by sorry


@[target] theorem star_imK : (star a).imK = -a.imK := by sorry


@[simp] theorem star_im : (star a).im = -a.im := a.im_star

nonrec theorem self_add_star' : a + star a = ↑(2 * a.re) := by
  simp [a.self_add_star', Quaternion.coe]

nonrec theorem self_add_star : a + star a = 2 * a.re := by
  simp [a.self_add_star, Quaternion.coe]

nonrec theorem star_add_self' : star a + a = ↑(2 * a.re) := by
  simp [a.star_add_self', Quaternion.coe]

nonrec theorem star_add_self : star a + a = 2 * a.re := by
  simp [a.star_add_self, Quaternion.coe]

nonrec theorem star_eq_two_re_sub : star a = ↑(2 * a.re) - a := by
  simp [a.star_eq_two_re_sub, Quaternion.coe]

@[simp, norm_cast]
theorem star_coe : star (x : ℍ[R]) = x :=
  QuaternionAlgebra.star_coe x

@[simp]
theorem im_star : star a.im = -a.im := by ext <;> simp

@[simp]
theorem star_smul [Monoid S] [DistribMulAction S R] (s : S) (a : ℍ[R]) :
    star (s • a) = s • star a := QuaternionAlgebra.star_smul' s a

theorem eq_re_of_eq_coe {a : ℍ[R]} {x : R} (h : a = x) : a = a.re :=
  QuaternionAlgebra.eq_re_of_eq_coe h

theorem eq_re_iff_mem_range_coe {a : ℍ[R]} : a = a.re ↔ a ∈ Set.range (coe : R → ℍ[R]) :=
  QuaternionAlgebra.eq_re_iff_mem_range_coe

section CharZero

variable [NoZeroDivisors R] [CharZero R]

@[simp]
theorem star_eq_self {a : ℍ[R]} : star a = a ↔ a = a.re :=
  QuaternionAlgebra.star_eq_self

@[simp]
theorem star_eq_neg {a : ℍ[R]} : star a = -a ↔ a.re = 0 :=
  QuaternionAlgebra.star_eq_neg

end CharZero

nonrec theorem star_mul_eq_coe : star a * a = (star a * a).re :=
  a.star_mul_eq_coe

nonrec theorem mul_star_eq_coe : a * star a = (a * star a).re :=
  a.mul_star_eq_coe

open MulOpposite

/-- Quaternion conjugate as an `AlgEquiv` to the opposite ring. -/
def starAe : ℍ[R] ≃ₐ[R] ℍ[R]ᵐᵒᵖ :=
  QuaternionAlgebra.starAe

@[simp]
theorem coe_starAe : ⇑(starAe : ℍ[R] ≃ₐ[R] ℍ[R]ᵐᵒᵖ) = op ∘ star :=
  rfl

/-- Square of the norm. -/
/-- Square of the norm. -/
def normSq : ℍ[R] →*₀ R where
  toFun a := (a * star a).re
  map_zero' := by sorry


@[target] theorem normSq_def : normSq a = (a * star a).re := by sorry


theorem normSq_def' : normSq a = a.1 ^ 2 + a.2 ^ 2 + a.3 ^ 2 + a.4 ^ 2 := by
  simp only [normSq_def, sq, mul_neg, sub_neg_eq_add, mul_re, star_re, star_imI, star_imJ,
    star_imK]

theorem normSq_coe : normSq (x : ℍ[R]) = x ^ 2 := by
  rw [normSq_def, star_coe, ← coe_mul, coe_re, sq]

@[simp]
theorem normSq_star : normSq (star a) = normSq a := by simp [normSq_def']

@[target] theorem normSq_natCast (n : ℕ) : normSq (n : ℍ[R]) = (n : R) ^ 2 := by
  sorry


@[target] theorem normSq_intCast (z : ℤ) : normSq (z : ℍ[R]) = (z : R) ^ 2 := by
  sorry


@[target] theorem normSq_neg : normSq (-a) = normSq a := by sorry


theorem self_mul_star : a * star a = normSq a := by rw [mul_star_eq_coe, normSq_def]

@[target] theorem star_mul_self (U : unitary R) : star U * U = 1 := by sorry


@[target] theorem im_sq : a.im ^ 2 = -normSq a.im := by
  sorry


theorem coe_normSq_add : normSq (a + b) = normSq a + a * star b + b * star a + normSq b := by
  simp only [star_add, ← self_mul_star, mul_add, add_mul, add_assoc, add_left_comm]

theorem normSq_smul (r : R) (q : ℍ[R]) : normSq (r • q) = r ^ 2 * normSq q := by
  simp only [normSq_def', smul_re, smul_imI, smul_imJ, smul_imK, mul_pow, mul_add, smul_eq_mul]

@[target] theorem normSq_add (a b : ℍ[R]) : normSq (a + b) = normSq a + normSq b + 2 * (a * star b).re :=
  calc
    normSq (a + b) = normSq a + (a * star b).re + ((b * star a).re + normSq b) := by
      sorry


end Quaternion

namespace Quaternion

variable {R : Type*}

section LinearOrderedCommRing

variable [LinearOrderedCommRing R] {a : ℍ[R]}

@[target] theorem normSq_eq_zero : normSq a = 0 ↔ a = 0 := by
  sorry


@[target] theorem normSq_ne_zero : normSq a ≠ 0 ↔ a ≠ 0 := by sorry


@[target] theorem normSq_nonneg : 0 ≤ normSq a := by
  sorry


@[target] theorem normSq_le_zero : normSq a ≤ 0 ↔ a = 0 := by sorry


instance instNontrivial : Nontrivial ℍ[R] where
  exists_pair_ne := ⟨0, 1, mt (congr_arg QuaternionAlgebra.re) zero_ne_one⟩

instance : NoZeroDivisors ℍ[R] where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} hab :=
    have : normSq a * normSq b = 0 := by rwa [← map_mul, normSq_eq_zero]
    (eq_zero_or_eq_zero_of_mul_eq_zero this).imp normSq_eq_zero.1 normSq_eq_zero.1

instance : IsDomain ℍ[R] := NoZeroDivisors.to_isDomain _

theorem sq_eq_normSq : a ^ 2 = normSq a ↔ a = a.re := by
  rw [← star_eq_self, ← star_mul_self, sq, mul_eq_mul_right_iff, eq_comm]
  exact or_iff_left_of_imp fun ha ↦ ha.symm ▸ star_zero _

@[target] theorem sq_eq_neg_normSq : a ^ 2 = -normSq a ↔ a.re = 0 := by
  sorry


end LinearOrderedCommRing

section Field

variable [LinearOrderedField R] (a b : ℍ[R])

@[simps (config := .lemmasOnly)]
instance instInv : Inv ℍ[R] :=
  ⟨fun a => (normSq a)⁻¹ • star a⟩

instance instGroupWithZero : GroupWithZero ℍ[R] :=
  { Quaternion.instNontrivial with
    inv := Inv.inv
    inv_zero := by rw [instInv_inv, star_zero, smul_zero]
    mul_inv_cancel := fun a ha => by
      rw [instInv_inv, Algebra.mul_smul_comm (normSq a)⁻¹ a (star a), self_mul_star, smul_coe,
        inv_mul_cancel₀ (normSq_ne_zero.2 ha), coe_one] }

@[target] theorem coe_inv (r : R) : ↑r⁻¹ = ((↑r)⁻¹ : A) := by sorry


@[target] theorem coe_div (r s : R) : ↑(r / s) = (↑r / ↑s : A) := by sorry


@[target] theorem coe_zpow (r : R) (z : ℤ) : ↑(r ^ z) = (r : A) ^ z := by sorry


instance instNNRatCast : NNRatCast ℍ[R] where nnratCast q := (q : R)
instance instRatCast : RatCast ℍ[R] where ratCast q := (q : R)

@[target] lemma re_nnratCast (q : ℚ≥0) : (q : ℍ[R]).re = q := by sorry

@[simp, norm_cast] lemma im_nnratCast (q : ℚ≥0) : (q : ℍ[R]).im = 0 := rfl
@[target] lemma imI_nnratCast (q : ℚ≥0) : (q : ℍ[R]).imI = 0 := by sorry

@[target] lemma imJ_nnratCast (q : ℚ≥0) : (q : ℍ[R]).imJ = 0 := by sorry

@[target] lemma imK_nnratCast (q : ℚ≥0) : (q : ℍ[R]).imK = 0 := by sorry

@[target] lemma ratCast_re (q : ℚ) : (q : ℍ[R]).re = q := by sorry

@[target] lemma ratCast_im (q : ℚ) : (q : ℍ[R]).im = 0 := by sorry

@[simp, norm_cast] lemma ratCast_imI (q : ℚ) : (q : ℍ[R]).imI = 0 := rfl
@[target] lemma ratCast_imJ (q : ℚ) : (q : ℍ[R]).imJ = 0 := by sorry

@[target] lemma ratCast_imK (q : ℚ) : (q : ℍ[R]).imK = 0 := by sorry


@[target] lemma coe_nnratCast (q : ℚ≥0) : ↑(q : R) = (q : ℍ[R]) := by sorry


@[target] theorem coe_ratCast (q : ℚ) : ↑(q : R) = (q : A) := by sorry


instance instDivisionRing : DivisionRing ℍ[R] where
  __ := Quaternion.instRing
  __ := Quaternion.instGroupWithZero
  nnqsmul := (· • ·)
  qsmul := (· • ·)
  nnratCast_def _ := by rw [← coe_nnratCast, NNRat.cast_def, coe_div, coe_natCast, coe_natCast]
  ratCast_def _ := by rw [← coe_ratCast, Rat.cast_def, coe_div, coe_intCast, coe_natCast]
  nnqsmul_def _ _ := by rw [← coe_nnratCast, coe_mul_eq_smul]; ext <;> exact NNRat.smul_def ..
  qsmul_def _ _ := by rw [← coe_ratCast, coe_mul_eq_smul]; ext <;> exact Rat.smul_def ..

@[target] theorem normSq_inv : normSq a⁻¹ = (normSq a)⁻¹ := by sorry


@[target] theorem normSq_div : normSq (a / b) = normSq a / normSq b := by sorry


@[target] theorem normSq_zpow (z : ℤ) : normSq (a ^ z) = normSq a ^ z := by sorry


@[norm_cast]
theorem normSq_ratCast (q : ℚ) : normSq (q : ℍ[R]) = (q : ℍ[R]) ^ 2 := by
  rw [← coe_ratCast, normSq_coe, coe_pow]

end Field

end Quaternion

namespace Cardinal

open Quaternion

section QuaternionAlgebra

variable {R : Type*} (c₁ c₂ c₃ : R)

private theorem pow_four [Infinite R] : #R ^ 4 = #R :=
  power_nat_eq (aleph0_le_mk R) <| by decide

/-- The cardinality of a quaternion algebra, as a type. -/
/-- The cardinality of a quaternion algebra, as a type. -/
@[target] theorem mk_quaternionAlgebra : #(ℍ[R,c₁,c₂,c₃]) = #R ^ 4 := by
  sorry


@[target] theorem mk_quaternionAlgebra_of_infinite [Infinite R] : #(ℍ[R,c₁,c₂,c₃]) = #R := by
  sorry


/-- The cardinality of a quaternion algebra, as a set. -/
theorem mk_univ_quaternionAlgebra : #(Set.univ : Set ℍ[R,c₁,c₂,c₃]) = #R ^ 4 := by
  rw [mk_univ, mk_quaternionAlgebra]

theorem mk_univ_quaternionAlgebra_of_infinite [Infinite R] :
    #(Set.univ : Set ℍ[R,c₁,c₂,c₃]) = #R := by rw [mk_univ_quaternionAlgebra, pow_four]

/-- Show the quaternion ⟨w, x, y, z⟩ as a string "{ re := w, imI := x, imJ := y, imK := z }".

For the typical case of quaternions over ℝ, each component will show as a Cauchy sequence due to
the way Real numbers are represented.
-/
instance [Repr R] {a b c : R} : Repr ℍ[R, a, b, c] where
  reprPrec q _ :=
    s!"\{ re := {repr q.re}, imI := {repr q.imI}, imJ := {repr q.imJ}, imK := {repr q.imK} }"

end QuaternionAlgebra

section Quaternion

variable (R : Type*) [Zero R] [One R] [Neg R]

/-- The cardinality of the quaternions, as a type. -/
/-- The cardinality of the quaternions, as a type. -/
@[target] theorem mk_quaternion : #(ℍ[R]) = #R ^ 4 := by sorry


@[target] theorem mk_quaternion_of_infinite [Infinite R] : #(ℍ[R]) = #R := by sorry


/-- The cardinality of the quaternions, as a set. -/
/-- The cardinality of the quaternions, as a set. -/
@[target] theorem mk_univ_quaternion : #(Set.univ : Set ℍ[R]) = #R ^ 4 := by sorry


@[target] theorem mk_univ_quaternion_of_infinite [Infinite R] : #(Set.univ : Set ℍ[R]) = #R := by sorry


end Quaternion

end Cardinal
