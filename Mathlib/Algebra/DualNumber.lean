import VerifiedAgora.tagger
/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.TrivSqZeroExt

/-!
# Dual numbers

The dual numbers over `R` are of the form `a + bε`, where `a` and `b` are typically elements of a
commutative ring `R`, and `ε` is a symbol satisfying `ε^2 = 0` that commutes with every other
element. They are a special case of `TrivSqZeroExt R M` with `M = R`.

## Notation

In the `DualNumber` locale:

* `R[ε]` is a shorthand for `DualNumber R`
* `ε` is a shorthand for `DualNumber.eps`

## Main definitions

* `DualNumber`
* `DualNumber.eps`
* `DualNumber.lift`

## Implementation notes

Rather than duplicating the API of `TrivSqZeroExt`, this file reuses the functions there.

## References

* https://en.wikipedia.org/wiki/Dual_number
-/


variable {R A B : Type*}

/-- The type of dual numbers, numbers of the form $a + bε$ where $ε^2 = 0$.
`R[ε]` is notation for `DualNumber R`. -/
/-- The type of dual numbers, numbers of the form $a + bε$ where $ε^2 = 0$.
`R[ε]` is notation for `DualNumber R`. -/
abbrev DualNumber (R : Type*) : Type _ := by sorry


/-- The unit element $ε$ that squares to zero, with notation `ε`. -/
def DualNumber.eps [Zero R] [One R] : DualNumber R :=
  TrivSqZeroExt.inr 1

@[inherit_doc]
scoped[DualNumber] notation "ε" => DualNumber.eps

@[inherit_doc]
scoped[DualNumber] postfix:1024 "[ε]" => DualNumber

open DualNumber

namespace DualNumber

open TrivSqZeroExt

@[target] theorem fst_eps [Zero R] [One R] : fst ε = (0 : R) := by sorry


@[simp]
theorem snd_eps [Zero R] [One R] : snd ε = (1 : R) :=
  snd_inr _ _

/-- A version of `TrivSqZeroExt.snd_mul` with `*` instead of `•`. -/
/-- A version of `TrivSqZeroExt.snd_mul` with `*` instead of `•`. -/
@[target] theorem snd_mul [Semiring R] (x y : R[ε]) : snd (x * y) = fst x * snd y + snd x * fst y := by sorry


@[target] theorem eps_mul_eps [Semiring R] : (ε * ε : R[ε]) = 0 := by sorry


@[target] theorem inv_eps [DivisionRing R] : (ε : R[ε])⁻¹ = 0 := by sorry


@[target] theorem inr_eq_smul_eps [MulZeroOneClass R] (r : R) : inr r = (r • ε : R[ε]) := by sorry


/-- `ε` commutes with every element of the algebra. -/
/-- `ε` commutes with every element of the algebra. -/
@[target] theorem commute_eps_left [Semiring R] (x : DualNumber R) : Commute ε x := by
  sorry


/-- `ε` commutes with every element of the algebra. -/
/-- `ε` commutes with every element of the algebra. -/
@[target] theorem commute_eps_right [Semiring R] (x : DualNumber R) : Commute x ε := by sorry


variable {A : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

/-- For two `R`-algebra morphisms out of `A[ε]` to agree, it suffices for them to agree on the
elements of `A` and the `A`-multiples of `ε`. -/
@[ext 1100]
nonrec theorem algHom_ext' ⦃f g : A[ε] →ₐ[R] B⦄
    (hinl : f.comp (inlAlgHom _ _ _) = g.comp (inlAlgHom _ _ _))
    (hinr : f.toLinearMap ∘ₗ (LinearMap.toSpanSingleton A A[ε] ε).restrictScalars R =
        g.toLinearMap ∘ₗ (LinearMap.toSpanSingleton A A[ε] ε).restrictScalars R) :
      f = g :=
  algHom_ext' hinl (by
    ext a
    show f (inr a) = g (inr a)
    simpa only [inr_eq_smul_eps] using DFunLike.congr_fun hinr a)

/-- For two `R`-algebra morphisms out of `R[ε]` to agree, it suffices for them to agree on `ε`. -/
@[ext 1200]
nonrec theorem algHom_ext ⦃f g : R[ε] →ₐ[R] A⦄ (hε : f ε = g ε) : f = g := by
  ext
  dsimp
  simp only [one_smul, hε]

/-- A universal property of the dual numbers, providing a unique `A[ε] →ₐ[R] B` for every map
`f : A →ₐ[R] B` and a choice of element `e : B` which squares to `0` and commutes with the range of
`f`.

This isomorphism is named to match the similar `Complex.lift`.
Note that when `f : R →ₐ[R] B := Algebra.ofId R B`, the commutativity assumption is automatic, and
we are free to choose any element `e : B`. -/
/-- Equivalence between maps `α → M` and monoid homomorphisms `FreeMonoid α →* M`. -/
@[to_additive "Equivalence between maps `α → A` and additive monoid homomorphisms
`FreeAddMonoid α →+ A`."]
def lift : (α → M) ≃ (FreeMonoid α →* M) where
  toFun f :=
  { toFun := fun l ↦ prodAux ((toList l).map f)
    map_one' := rfl
    map_mul' := fun _ _ ↦ by sorry


@[target] theorem lift_apply_apply (fe : {_fe : (A →ₐ[R] B) × B // _}) (a : A[ε]) :
    lift fe a = fe.val.1 a.fst + fe.val.1 a.snd * fe.val.2 := by sorry


@[target] theorem coe_lift_symm_apply (F : A[ε] →ₐ[R] B) :
    (lift.symm F).val = (F.comp (inlAlgHom _ _ _), F ε) := by sorry

/-- When applied to `inl`, `DualNumber.lift` applies the map `f : A →ₐ[R] B`. -/
set_option linter.unusedVariables false in
/-- When applied to `inl`, `DualNumber.lift` applies the map `f : A →ₐ[R] B`. -/
@[target] theorem lift_apply_inl (fe : {fe : (A →ₐ[R] B) × B // _}) (a : A) :
    lift fe (inl a : A[ε]) = fe.val.1 a := by
  sorry

/-- Scaling on the left is sent by `DualNumber.lift` to multiplication on the left -/
@[simp] theorem lift_smul (fe : {fe : (A →ₐ[R] B) × B // _}) (a : A) (ad : A[ε]) :
    lift fe (a • ad) = fe.val.1 a * lift fe ad := by
  rw [← inl_mul_eq_smul, map_mul, lift_apply_inl]

#adaptation_note /-- https://github.com/leanprover/lean4/pull/5338
The new unused variable linter flags `{fe : (A →ₐ[R] B) × B // _}`. -/
set_option linter.unusedVariables false in
/-- Scaling on the right is sent by `DualNumber.lift` to multiplication on the right -/
set_option linter.unusedVariables false in
/-- Scaling on the right is sent by `DualNumber.lift` to multiplication on the right -/
@[target] theorem lift_op_smul (fe : {fe : (A →ₐ[R] B) × B // _}) (a : A) (ad : A[ε]) :
    lift fe (MulOpposite.op a • ad) = lift fe ad * fe.val.1 a := by
  sorry


/-- When applied to `ε`, `DualNumber.lift` produces the element of `B` that squares to 0. -/
/-- When applied to `ε`, `DualNumber.lift` produces the element of `B` that squares to 0. -/
@[target] theorem lift_apply_eps
    (fe : {fe : (A →ₐ[R] B) × B // fe.2 * fe.2 = 0 ∧ ∀ a, Commute fe.2 (fe.1 a)}) :
    lift fe (ε : A[ε]) = fe.val.2 := by
  sorry


/-- Lifting `DualNumber.eps` itself gives the identity. -/
/-- Lifting `DualNumber.eps` itself gives the identity. -/
@[target] theorem lift_inlAlgHom_eps :
    lift ⟨(inlAlgHom _ _ _, ε), eps_mul_eps, fun _ => commute_eps_left _⟩ = AlgHom.id R A[ε] := by sorry


/-- Show DualNumber with values x and y as an "x + y*ε" string -/
instance instRepr [Repr R] : Repr (DualNumber R) where
  reprPrec f p :=
    (if p > 65 then (Std.Format.bracket "(" · ")") else (·)) <|
      reprPrec f.fst 65 ++ " + " ++ reprPrec f.snd 70 ++ "*ε"

end DualNumber
