import VerifiedAgora.tagger
/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Anne Baanen
-/
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Towers of algebras

In this file we prove basic facts about towers of algebra.

An algebra tower A/S/R is expressed by having instances of `Algebra A S`,
`Algebra R S`, `Algebra R A` and `IsScalarTower R S A`, the later asserting the
compatibility condition `(r • s) • a = r • (s • a)`.

An important definition is `toAlgHom R S A`, the canonical `R`-algebra homomorphism `S →ₐ[R] A`.

-/


open Pointwise

universe u v w u₁ v₁

variable (R : Type u) (S : Type v) (A : Type w) (B : Type u₁) (M : Type v₁)

namespace Algebra

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
variable [AddCommMonoid M] [Module R M] [Module A M] [Module B M]
variable [IsScalarTower R A M] [IsScalarTower R B M] [SMulCommClass A B M]
variable {A}


/-- The `R`-algebra morphism `A → End (M)` corresponding to the representation of the algebra `A`
on the `B`-module `M`.

This is a stronger version of `DistribMulAction.toLinearMap`, and could also have been
called `Algebra.toModuleEnd`.

The typeclasses correspond to the situation where the types act on each other as
```
R ----→ B
| ⟍     |
|   ⟍   |
↓     ↘ ↓
A ----→ M
```
where the diagram commutes, the action by `R` commutes with everything, and the action by `A` and
`B` on `M` commute.

Typically this is most useful with `B = R` as `Algebra.lsmul R R A : A →ₐ[R] Module.End R M`.
However this can be used to get the fact that left-multiplication by `A` is right `A`-linear, and
vice versa, as
```lean
example : A →ₐ[R] Module.End Aᵐᵒᵖ A := Algebra.lsmul R Aᵐᵒᵖ A
example : Aᵐᵒᵖ →ₐ[R] Module.End A A := Algebra.lsmul R A A
```
respectively; though `LinearMap.mulLeft` and `LinearMap.mulRight` can also be used here.
-/
/-- The `R`-algebra morphism `A → End (M)` corresponding to the representation of the algebra `A`
on the `B`-module `M`.

This is a stronger version of `DistribMulAction.toLinearMap`, and could also have been
called `Algebra.toModuleEnd`.

The typeclasses correspond to the situation where the types act on each other as
```
R ----→ B
| ⟍     |
|   ⟍   |
↓     ↘ ↓
A ----→ M
```
where the diagram commutes, the action by `R` commutes with everything, and the action by `A` and
`B` on `M` commute.

Typically this is most useful with `B = R` as `Algebra.lsmul R R A : A →ₐ[R] Module.End R M`.
However this can be used to get the fact that left-multiplication by `A` is right `A`-linear, and
vice versa, as
```lean
example : A →ₐ[R] Module.End Aᵐᵒᵖ A := by sorry


@[target] theorem lsmul_coe (a : A) : (lsmul R B M a : M → M) = (a • ·) := by sorry


end Algebra

namespace IsScalarTower

section Module

variable [CommSemiring R] [Semiring A] [Algebra R A]
variable [MulAction A M]
variable {R} {M}

@[target] theorem algebraMap_smul [SMul R M] [IsScalarTower R A M] (r : R) (x : M) :
    algebraMap R A r • x = r • x := by
  sorry


variable {A} in
variable {A} in
@[target] theorem of_algebraMap_smul [SMul R M] (h : ∀ (r : R) (x : M), algebraMap R A r • x = r • x) :
    IsScalarTower R A M where
  smul_assoc r a x := by sorry


variable (R M) in
variable (R M) in
@[target] theorem of_compHom : letI := by sorry


end Module

section Semiring

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]
variable [Algebra R S] [Algebra S A] [Algebra S B]
variable {R S A}

@[target] theorem of_algebraMap_eq [Algebra R A]
    (h : ∀ x, algebraMap R A x = algebraMap S A (algebraMap R S x)) : IsScalarTower R S A :=
  ⟨fun x y z => by sorry


/-- See note [partially-applied ext lemmas]. -/
theorem of_algebraMap_eq' [Algebra R A]
    (h : algebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A :=
  of_algebraMap_eq <| RingHom.ext_iff.1 h

variable (R S A)
variable [Algebra R A] [Algebra R B]
variable [IsScalarTower R S A] [IsScalarTower R S B]

@[target] theorem algebraMap_eq : algebraMap R A = (algebraMap S A).comp (algebraMap R S) :=
  RingHom.ext fun x => by
    sorry


@[target] theorem algebraMap_apply (x : R) : algebraMap R A x = algebraMap S A (algebraMap R S x) := by
  sorry


@[ext]
theorem Algebra.ext {S : Type u} {A : Type v} [CommSemiring S] [Semiring A] (h1 h2 : Algebra S A)
    (h : ∀ (r : S) (x : A), (by have I := h1; exact r • x) = r • x) : h1 = h2 :=
  Algebra.algebra_ext _ _ fun r => by
    simpa only [@Algebra.smul_def _ _ _ _ h1, @Algebra.smul_def _ _ _ _ h2, mul_one] using h r 1

/-- In a tower, the canonical map from the middle element to the top element is an
algebra homomorphism over the bottom element. -/
/-- In a tower, the canonical map from the middle element to the top element is an
algebra homomorphism over the bottom element. -/
def toAlgHom : S →ₐ[R] A := by sorry


@[target] theorem toAlgHom_apply (y : S) : toAlgHom R S A y = algebraMap S A y := by sorry


@[target] theorem coe_toAlgHom : ↑(toAlgHom R S A) = algebraMap S A := by sorry


@[simp]
theorem coe_toAlgHom' : (toAlgHom R S A : S → A) = algebraMap S A := rfl

variable {R S A B}

@[simp]
theorem _root_.AlgHom.map_algebraMap (f : A →ₐ[S] B) (r : R) :
    f (algebraMap R A r) = algebraMap R B r := by
  rw [algebraMap_apply R S A r, f.commutes, ← algebraMap_apply R S B]

variable (R)

@[simp]
theorem _root_.AlgHom.comp_algebraMap_of_tower (f : A →ₐ[S] B) :
    (f : A →+* B).comp (algebraMap R A) = algebraMap R B :=
  RingHom.ext (AlgHom.map_algebraMap f)

-- conflicts with IsScalarTower.Subalgebra
instance (priority := 999) subsemiring (U : Subsemiring S) : IsScalarTower U S A :=
  of_algebraMap_eq fun _x => rfl

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/12096): removed @[nolint instance_priority], linter not ported yet
instance (priority := 999) of_algHom {R A B : Type*} [CommSemiring R] [CommSemiring A]
    [CommSemiring B] [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) :
    @IsScalarTower R A B _ f.toRingHom.toAlgebra.toSMul _ :=
  letI := (f : A →+* B).toAlgebra
  of_algebraMap_eq fun x => (f.commutes x).symm

end Semiring

end IsScalarTower

section Homs

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]
variable [Algebra R S] [Algebra S A] [Algebra S B]
variable [Algebra R A] [Algebra R B]
variable [IsScalarTower R S A] [IsScalarTower R S B]
variable {A S B}

open IsScalarTower

namespace AlgHom

/-- R ⟶ S induces S-Alg ⥤ R-Alg -/
/-- R ⟶ S induces S-Alg ⥤ R-Alg -/
def restrictScalars (f : A →ₐ[S] B) : A →ₐ[R] B :=
  { (f : A →+* B) with
    commutes' := fun r => by
      sorry


@[target] theorem restrictScalars_apply (f : A →ₐ[S] B) (x : A) : f.restrictScalars R x = f x := by sorry


@[target] theorem coe_restrictScalars (f : A →ₐ[S] B) : (f.restrictScalars R : A →+* B) = f := by sorry


@[simp]
theorem coe_restrictScalars' (f : A →ₐ[S] B) : (restrictScalars R f : A → B) = f := rfl

@[target] theorem restrictScalars_injective :
    Function.Injective (restrictScalars R : (A →ₐ[S] B) → A →ₐ[R] B) := by sorry


end AlgHom

namespace AlgEquiv

/-- R ⟶ S induces S-Alg ⥤ R-Alg -/
def restrictScalars (f : A ≃ₐ[S] B) : A ≃ₐ[R] B :=
  { (f : A ≃+* B) with
    commutes' := fun r => by
      rw [algebraMap_apply R S A, algebraMap_apply R S B]
      exact f.commutes (algebraMap R S r) }

theorem restrictScalars_apply (f : A ≃ₐ[S] B) (x : A) : f.restrictScalars R x = f x := rfl

@[simp]
theorem coe_restrictScalars (f : A ≃ₐ[S] B) : (f.restrictScalars R : A ≃+* B) = f := rfl

@[simp]
theorem coe_restrictScalars' (f : A ≃ₐ[S] B) : (restrictScalars R f : A → B) = f := rfl

theorem restrictScalars_injective :
    Function.Injective (restrictScalars R : (A ≃ₐ[S] B) → A ≃ₐ[R] B) := fun _ _ h =>
  AlgEquiv.ext (AlgEquiv.congr_fun h :)

end AlgEquiv

end Homs

namespace Submodule

variable {M}
variable [CommSemiring R] [Semiring A] [Algebra R A] [AddCommMonoid M]
variable [Module R M] [Module A M] [IsScalarTower R A M]

/-- If `A` is an `R`-algebra such that the induced morphism `R →+* A` is surjective, then the
`R`-module generated by a set `X` equals the `A`-module generated by `X`. -/
/-- If `A` is an `R`-algebra such that the induced morphism `R →+* A` is surjective, then the
`R`-module generated by a set `X` equals the `A`-module generated by `X`. -/
@[target] theorem restrictScalars_span (hsur : Function.Surjective (algebraMap R A)) (X : Set M) :
    restrictScalars R (span A X) = span R X := by
  sorry


@[target] theorem coe_span_eq_span_of_surjective (h : Function.Surjective (algebraMap R A)) (s : Set M) :
    (Submodule.span A s : Set M) = Submodule.span R s := by sorry


end Submodule

section Semiring

variable {R S A}

namespace Submodule

section Module

variable [Semiring R] [Semiring S] [AddCommMonoid A]
variable [Module R S] [Module S A] [Module R A] [IsScalarTower R S A]

open IsScalarTower

@[target] theorem smul_mem_span_smul_of_mem {s : Set S} {t : Set A} {k : S} (hks : k ∈ span R s) {x : A}
    (hx : x ∈ t) : k • x ∈ span R (s • t) :=
  span_induction (fun _ hc => subset_span <| Set.smul_mem_smul hc hx)
    (by sorry


@[target] theorem span_smul_of_span_eq_top {s : Set S} (hs : span R s = ⊤) (t : Set A) :
    span R (s • t) = (span S t).restrictScalars R :=
  le_antisymm
    (span_le.2 fun _x ⟨p, _hps, _q, hqt, hpqx⟩ ↦ hpqx ▸ (span S t).smul_mem p (subset_span hqt))
    fun _ hp ↦ closure_induction (hx := hp) (zero_mem _) (fun _ _ _ _ ↦ add_mem) fun s0 y hy ↦ by
      sorry

@[target] theorem smul_mem_span_smul {s : Set S} (hs : span R s = ⊤) {t : Set A} {k : S} {x : A}
    (hx : x ∈ span R t) : k • x ∈ span R (s • t) := by
  sorry


theorem smul_mem_span_smul {s : Set S} (hs : span R s = ⊤) {t : Set A} {k : S} {x : A}
    (hx : x ∈ span R t) : k • x ∈ span R (s • t) := by
  rw [span_smul_of_span_eq_top hs]
  exact (span S t).smul_mem k (span_le_restrictScalars R S t hx)

end Module

section Algebra

variable [CommSemiring R] [Semiring S] [AddCommMonoid A]
variable [Algebra R S] [Module S A] [Module R A] [IsScalarTower R S A]

/-- A variant of `Submodule.span_image` for `algebraMap`. -/
/-- A variant of `Submodule.span_image` for `algebraMap`. -/
@[target] theorem span_algebraMap_image (a : Set R) :
    Submodule.span R (algebraMap R S '' a) = (Submodule.span R a).map (Algebra.linearMap R S) := by sorry


@[target] theorem span_algebraMap_image_of_tower {S T : Type*} [CommSemiring S] [Semiring T] [Module R S]
    [Algebra R T] [Algebra S T] [IsScalarTower R S T] (a : Set S) :
    Submodule.span R (algebraMap S T '' a) =
      (Submodule.span R a).map ((Algebra.linearMap S T).restrictScalars R) := by sorry


@[target] theorem map_mem_span_algebraMap_image {S T : Type*} [CommSemiring S] [Semiring T] [Algebra R S]
    [Algebra R T] [Algebra S T] [IsScalarTower R S T] (x : S) (a : Set S)
    (hx : x ∈ Submodule.span R a) : algebraMap S T x ∈ Submodule.span R (algebraMap S T '' a) := by
  sorry


end Algebra

end Submodule

end Semiring

section Ring

namespace Algebra

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
variable [AddCommGroup M] [Module R M] [Module A M] [Module B M]
variable [IsScalarTower R A M] [IsScalarTower R B M] [SMulCommClass A B M]

@[target] theorem lsmul_injective [NoZeroSMulDivisors A M] {x : A} (hx : x ≠ 0) :
    Function.Injective (lsmul R B M x) := by sorry


end Algebra

end Ring
