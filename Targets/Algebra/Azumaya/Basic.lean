import VerifiedAgora.tagger
/-
Copyright (c) 2025 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Jujian Zhang
-/
import Mathlib.Algebra.Azumaya.Defs
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.GroupTheory.GroupAction.Hom

/-!
# Basic properties of Azumaya algebras

In this file we prove basic facts about Azumaya algebras such as `R` is an Azumaya algebra
over itself where `R` is a commutative ring.

## Main Results

- `IsAzumaya.id`: `R` is an Azumaya algebra over itself.

- `IsAzumaya.ofAlgEquiv`: If `A` is an Azumaya algebra over `R` and `A` is isomorphic to `B`
  as an `R`-algebra, then `B` is an Azumaya algebra over `R`.

## Tags
Noncommutative algebra, Azumaya algebra, Brauer Group

-/

open scoped TensorProduct

open MulOpposite

namespace IsAzumaya

variable (R A B : Type*) [CommSemiring R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]

@[target]
lemma AlgHom.mulLeftRight_bij [h : IsAzumaya R A] :
    Function.Bijective (AlgHom.mulLeftRight R A) := sorry

@[target]
lemma coe_tensorEquivEnd : tensorEquivEnd R = AlgHom.mulLeftRight R R := by sorry

instance id : IsAzumaya R R where
  bij := by rw [← coe_tensorEquivEnd]; exact tensorEquivEnd R |>.bijective

/--
The following diagram commutes:
```
          e ⊗ eᵒᵖ
A ⊗ Aᵐᵒᵖ  ------------> B ⊗ Bᵐᵒᵖ
  |                        |
  |                        |
  | mulLeftRight R A       | mulLeftRight R B
  |                        |
  V                        V
End R A   ------------> End R B
          e.conj
```
-/
@[target]
lemma mulLeftRight_comp_congr (e : A ≃ₐ[R] B) :
    (AlgHom.mulLeftRight R B).comp (Algebra.TensorProduct.congr e e.op).toAlgHom =
    (e.toLinearEquiv.algConj).toAlgHom.comp (AlgHom.mulLeftRight R A) := by sorry

@[target]
theorem of_AlgEquiv (e : A ≃ₐ[R] B) [IsAzumaya R A] : IsAzumaya R B :=
  sorry

end IsAzumaya
