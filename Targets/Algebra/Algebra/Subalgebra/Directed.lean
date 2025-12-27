import VerifiedAgora.tagger
/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Data.Set.UnionLift

/-!
# Subalgebras and directed Unions of sets

## Main results

 * `Subalgebra.coe_iSup_of_directed`: a directed supremum consists of the union of the algebras
 * `Subalgebra.iSupLift`: define an algebra homomorphism on a directed supremum of subalgebras by
   defining it on each subalgebra, and proving that it agrees on the intersection of subalgebras.
-/

namespace Subalgebra

open Algebra

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
variable (S : Subalgebra R A)

variable {ι : Type*} [Nonempty ι] {K : ι → Subalgebra R A}

@[target]
theorem coe_iSup_of_directed (dir : Directed (· ≤ ·) K) : ↑(iSup K) = ⋃ i, (K i : Set A) :=
  sorry

variable (K)

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11215): TODO: turn `hT` into an assumption `T ≤ iSup K`.
-- That's what `Set.iUnionLift` needs
-- Porting note: the proofs of `map_{zero,one,add,mul}` got a bit uglier, probably unification trbls
/-- Define an algebra homomorphism on a directed supremum of subalgebras by defining
it on each subalgebra, and proving that it agrees on the intersection of subalgebras. -/
noncomputable def iSupLift (dir : Directed (· ≤ ·) K) (f : ∀ i, K i →ₐ[R] B)
    (hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (inclusion h))
    (T : Subalgebra R A) (hT : T = iSup K): ↥T →ₐ[R] B :=
  { toFun := Set.iUnionLift (fun i => ↑(K i)) (fun i x => f i x)
        (fun i j x hxi hxj => by
          let ⟨k, hik, hjk⟩ := dir i j
          dsimp
          rw [hf i k hik, hf j k hjk]
          rfl)
        (T : Set A) (by rw [hT, coe_iSup_of_directed dir])
    map_one' := by apply Set.iUnionLift_const _ (fun _ => 1) <;> simp
    map_zero' := by dsimp; apply Set.iUnionLift_const _ (fun _ => 0) <;> simp
    map_mul' := by
      subst hT; dsimp
      apply Set.iUnionLift_binary (coe_iSup_of_directed dir) dir _ (fun _ => (· * ·))
      all_goals simp
    map_add' := by
      subst hT; dsimp
      apply Set.iUnionLift_binary (coe_iSup_of_directed dir) dir _ (fun _ => (· + ·))
      all_goals simp
    commutes' := fun r => by
      dsimp
      apply Set.iUnionLift_const _ (fun _ => algebraMap R _ r) <;> simp }


@[target, simp]
theorem iSupLift_inclusion {dir : Directed (· ≤ ·) K} {f : ∀ i, K i →ₐ[R] B}
    {hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (inclusion h)}
    {T : Subalgebra R A} {hT : T = iSup K} {i : ι} (x : K i) (h : K i ≤ T) :
    iSupLift K dir f hf T hT (inclusion h x) = f i x := by sorry

@[simp]
theorem iSupLift_comp_inclusion {dir : Directed (· ≤ ·) K} {f : ∀ i, K i →ₐ[R] B}
    {hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (inclusion h)}
    {T : Subalgebra R A} {hT : T = iSup K} {i : ι} (h : K i ≤ T) :
    (iSupLift K dir f hf T hT).comp (inclusion h) = f i := by ext; simp

@[target, simp]
theorem iSupLift_mk {dir : Directed (· ≤ ·) K} {f : ∀ i, K i →ₐ[R] B}
    {hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (inclusion h)}
    {T : Subalgebra R A} {hT : T = iSup K} {i : ι} (x : K i) (hx : (x : A) ∈ T) :
    iSupLift K dir f hf T hT ⟨x, hx⟩ = f i x := by sorry

@[target]
theorem iSupLift_of_mem {dir : Directed (· ≤ ·) K} {f : ∀ i, K i →ₐ[R] B}
    {hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (inclusion h)}
    {T : Subalgebra R A} {hT : T = iSup K} {i : ι} (x : T) (hx : (x : A) ∈ K i) :
    iSupLift K dir f hf T hT x = f i ⟨x, hx⟩ := by sorry

end Subalgebra
