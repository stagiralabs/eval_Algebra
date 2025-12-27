import VerifiedAgora.tagger
/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.Quaternion

/-!
# Dual quaternions

Similar to the way that rotations in 3D space can be represented by quaternions of unit length,
rigid motions in 3D space can be represented by dual quaternions of unit length.

## Main results

* `Quaternion.dualNumberEquiv`: quaternions over dual numbers or dual
  numbers over quaternions are equivalent constructions.

## References

* <https://en.wikipedia.org/wiki/Dual_quaternion>
-/


variable {R : Type*} [CommRing R]

namespace Quaternion

/-- The dual quaternions can be equivalently represented as a quaternion with dual coefficients,
or as a dual number with quaternion coefficients.

See also `Matrix.dualNumberEquiv` for a similar result. -/
/-- The dual quaternions can be equivalently represented as a quaternion with dual coefficients,
or as a dual number with quaternion coefficients.

See also `Matrix.dualNumberEquiv` for a similar result. -/
def dualNumberEquiv : Quaternion (DualNumber R) ≃ₐ[R] DualNumber (Quaternion R) where
  toFun q :=
    (⟨q.re.fst, q.imI.fst, q.imJ.fst, q.imK.fst⟩, ⟨q.re.snd, q.imI.snd, q.imJ.snd, q.imK.snd⟩)
  invFun d :=
    ⟨(d.fst.re, d.snd.re), (d.fst.imI, d.snd.imI), (d.fst.imJ, d.snd.imJ), (d.fst.imK, d.snd.imK)⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_mul' := by
    sorry

@[target] theorem re_fst_dualNumberEquiv (q : Quaternion (DualNumber R)) :
    (dualNumberEquiv q).fst.re = q.re.fst := by sorry


@[target] theorem imI_fst_dualNumberEquiv (q : Quaternion (DualNumber R)) :
    (dualNumberEquiv q).fst.imI = q.imI.fst := by sorry


@[target] theorem imJ_fst_dualNumberEquiv (q : Quaternion (DualNumber R)) :
    (dualNumberEquiv q).fst.imJ = q.imJ.fst := by sorry


@[simp]
theorem imK_fst_dualNumberEquiv (q : Quaternion (DualNumber R)) :
    (dualNumberEquiv q).fst.imK = q.imK.fst :=
  rfl

@[target] theorem re_snd_dualNumberEquiv (q : Quaternion (DualNumber R)) :
    (dualNumberEquiv q).snd.re = q.re.snd := by sorry


@[simp]
theorem imI_snd_dualNumberEquiv (q : Quaternion (DualNumber R)) :
    (dualNumberEquiv q).snd.imI = q.imI.snd :=
  rfl

@[target] theorem imJ_snd_dualNumberEquiv (q : Quaternion (DualNumber R)) :
    (dualNumberEquiv q).snd.imJ = q.imJ.snd := by sorry


@[simp]
theorem imK_snd_dualNumberEquiv (q : Quaternion (DualNumber R)) :
    (dualNumberEquiv q).snd.imK = q.imK.snd :=
  rfl

@[target] theorem fst_re_dualNumberEquiv_symm (d : DualNumber (Quaternion R)) :
    (dualNumberEquiv.symm d).re.fst = d.fst.re := by sorry


@[target] theorem fst_imI_dualNumberEquiv_symm (d : DualNumber (Quaternion R)) :
    (dualNumberEquiv.symm d).imI.fst = d.fst.imI := by sorry


@[target] theorem fst_imJ_dualNumberEquiv_symm (d : DualNumber (Quaternion R)) :
    (dualNumberEquiv.symm d).imJ.fst = d.fst.imJ := by sorry


@[target] theorem fst_imK_dualNumberEquiv_symm (d : DualNumber (Quaternion R)) :
    (dualNumberEquiv.symm d).imK.fst = d.fst.imK := by sorry


@[simp]
theorem snd_re_dualNumberEquiv_symm (d : DualNumber (Quaternion R)) :
    (dualNumberEquiv.symm d).re.snd = d.snd.re :=
  rfl

@[simp]
theorem snd_imI_dualNumberEquiv_symm (d : DualNumber (Quaternion R)) :
    (dualNumberEquiv.symm d).imI.snd = d.snd.imI :=
  rfl

@[target] theorem snd_imJ_dualNumberEquiv_symm (d : DualNumber (Quaternion R)) :
    (dualNumberEquiv.symm d).imJ.snd = d.snd.imJ := by sorry


@[target] theorem snd_imK_dualNumberEquiv_symm (d : DualNumber (Quaternion R)) :
    (dualNumberEquiv.symm d).imK.snd = d.snd.imK := by sorry


end Quaternion
