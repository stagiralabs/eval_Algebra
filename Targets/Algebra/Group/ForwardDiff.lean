import VerifiedAgora.tagger
/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Caflisch, David Loeffler
-/
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Abel

/-!
# Forward difference operators and Newton series

We define the forward difference operator, sending `f` to the function `x ↦ f (x + h) - f x` for
a given `h` (for any additive semigroup, taking values in an abelian group). The notation `Δ_[h]` is
defined for this operator, scoped in namespace `fwdDiff`.

We prove two key formulae about this operator:

* `shift_eq_sum_fwdDiff_iter`: the **Gregory-Newton formula**, expressing `f (y + n • h)` as a
  linear combination of forward differences of `f` at `y`, for `n ∈ ℕ`;
* `fwdDiff_iter_eq_sum_shift`: formula expressing the `n`-th forward difference of `f` at `y` as
  a linear combination of `f (y + k • h)` for `0 ≤ k ≤ n`.

We also prove some auxiliary results about iterated forward differences of the function
`n ↦ n.choose k`.
-/

open Finset Nat Function

variable {M G : Type*} [AddCommMonoid M] [AddCommGroup G] (h : M)

/--
Forward difference operator, `fwdDiff h f n = f (n + h) - f n`. The notation `Δ_[h]` for this
operator is available in the `fwdDiff` namespace.
-/
def fwdDiff (h : M) (f : M → G) : M → G := fun n ↦ f (n + h) - f n

@[inherit_doc] scoped[fwdDiff] notation "Δ_[" h "]" => fwdDiff h

open fwdDiff

@[simp] lemma fwdDiff_add (h : M) (f g : M → G) :
    Δ_[h] (f + g) = Δ_[h] f + Δ_[h] g :=
  add_sub_add_comm ..

@[simp] lemma fwdDiff_const (g : G) : Δ_[h] (fun _ ↦ g : M → G) = fun _ ↦ 0 :=
  funext fun _ ↦ sub_self g

section smul

@[target]
lemma fwdDiff_smul {R : Type} [Ring R] [Module R G] (f : M → R) (g : M → G) :
    Δ_[h] (f • g) = Δ_[h] f • g + f • Δ_[h] g + Δ_[h] f • Δ_[h] g := by sorry

-- Note `fwdDiff_const_smul` is more general than `fwdDiff_smul` since it allows `R` to be a
-- semiring, rather than a ring; in particular `R = ℕ` is allowed.
@[simp] lemma fwdDiff_const_smul {R : Type*} [Semiring R] [Module R G] (r : R) (f : M → G) :
    Δ_[h] (r • f) = r • Δ_[h] f :=
  funext fun _ ↦ (smul_sub ..).symm

@[simp] lemma fwdDiff_smul_const {R : Type} [Ring R] [Module R G] (f : M → R) (g : G) :
    Δ_[h] (fun y ↦ f y • g) = Δ_[h] f • fun _ ↦ g := by
  ext y
  simp only [fwdDiff, Pi.smul_apply', sub_smul]

end smul

namespace fwdDiff_aux
/-!
## Forward-difference and shift operators as linear endomorphisms

This section contains versions of the forward-difference operator and the shift operator bundled as
`ℤ`-linear endomorphisms. These are useful for certain proofs; but they are slightly annoying to
use, as the source and target types of the maps have to be specified each time, and various
coercions need to be un-wound when the operators are applied, so we also provide the un-bundled
version.
-/

variable (M G) in
/-- Linear-endomorphism version of the forward difference operator. -/
@[simps]
def fwdDiffₗ  : Module.End ℤ (M → G) where
  toFun := fwdDiff h
  map_add' := fwdDiff_add h
  map_smul' := fwdDiff_const_smul h

lemma coe_fwdDiffₗ : ↑(fwdDiffₗ M G h) = fwdDiff h := rfl

@[target]
lemma coe_fwdDiffₗ_pow (n : ℕ) : ↑(fwdDiffₗ M G h ^ n) = (fwdDiff h)^[n] := by sorry

variable (M G) in
/-- Linear-endomorphism version of the shift-by-1 operator. -/
def shiftₗ : Module.End ℤ (M → G) := fwdDiffₗ M G h + 1

@[target]
lemma shiftₗ_apply (f : M → G) (y : M) : shiftₗ M G h f y = f (y + h) := by sorry

@[target]
lemma shiftₗ_pow_apply (f : M → G) (k : ℕ) (y : M) : (shiftₗ M G h ^ k) f y = f (y + k • h) := by sorry

end fwdDiff_aux

open fwdDiff_aux

@[simp] lemma fwdDiff_finset_sum {α : Type*} (s : Finset α) (f : α → M → G) :
    Δ_[h] (∑ k ∈ s, f k) = ∑ k ∈ s, Δ_[h] (f k) :=
  map_sum (fwdDiffₗ M G h) f s

@[simp] lemma fwdDiff_iter_add (f g : M → G) (n : ℕ) :
    Δ_[h]^[n] (f + g) = Δ_[h]^[n] f + Δ_[h]^[n] g := by
  simpa only [coe_fwdDiffₗ_pow] using map_add (fwdDiffₗ M G h ^ n) f g

@[simp] lemma fwdDiff_iter_const_smul {R : Type*} [Semiring R] [Module R G]
    (r : R) (f : M → G) (n : ℕ) : Δ_[h]^[n] (r • f) = r • Δ_[h]^[n] f := by
  induction' n with n IH generalizing f
  · simp only [iterate_zero, id_eq]
  · simp only [iterate_succ_apply, fwdDiff_const_smul, IH]

@[simp] lemma fwdDiff_iter_finset_sum {α : Type*} (s : Finset α) (f : α → M → G) (n : ℕ) :
    Δ_[h]^[n] (∑ k ∈ s, f k) = ∑ k ∈ s, Δ_[h]^[n] (f k) := by
  simpa only [coe_fwdDiffₗ_pow] using map_sum (fwdDiffₗ M G h ^ n) f s

section newton_formulae

/--
Express the `n`-th forward difference of `f` at `y` in terms of the values `f (y + k)`, for
`0 ≤ k ≤ n`.
-/
@[target]
theorem fwdDiff_iter_eq_sum_shift (f : M → G) (n : ℕ) (y : M) :
    Δ_[h]^[n] f y = ∑ k ∈ range (n + 1), ((-1 : ℤ) ^ (n - k) * n.choose k) • f (y + k • h) := by sorry
theorem shift_eq_sum_fwdDiff_iter (f : M → G) (n : ℕ) (y : M) :
    f (y + n • h) = ∑ k ∈ range (n + 1), n.choose k • Δ_[h]^[k] f y := by
  convert congr_fun (LinearMap.congr_fun
      ((Commute.one_right (fwdDiffₗ M G h)).add_pow n) f) y using 1
  · rw [← shiftₗ_pow_apply h f, shiftₗ]
  · simp only [LinearMap.sum_apply, sum_apply, one_pow, mul_one, LinearMap.mul_apply,
      Module.End.natCast_apply, map_nsmul, Pi.smul_apply, LinearMap.pow_apply, coe_fwdDiffₗ]

end newton_formulae

section choose

lemma fwdDiff_choose (j : ℕ) : Δ_[1] (fun x ↦ x.choose (j + 1) : ℕ → ℤ) = fun x ↦ x.choose j := by
  ext n
  simp only [fwdDiff, choose_succ_succ' n j, cast_add, add_sub_cancel_right]

@[target]
lemma fwdDiff_iter_choose (j k : ℕ) :
    Δ_[1]^[k] (fun x ↦ x.choose (k + j) : ℕ → ℤ) = fun x ↦ x.choose j := by sorry

@[target]
lemma fwdDiff_iter_choose_zero (m n : ℕ) :
    Δ_[1]^[n] (fun x ↦ x.choose m : ℕ → ℤ) 0 = if n = m then 1 else 0 := by sorry

end choose
