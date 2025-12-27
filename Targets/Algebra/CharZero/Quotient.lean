import VerifiedAgora.tagger
/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Algebra.Module.NatInt
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

/-!
# Lemmas about quotients in characteristic zero
-/


variable {R : Type*} [DivisionRing R] [CharZero R] {p : R}

namespace AddSubgroup

/-- `z • r` is a multiple of `p` iff `r` is `pk/z` above a multiple of `p`, where `0 ≤ k < |z|`. -/
@[target]
theorem zsmul_mem_zmultiples_iff_exists_sub_div {r : R} {z : ℤ} (hz : z ≠ 0) :
    z • r ∈ AddSubgroup.zmultiples p ↔
      ∃ k : Fin z.natAbs, r - (k : ℕ) • (p / z : R) ∈ AddSubgroup.zmultiples p := by sorry

theorem nsmul_mem_zmultiples_iff_exists_sub_div {r : R} {n : ℕ} (hn : n ≠ 0) :
    n • r ∈ AddSubgroup.zmultiples p ↔
      ∃ k : Fin n, r - (k : ℕ) • (p / n : R) ∈ AddSubgroup.zmultiples p := by
  rw [← natCast_zsmul r, zsmul_mem_zmultiples_iff_exists_sub_div (Int.natCast_ne_zero.mpr hn),
    Int.cast_natCast]
  rfl

end AddSubgroup

namespace QuotientAddGroup

theorem zmultiples_zsmul_eq_zsmul_iff {ψ θ : R ⧸ AddSubgroup.zmultiples p} {z : ℤ} (hz : z ≠ 0) :
    z • ψ = z • θ ↔ ∃ k : Fin z.natAbs, ψ = θ + ((k : ℕ) • (p / z) : R) := by
  induction ψ using Quotient.inductionOn
  induction θ using Quotient.inductionOn
  -- Porting note: Introduced Zp notation to shorten lines
  let Zp := AddSubgroup.zmultiples p
  have : (Quotient.mk _ : R → R ⧸ Zp) = ((↑) : R → R ⧸ Zp) := rfl
  simp only [Zp, this]
  simp_rw [← QuotientAddGroup.mk_zsmul, ← QuotientAddGroup.mk_add,
    QuotientAddGroup.eq_iff_sub_mem, ← smul_sub, ← sub_sub]
  exact AddSubgroup.zsmul_mem_zmultiples_iff_exists_sub_div hz

@[target]
theorem zmultiples_nsmul_eq_nsmul_iff {ψ θ : R ⧸ AddSubgroup.zmultiples p} {n : ℕ} (hz : n ≠ 0) :
    n • ψ = n • θ ↔ ∃ k : Fin n, ψ = θ + (k : ℕ) • (p / n : R) := by sorry

end QuotientAddGroup
