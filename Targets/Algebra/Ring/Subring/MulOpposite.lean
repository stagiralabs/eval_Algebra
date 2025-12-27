import VerifiedAgora.tagger
/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.Algebra.Ring.Subsemiring.MulOpposite
import Mathlib.Algebra.Ring.Subring.Basic

/-!

# Subring of opposite rings

For every ring `R`, we construct an equivalence between subrings of `R` and that of `Rᵐᵒᵖ`.

-/

namespace Subring

variable {ι : Sort*} {R : Type*} [Ring R]

/-- Pull a subring back to an opposite subring along `MulOpposite.unop` -/
@[simps! coe toSubsemiring]
protected def op (S : Subring R) : Subring Rᵐᵒᵖ where
  toSubsemiring := S.toSubsemiring.op
  neg_mem' {x} hx := neg_mem (show x.unop ∈ S from hx)

attribute [norm_cast] coe_op

@[target, simp]
theorem mem_op {x : Rᵐᵒᵖ} {S : Subring R} : x ∈ S.op ↔ x.unop ∈ S := sorry
@[simps! coe toSubsemiring]
protected def unop (S : Subring Rᵐᵒᵖ) : Subring R where
  toSubsemiring := S.toSubsemiring.unop
  neg_mem' {x} hx := neg_mem (show MulOpposite.op x ∈ S from hx)

attribute [norm_cast] coe_unop

@[simp]
theorem mem_unop {x : R} {S : Subring Rᵐᵒᵖ} : x ∈ S.unop ↔ MulOpposite.op x ∈ S := Iff.rfl

@[simp]
theorem unop_op (S : Subring R) : S.op.unop = S := rfl

@[target, simp]
theorem op_unop (S : Subring Rᵐᵒᵖ) : S.unop.op = S := sorry

theorem op_le_iff {S₁ : Subring R} {S₂ : Subring Rᵐᵒᵖ} : S₁.op ≤ S₂ ↔ S₁ ≤ S₂.unop :=
  MulOpposite.op_surjective.forall

@[target]
theorem le_op_iff {S₁ : Subring Rᵐᵒᵖ} {S₂ : Subring R} : S₁ ≤ S₂.op ↔ S₁.unop ≤ S₂ :=
  sorry

@[simp]
theorem op_le_op_iff {S₁ S₂ : Subring R} : S₁.op ≤ S₂.op ↔ S₁ ≤ S₂ :=
  MulOpposite.op_surjective.forall

@[target, simp]
theorem unop_le_unop_iff {S₁ S₂ : Subring Rᵐᵒᵖ} : S₁.unop ≤ S₂.unop ↔ S₁ ≤ S₂ :=
  sorry
@[simps]
def opEquiv : Subring R ≃o Subring Rᵐᵒᵖ where
  toFun := Subring.op
  invFun := Subring.unop
  left_inv := unop_op
  right_inv := op_unop
  map_rel_iff' := op_le_op_iff

@[target]
theorem op_injective : (@Subring.op R _).Injective := sorry
theorem unop_injective : (@Subring.unop R _).Injective := opEquiv.symm.injective
@[simp] theorem op_inj {S T : Subring R} : S.op = T.op ↔ S = T := opEquiv.eq_iff_eq
@[simp] theorem unop_inj {S T : Subring Rᵐᵒᵖ} : S.unop = T.unop ↔ S = T := opEquiv.symm.eq_iff_eq

@[target, simp]
theorem op_bot : (⊥ : Subring R).op = ⊥ := sorry

@[target, simp]
theorem op_eq_bot {S : Subring R} : S.op = ⊥ ↔ S = ⊥ := sorry

@[simp]
theorem unop_bot : (⊥ : Subring Rᵐᵒᵖ).unop = ⊥ := opEquiv.symm.map_bot

@[simp]
theorem unop_eq_bot {S : Subring Rᵐᵒᵖ} : S.unop = ⊥ ↔ S = ⊥ := unop_injective.eq_iff' unop_bot

@[target, simp]
theorem op_top : (⊤ : Subring R).op = ⊤ := sorry

@[target, simp]
theorem op_eq_top {S : Subring R} : S.op = ⊤ ↔ S = ⊤ := sorry

@[target, simp]
theorem unop_top : (⊤ : Subring Rᵐᵒᵖ).unop = ⊤ := sorry

@[target, simp]
theorem unop_eq_top {S : Subring Rᵐᵒᵖ} : S.unop = ⊤ ↔ S = ⊤ := sorry

theorem op_sup (S₁ S₂ : Subring R) : (S₁ ⊔ S₂).op = S₁.op ⊔ S₂.op :=
  opEquiv.map_sup _ _

theorem unop_sup (S₁ S₂ : Subring Rᵐᵒᵖ) : (S₁ ⊔ S₂).unop = S₁.unop ⊔ S₂.unop :=
  opEquiv.symm.map_sup _ _

@[target]
theorem op_inf (S₁ S₂ : Subring R) : (S₁ ⊓ S₂).op = S₁.op ⊓ S₂.op := sorry

@[target]
theorem unop_inf (S₁ S₂ : Subring Rᵐᵒᵖ) : (S₁ ⊓ S₂).unop = S₁.unop ⊓ S₂.unop := sorry

theorem op_sSup (S : Set (Subring R)) : (sSup S).op = sSup (.unop ⁻¹' S) :=
  opEquiv.map_sSup_eq_sSup_symm_preimage _

@[target]
theorem unop_sSup (S : Set (Subring Rᵐᵒᵖ)) : (sSup S).unop = sSup (.op ⁻¹' S) :=
  sorry

theorem op_sInf (S : Set (Subring R)) : (sInf S).op = sInf (.unop ⁻¹' S) :=
  opEquiv.map_sInf_eq_sInf_symm_preimage _

@[target]
theorem unop_sInf (S : Set (Subring Rᵐᵒᵖ)) : (sInf S).unop = sInf (.op ⁻¹' S) :=
  sorry

@[target]
theorem op_iSup (S : ι → Subring R) : (iSup S).op = ⨆ i, (S i).op := sorry

@[target]
theorem unop_iSup (S : ι → Subring Rᵐᵒᵖ) : (iSup S).unop = ⨆ i, (S i).unop :=
  sorry

@[target]
theorem op_iInf (S : ι → Subring R) : (iInf S).op = ⨅ i, (S i).op := sorry

theorem unop_iInf (S : ι → Subring Rᵐᵒᵖ) : (iInf S).unop = ⨅ i, (S i).unop :=
  opEquiv.symm.map_iInf _

@[target]
theorem op_closure (s : Set R) : (closure s).op = closure (MulOpposite.unop ⁻¹' s) := by sorry

theorem unop_closure (s : Set Rᵐᵒᵖ) : (closure s).unop = closure (MulOpposite.op ⁻¹' s) := by
  rw [← op_inj, op_unop, op_closure]
  simp_rw [Set.preimage_preimage, MulOpposite.op_unop, Set.preimage_id']

/-- Bijection between a subring `S` and its opposite. -/
@[simps!]
def addEquivOp (S : Subring R) : S ≃+ S.op := S.toSubsemiring.addEquivOp

/-- Bijection between a subring `S` and `MulOpposite` of its opposite. -/
@[simps!]
def ringEquivOpMop (S : Subring R) : S ≃+* (S.op)ᵐᵒᵖ := S.toSubsemiring.ringEquivOpMop

/-- Bijection between `MulOpposite` of a subring `S` and its opposite. -/
@[simps!]
def mopRingEquivOp (S : Subring R) : Sᵐᵒᵖ ≃+* S.op := S.toSubsemiring.mopRingEquivOp

end Subring
