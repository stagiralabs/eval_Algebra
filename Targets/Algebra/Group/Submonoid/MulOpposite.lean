import VerifiedAgora.tagger
/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Jujian Zhang
-/
import Mathlib.Algebra.Group.Opposite
import Mathlib.Algebra.Group.Submonoid.Basic

/-!
# Submonoid of opposite monoids

For every monoid `M`, we construct an equivalence between submonoids of `M` and that of `Mᵐᵒᵖ`.

-/

assert_not_exists MonoidWithZero

variable {ι : Sort*} {M : Type*} [MulOneClass M]

namespace Submonoid

/-- Pull a submonoid back to an opposite submonoid along `MulOpposite.unop` -/
@[to_additive (attr := simps) "Pull an additive submonoid back to an opposite submonoid along
`AddOpposite.unop`"]
protected def op (x : Submonoid M) : Submonoid Mᵐᵒᵖ where
  carrier := MulOpposite.unop ⁻¹' x
  mul_mem' ha hb := x.mul_mem hb ha
  one_mem' := Submonoid.one_mem' _

@[target, to_additive (attr := sorry
@[to_additive (attr := simps) "Pull an opposite additive submonoid back to a submonoid along
`AddOpposite.op`"]
protected def unop (x : Submonoid Mᵐᵒᵖ) : Submonoid M where
  carrier := MulOpposite.op ⁻¹' x
  mul_mem' ha hb := x.mul_mem hb ha
  one_mem' := Submonoid.one_mem' _

@[target, to_additive (attr := sorry

@[to_additive (attr := simp)]
theorem unop_op (S : Submonoid M) : S.op.unop = S := rfl

@[target, to_additive (attr := sorry

@[to_additive]
theorem op_le_iff {S₁ : Submonoid M} {S₂ : Submonoid Mᵐᵒᵖ} : S₁.op ≤ S₂ ↔ S₁ ≤ S₂.unop :=
  MulOpposite.op_surjective.forall

@[target, to_additive]
theorem le_op_iff {S₁ : Submonoid Mᵐᵒᵖ} {S₂ : Submonoid M} : S₁ ≤ S₂.op ↔ S₁.unop ≤ S₂ :=
  sorry

@[target, to_additive (attr := sorry

@[target, to_additive (attr := sorry
@[to_additive (attr := simps) "A additive submonoid `H` of `G` determines an additive submonoid
`H.op` of the opposite group `Gᵐᵒᵖ`."]
def opEquiv : Submonoid M ≃o Submonoid Mᵐᵒᵖ where
  toFun := Submonoid.op
  invFun := Submonoid.unop
  left_inv := unop_op
  right_inv := op_unop
  map_rel_iff' := op_le_op_iff

@[to_additive]
theorem op_injective : (@Submonoid.op M _).Injective := opEquiv.injective

@[target, to_additive]
theorem unop_injective : (@Submonoid.unop M _).Injective := sorry

@[target, to_additive (attr := sorry

@[target, to_additive (attr := sorry

@[target, to_additive (attr := sorry

@[target, to_additive (attr := sorry

@[target, to_additive (attr := sorry

@[target, to_additive (attr := sorry

@[target, to_additive (attr := sorry

@[to_additive (attr := simp)]
theorem op_eq_top {S : Submonoid M} : S.op = ⊤ ↔ S = ⊤ := op_injective.eq_iff' op_top

@[target, to_additive (attr := sorry

@[target, to_additive (attr := sorry

@[target, to_additive]
theorem op_sup (S₁ S₂ : Submonoid M) : (S₁ ⊔ S₂).op = S₁.op ⊔ S₂.op :=
  sorry

@[target, to_additive]
theorem unop_sup (S₁ S₂ : Submonoid Mᵐᵒᵖ) : (S₁ ⊔ S₂).unop = S₁.unop ⊔ S₂.unop :=
  sorry

@[target, to_additive]
theorem op_inf (S₁ S₂ : Submonoid M) : (S₁ ⊓ S₂).op = S₁.op ⊓ S₂.op := sorry

@[to_additive]
theorem unop_inf (S₁ S₂ : Submonoid Mᵐᵒᵖ) : (S₁ ⊓ S₂).unop = S₁.unop ⊓ S₂.unop := rfl

@[target, to_additive]
theorem op_sSup (S : Set (Submonoid M)) : (sSup S).op = sSup (.unop ⁻¹' S) :=
  sorry

@[target, to_additive]
theorem unop_sSup (S : Set (Submonoid Mᵐᵒᵖ)) : (sSup S).unop = sSup (.op ⁻¹' S) :=
  sorry

@[to_additive]
theorem op_sInf (S : Set (Submonoid M)) : (sInf S).op = sInf (.unop ⁻¹' S) :=
  opEquiv.map_sInf_eq_sInf_symm_preimage _

@[target, to_additive]
theorem unop_sInf (S : Set (Submonoid Mᵐᵒᵖ)) : (sInf S).unop = sInf (.op ⁻¹' S) :=
  sorry

@[target, to_additive]
theorem op_iSup (S : ι → Submonoid M) : (iSup S).op = ⨆ i, (S i).op := sorry

@[to_additive]
theorem unop_iSup (S : ι → Submonoid Mᵐᵒᵖ) : (iSup S).unop = ⨆ i, (S i).unop :=
  opEquiv.symm.map_iSup _

@[to_additive]
theorem op_iInf (S : ι → Submonoid M) : (iInf S).op = ⨅ i, (S i).op := opEquiv.map_iInf _

@[target, to_additive]
theorem unop_iInf (S : ι → Submonoid Mᵐᵒᵖ) : (iInf S).unop = ⨅ i, (S i).unop :=
  sorry

@[target, to_additive]
theorem op_closure (s : Set M) : (closure s).op = closure (MulOpposite.unop ⁻¹' s) := by sorry

@[to_additive]
theorem unop_closure (s : Set Mᵐᵒᵖ) : (closure s).unop = closure (MulOpposite.op ⁻¹' s) := by
  rw [← op_inj, op_unop, op_closure]
  simp_rw [Set.preimage_preimage, MulOpposite.op_unop, Set.preimage_id']

/-- Bijection between a submonoid `H` and its opposite. -/
@[to_additive (attr := simps!) "Bijection between an additive submonoid `H` and its opposite."]
def equivOp (H : Submonoid M) : H ≃ H.op :=
  MulOpposite.opEquiv.subtypeEquiv fun _ => Iff.rfl

end Submonoid
