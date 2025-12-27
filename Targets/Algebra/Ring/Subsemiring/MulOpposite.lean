import VerifiedAgora.tagger
/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.Algebra.Group.Submonoid.MulOpposite
import Mathlib.Algebra.Ring.Subsemiring.Basic
import Mathlib.Algebra.Ring.Opposite

/-!

# Subsemiring of opposite semirings

For every semiring `R`, we construct an equivalence between subsemirings of `R` and that of `Rᵐᵒᵖ`.

-/

namespace Subsemiring

variable {ι : Sort*} {R : Type*} [NonAssocSemiring R]

/-- Pull a subsemiring back to an opposite subsemiring along `MulOpposite.unop` -/
@[simps! coe toSubmonoid]
protected def op (S : Subsemiring R) : Subsemiring Rᵐᵒᵖ where
  toSubmonoid := S.toSubmonoid.op
  add_mem' {x} {y} hx hy := add_mem (show x.unop ∈ S from hx) (show y.unop ∈ S from hy)
  zero_mem' := zero_mem S

attribute [norm_cast] coe_op

@[target, simp]
theorem mem_op {x : Rᵐᵒᵖ} {S : Subsemiring R} : x ∈ S.op ↔ x.unop ∈ S := sorry
@[simps! coe toSubmonoid]
protected def unop (S : Subsemiring Rᵐᵒᵖ) : Subsemiring R where
  toSubmonoid := S.toSubmonoid.unop
  add_mem' {x} {y} hx hy := add_mem
    (show MulOpposite.op x ∈ S from hx) (show MulOpposite.op y ∈ S from hy)
  zero_mem' := zero_mem S

attribute [norm_cast] coe_unop

@[simp]
theorem mem_unop {x : R} {S : Subsemiring Rᵐᵒᵖ} : x ∈ S.unop ↔ MulOpposite.op x ∈ S := Iff.rfl

@[target, simp]
theorem unop_op (S : Subsemiring R) : S.op.unop = S := sorry

@[target, simp]
theorem op_unop (S : Subsemiring Rᵐᵒᵖ) : S.unop.op = S := sorry

theorem op_le_iff {S₁ : Subsemiring R} {S₂ : Subsemiring Rᵐᵒᵖ} : S₁.op ≤ S₂ ↔ S₁ ≤ S₂.unop :=
  MulOpposite.op_surjective.forall

theorem le_op_iff {S₁ : Subsemiring Rᵐᵒᵖ} {S₂ : Subsemiring R} : S₁ ≤ S₂.op ↔ S₁.unop ≤ S₂ :=
  MulOpposite.op_surjective.forall

@[target, simp]
theorem op_le_op_iff {S₁ S₂ : Subsemiring R} : S₁.op ≤ S₂.op ↔ S₁ ≤ S₂ :=
  sorry

@[target, simp]
theorem unop_le_unop_iff {S₁ S₂ : Subsemiring Rᵐᵒᵖ} : S₁.unop ≤ S₂.unop ↔ S₁ ≤ S₂ :=
  sorry
@[simps]
def opEquiv : Subsemiring R ≃o Subsemiring Rᵐᵒᵖ where
  toFun := Subsemiring.op
  invFun := Subsemiring.unop
  left_inv := unop_op
  right_inv := op_unop
  map_rel_iff' := op_le_op_iff

@[target]
theorem op_injective : (@Subsemiring.op R _).Injective := sorry
@[target]
theorem unop_injective : (@Subsemiring.unop R _).Injective := sorry

@[simp] theorem op_inj {S T : Subsemiring R} : S.op = T.op ↔ S = T := opEquiv.eq_iff_eq

@[simp]
theorem unop_inj {S T : Subsemiring Rᵐᵒᵖ} : S.unop = T.unop ↔ S = T := opEquiv.symm.eq_iff_eq

@[target, simp]
theorem op_bot : (⊥ : Subsemiring R).op = ⊥ := sorry

@[target, simp]
theorem op_eq_bot {S : Subsemiring R} : S.op = ⊥ ↔ S = ⊥ := sorry

@[target, simp]
theorem unop_bot : (⊥ : Subsemiring Rᵐᵒᵖ).unop = ⊥ := sorry

@[simp]
theorem unop_eq_bot {S : Subsemiring Rᵐᵒᵖ} : S.unop = ⊥ ↔ S = ⊥ := unop_injective.eq_iff' unop_bot

@[simp]
theorem op_top : (⊤ : Subsemiring R).op = ⊤ := rfl

@[simp]
theorem op_eq_top {S : Subsemiring R} : S.op = ⊤ ↔ S = ⊤ := op_injective.eq_iff' op_top

@[target, simp]
theorem unop_top : (⊤ : Subsemiring Rᵐᵒᵖ).unop = ⊤ := sorry

@[target, simp]
theorem unop_eq_top {S : Subsemiring Rᵐᵒᵖ} : S.unop = ⊤ ↔ S = ⊤ := sorry

@[target]
theorem op_sup (S₁ S₂ : Subsemiring R) : (S₁ ⊔ S₂).op = S₁.op ⊔ S₂.op :=
  sorry

@[target]
theorem unop_sup (S₁ S₂ : Subsemiring Rᵐᵒᵖ) : (S₁ ⊔ S₂).unop = S₁.unop ⊔ S₂.unop :=
  sorry

@[target]
theorem op_inf (S₁ S₂ : Subsemiring R) : (S₁ ⊓ S₂).op = S₁.op ⊓ S₂.op := sorry

theorem unop_inf (S₁ S₂ : Subsemiring Rᵐᵒᵖ) : (S₁ ⊓ S₂).unop = S₁.unop ⊓ S₂.unop := rfl

@[target]
theorem op_sSup (S : Set (Subsemiring R)) : (sSup S).op = sSup (.unop ⁻¹' S) :=
  sorry

@[target]
theorem unop_sSup (S : Set (Subsemiring Rᵐᵒᵖ)) : (sSup S).unop = sSup (.op ⁻¹' S) :=
  sorry

theorem op_sInf (S : Set (Subsemiring R)) : (sInf S).op = sInf (.unop ⁻¹' S) :=
  opEquiv.map_sInf_eq_sInf_symm_preimage _

@[target]
theorem unop_sInf (S : Set (Subsemiring Rᵐᵒᵖ)) : (sInf S).unop = sInf (.op ⁻¹' S) :=
  sorry

theorem op_iSup (S : ι → Subsemiring R) : (iSup S).op = ⨆ i, (S i).op := opEquiv.map_iSup _

@[target]
theorem unop_iSup (S : ι → Subsemiring Rᵐᵒᵖ) : (iSup S).unop = ⨆ i, (S i).unop :=
  sorry

@[target]
theorem op_iInf (S : ι → Subsemiring R) : (iInf S).op = ⨅ i, (S i).op := sorry

theorem unop_iInf (S : ι → Subsemiring Rᵐᵒᵖ) : (iInf S).unop = ⨅ i, (S i).unop :=
  opEquiv.symm.map_iInf _

@[target]
theorem op_closure (s : Set R) : (closure s).op = closure (MulOpposite.unop ⁻¹' s) := by sorry

@[target]
theorem unop_closure (s : Set Rᵐᵒᵖ) : (closure s).unop = closure (MulOpposite.op ⁻¹' s) := by sorry
@[simps!]
def addEquivOp (S : Subsemiring R) : S ≃+ S.op where
  toEquiv := S.toSubmonoid.equivOp
  map_add' _ _ := rfl

-- TODO: Add this for `[Add]Submonoid` and `[Add]Subgroup`
/-- Bijection between a subsemiring `S` and `MulOpposite` of its opposite. -/
@[simps!]
def ringEquivOpMop (S : Subsemiring R) : S ≃+* (S.op)ᵐᵒᵖ where
  __ := S.addEquivOp.trans MulOpposite.opAddEquiv
  map_mul' _ _ := rfl

-- TODO: Add this for `[Add]Submonoid` and `[Add]Subgroup`
/-- Bijection between `MulOpposite` of a subsemiring `S` and its opposite. -/
@[simps!]
def mopRingEquivOp (S : Subsemiring R) : Sᵐᵒᵖ ≃+* S.op where
  __ := MulOpposite.opAddEquiv.symm.trans S.addEquivOp
  map_mul' _ _ := rfl

end Subsemiring
