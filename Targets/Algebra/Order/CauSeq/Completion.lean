import VerifiedAgora.tagger
/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Robert Y. Lewis
-/
import Mathlib.Algebra.Order.CauSeq.Basic
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic.FastInstance

/-!
# Cauchy completion

This file generalizes the Cauchy completion of `(ℚ, abs)` to the completion of a ring
with absolute value.
-/


namespace CauSeq.Completion

open CauSeq

section

variable {α : Type*} [LinearOrderedField α]
variable {β : Type*} [Ring β] (abv : β → α) [IsAbsoluteValue abv]

-- TODO: rename this to `CauSeq.Completion` instead of `CauSeq.Completion.Cauchy`.
/-- The Cauchy completion of a ring with absolute value. -/
def Cauchy :=
  @Quotient (CauSeq _ abv) CauSeq.equiv

variable {abv}

/-- The map from Cauchy sequences into the Cauchy completion. -/
def mk : CauSeq _ abv → Cauchy abv :=
  Quotient.mk''

@[target, simp]
theorem mk_eq_mk (f : CauSeq _ abv) : @Eq (Cauchy abv) ⟦f⟧ (mk f) :=
  sorry

theorem mk_eq {f g : CauSeq _ abv} : mk f = mk g ↔ f ≈ g :=
  Quotient.eq

/-- The map from the original ring into the Cauchy completion. -/
def ofRat (x : β) : Cauchy abv :=
  mk (const abv x)

instance : Zero (Cauchy abv) :=
  ⟨ofRat 0⟩

instance : One (Cauchy abv) :=
  ⟨ofRat 1⟩

instance : Inhabited (Cauchy abv) :=
  ⟨0⟩

@[target]
theorem ofRat_zero : (ofRat 0 : Cauchy abv) = 0 :=
  sorry

theorem ofRat_one : (ofRat 1 : Cauchy abv) = 1 :=
  rfl

@[target, simp]
theorem mk_eq_zero {f : CauSeq _ abv} : mk f = 0 ↔ LimZero f := by sorry

instance : Add (Cauchy abv) :=
  ⟨(Quotient.map₂ (· + ·)) fun _ _ hf _ _ hg => add_equiv_add hf hg⟩

@[simp]
theorem mk_add (f g : CauSeq β abv) : mk f + mk g = mk (f + g) :=
  rfl

instance : Neg (Cauchy abv) :=
  ⟨(Quotient.map Neg.neg) fun _ _ hf => neg_equiv_neg hf⟩

@[simp]
theorem mk_neg (f : CauSeq β abv) : -mk f = mk (-f) :=
  rfl

instance : Mul (Cauchy abv) :=
  ⟨(Quotient.map₂ (· * ·)) fun _ _ hf _ _ hg => mul_equiv_mul hf hg⟩

@[target, simp]
theorem mk_mul (f g : CauSeq β abv) : mk f * mk g = mk (f * g) :=
  sorry

instance : Sub (Cauchy abv) :=
  ⟨(Quotient.map₂ Sub.sub) fun _ _ hf _ _ hg => sub_equiv_sub hf hg⟩

@[target, simp]
theorem mk_sub (f g : CauSeq β abv) : mk f - mk g = mk (f - g) :=
  sorry

instance {γ : Type*} [SMul γ β] [IsScalarTower γ β β] : SMul γ (Cauchy abv) :=
  ⟨fun c => (Quotient.map (c • ·)) fun _ _ hf => smul_equiv_smul _ hf⟩

@[simp]
theorem mk_smul {γ : Type*} [SMul γ β] [IsScalarTower γ β β] (c : γ) (f : CauSeq β abv) :
    c • mk f = mk (c • f) :=
  rfl

instance : Pow (Cauchy abv) ℕ :=
  ⟨fun x n => Quotient.map (· ^ n) (fun _ _ hf => pow_equiv_pow hf _) x⟩

@[simp]
theorem mk_pow (n : ℕ) (f : CauSeq β abv) : mk f ^ n = mk (f ^ n) :=
  rfl

instance : NatCast (Cauchy abv) :=
  ⟨fun n => mk n⟩

instance : IntCast (Cauchy abv) :=
  ⟨fun n => mk n⟩

@[simp]
theorem ofRat_natCast (n : ℕ) : (ofRat n : Cauchy abv) = n :=
  rfl

@[simp]
theorem ofRat_intCast (z : ℤ) : (ofRat z : Cauchy abv) = z :=
  rfl

@[target]
theorem ofRat_add (x y : β) :
    ofRat (x + y) = (ofRat x + ofRat y : Cauchy abv) :=
  sorry

@[target]
theorem ofRat_neg (x : β) : ofRat (-x) = (-ofRat x : Cauchy abv) :=
  sorry

theorem ofRat_mul (x y : β) :
    ofRat (x * y) = (ofRat x * ofRat y : Cauchy abv) :=
  congr_arg mk (const_mul _ _)

private theorem zero_def : 0 = mk (abv := abv) 0 :=
  rfl

private theorem one_def : 1 = mk (abv := abv) 1 :=
  rfl

instance Cauchy.ring : Ring (Cauchy abv) := fast_instance%
  Function.Surjective.ring mk Quotient.mk'_surjective zero_def.symm one_def.symm
    (fun _ _ => (mk_add _ _).symm) (fun _ _ => (mk_mul _ _).symm) (fun _ => (mk_neg _).symm)
    (fun _ _ => (mk_sub _ _).symm) (fun _ _ => (mk_smul _ _).symm) (fun _ _ => (mk_smul _ _).symm)
    (fun _ _ => (mk_pow _ _).symm) (fun _ => rfl) fun _ => rfl

/-- `CauSeq.Completion.ofRat` as a `RingHom` -/
@[simps]
def ofRatRingHom : β →+* (Cauchy abv) where
  toFun := ofRat
  map_zero' := ofRat_zero
  map_one' := ofRat_one
  map_add' := ofRat_add
  map_mul' := ofRat_mul

theorem ofRat_sub (x y : β) : ofRat (x - y) = (ofRat x - ofRat y : Cauchy abv) :=
  congr_arg mk (const_sub _ _)

end

section

variable {α : Type*} [LinearOrderedField α]
variable {β : Type*} [CommRing β] {abv : β → α} [IsAbsoluteValue abv]

instance Cauchy.commRing : CommRing (Cauchy abv) := fast_instance%
  Function.Surjective.commRing mk Quotient.mk'_surjective zero_def.symm one_def.symm
    (fun _ _ => (mk_add _ _).symm) (fun _ _ => (mk_mul _ _).symm) (fun _ => (mk_neg _).symm)
    (fun _ _ => (mk_sub _ _).symm) (fun _ _ => (mk_smul _ _).symm) (fun _ _ => (mk_smul _ _).symm)
    (fun _ _ => (mk_pow _ _).symm) (fun _ => rfl) fun _ => rfl

end

section

variable {α : Type*} [LinearOrderedField α]
variable {β : Type*} [DivisionRing β] {abv : β → α} [IsAbsoluteValue abv]

instance instNNRatCast : NNRatCast (Cauchy abv) where nnratCast q := ofRat q
instance instRatCast : RatCast (Cauchy abv) where ratCast q := ofRat q

@[simp, norm_cast] lemma ofRat_nnratCast (q : ℚ≥0) : ofRat (q : β) = (q : Cauchy abv) := rfl
@[simp, norm_cast] lemma ofRat_ratCast (q : ℚ) : ofRat (q : β) = (q : Cauchy abv) := rfl

open Classical in
noncomputable instance : Inv (Cauchy abv) :=
  ⟨fun x =>
    (Quotient.liftOn x fun f => mk <| if h : LimZero f then 0 else inv f h) fun f g fg => by
      have := limZero_congr fg
      by_cases hf : LimZero f
      · simp [hf, this.1 hf, Setoid.refl]
      · have hg := mt this.2 hf
        simp only [hf, dite_false, hg]
        have If : mk (inv f hf) * mk f = 1 := mk_eq.2 (inv_mul_cancel hf)
        have Ig : mk (inv g hg) * mk g = 1 := mk_eq.2 (inv_mul_cancel hg)
        have Ig' : mk g * mk (inv g hg) = 1 := mk_eq.2 (mul_inv_cancel hg)
        rw [mk_eq.2 fg, ← Ig] at If
        rw [← mul_one (mk (inv f hf)), ← Ig', ← mul_assoc, If, mul_assoc, Ig', mul_one]⟩

theorem inv_zero : (0 : (Cauchy abv))⁻¹ = 0 :=
  congr_arg mk <| by rw [dif_pos] <;> [rfl; exact zero_limZero]

@[simp]
theorem inv_mk {f} (hf) : (mk (abv := abv) f)⁻¹ = mk (inv f hf) :=
  congr_arg mk <| by rw [dif_neg]

@[target]
theorem cau_seq_zero_ne_one : ¬(0 : CauSeq _ abv) ≈ 1 := sorry

theorem zero_ne_one : (0 : (Cauchy abv)) ≠ 1 := fun h => cau_seq_zero_ne_one <| mk_eq.1 h

protected theorem inv_mul_cancel {x : (Cauchy abv)} : x ≠ 0 → x⁻¹ * x = 1 :=
  Quotient.inductionOn x fun f hf => by
    simp only [mk_eq_mk, ne_eq, mk_eq_zero] at hf
    simp only [mk_eq_mk, hf, not_false_eq_true, inv_mk, mk_mul]
    exact Quotient.sound (CauSeq.inv_mul_cancel hf)

protected theorem mul_inv_cancel {x : (Cauchy abv)} : x ≠ 0 → x * x⁻¹ = 1 :=
  Quotient.inductionOn x fun f hf => by
    simp only [mk_eq_mk, ne_eq, mk_eq_zero] at hf
    simp only [mk_eq_mk, hf, not_false_eq_true, inv_mk, mk_mul]
    exact Quotient.sound (CauSeq.mul_inv_cancel hf)

theorem ofRat_inv (x : β) : ofRat x⁻¹ = ((ofRat x)⁻¹ : (Cauchy abv)) :=
  congr_arg mk <| by split_ifs with h <;>
    [simp only [const_limZero.1 h, GroupWithZero.inv_zero, const_zero]; rfl]

noncomputable instance instDivInvMonoid : DivInvMonoid (Cauchy abv) where

@[target]
lemma ofRat_div (x y : β) : ofRat (x / y) = (ofRat x / ofRat y : Cauchy abv) := by sorry

variable {α : Type*} [LinearOrderedField α]
variable {β : Type*} [Field β] {abv : β → α} [IsAbsoluteValue abv]

/-- The Cauchy completion forms a field. -/
noncomputable instance Cauchy.field : Field (Cauchy abv) :=
  { Cauchy.divisionRing, Cauchy.commRing with }

end

end CauSeq.Completion

variable {α : Type*} [LinearOrderedField α]

namespace CauSeq

section

variable (β : Type*) [Ring β] (abv : β → α) [IsAbsoluteValue abv]

/-- A class stating that a ring with an absolute value is complete, i.e. every Cauchy
sequence has a limit. -/
class IsComplete : Prop where
  /-- Every Cauchy sequence has a limit. -/
  isComplete : ∀ s : CauSeq β abv, ∃ b : β, s ≈ const abv b

end

section

variable {β : Type*} [Ring β] {abv : β → α} [IsAbsoluteValue abv]
variable [IsComplete β abv]

theorem complete : ∀ s : CauSeq β abv, ∃ b : β, s ≈ const abv b :=
  IsComplete.isComplete

/-- The limit of a Cauchy sequence in a complete ring. Chosen non-computably. -/
noncomputable def lim (s : CauSeq β abv) : β :=
  Classical.choose (complete s)

@[target]
theorem equiv_lim (s : CauSeq β abv) : s ≈ const abv (lim s) :=
  sorry

@[target]
theorem eq_lim_of_const_equiv {f : CauSeq β abv} {x : β} (h : CauSeq.const abv x ≈ f) : x = lim f :=
  sorry

theorem lim_eq_of_equiv_const {f : CauSeq β abv} {x : β} (h : f ≈ CauSeq.const abv x) : lim f = x :=
  (eq_lim_of_const_equiv <| Setoid.symm h).symm

@[target]
theorem lim_eq_lim_of_equiv {f g : CauSeq β abv} (h : f ≈ g) : lim f = lim g :=
  sorry

@[simp]
theorem lim_const (x : β) : lim (const abv x) = x :=
  lim_eq_of_equiv_const <| Setoid.refl _

@[target]
theorem lim_add (f g : CauSeq β abv) : lim f + lim g = lim (f + g) :=
  sorry

@[target]
theorem lim_mul_lim (f g : CauSeq β abv) : lim f * lim g = lim (f * g) :=
  sorry

@[target]
theorem lim_mul (f : CauSeq β abv) (x : β) : lim f * x = lim (f * const abv x) := by sorry

@[target]
theorem lim_neg (f : CauSeq β abv) : lim (-f) = -lim f :=
  sorry

@[target]
theorem lim_eq_zero_iff (f : CauSeq β abv) : lim f = 0 ↔ LimZero f :=
  sorry

variable {β : Type*} [Field β] {abv : β → α} [IsAbsoluteValue abv] [IsComplete β abv]

@[target]
theorem lim_inv {f : CauSeq β abv} (hf : ¬LimZero f) : lim (inv f hf) = (lim f)⁻¹ :=
  sorry

variable [IsComplete α abs]

@[target]
theorem lim_le {f : CauSeq α abs} {x : α} (h : f ≤ CauSeq.const abs x) : lim f ≤ x :=
  sorry

@[target]
theorem le_lim {f : CauSeq α abs} {x : α} (h : CauSeq.const abs x ≤ f) : x ≤ lim f :=
  sorry

theorem lt_lim {f : CauSeq α abs} {x : α} (h : CauSeq.const abs x < f) : x < lim f :=
  CauSeq.const_lt.1 <| CauSeq.lt_of_lt_of_eq h (equiv_lim f)

@[target]
theorem lim_lt {f : CauSeq α abs} {x : α} (h : f < CauSeq.const abs x) : lim f < x :=
  sorry

end CauSeq
