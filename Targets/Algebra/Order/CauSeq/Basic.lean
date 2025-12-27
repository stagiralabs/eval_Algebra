import VerifiedAgora.tagger
/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.Ring.Pi
import Mathlib.Data.Setoid.Basic
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.Tactic.GCongr

/-!
# Cauchy sequences

A basic theory of Cauchy sequences, used in the construction of the reals and p-adic numbers. Where
applicable, lemmas that will be reused in other contexts have been stated in extra generality.
There are other "versions" of Cauchyness in the library, in particular Cauchy filters in topology.
This is a concrete implementation that is useful for simplicity and computability reasons.

## Important definitions

* `IsCauSeq`: a predicate that says `f : ℕ → β` is Cauchy.
* `CauSeq`: the type of Cauchy sequences valued in type `β` with respect to an absolute value
  function `abv`.

## Tags

sequence, cauchy, abs val, absolute value
-/

assert_not_exists Finset Module Submonoid FloorRing Module

variable {α β : Type*}

open IsAbsoluteValue

section

variable [LinearOrderedField α] [Ring β] (abv : β → α) [IsAbsoluteValue abv]

theorem rat_add_continuous_lemma {ε : α} (ε0 : 0 < ε) :
    ∃ δ > 0, ∀ {a₁ a₂ b₁ b₂ : β}, abv (a₁ - b₁) < δ → abv (a₂ - b₂) < δ →
      abv (a₁ + a₂ - (b₁ + b₂)) < ε :=
  ⟨ε / 2, half_pos ε0, fun {a₁ a₂ b₁ b₂} h₁ h₂ => by
    simpa [add_halves, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      lt_of_le_of_lt (abv_add abv _ _) (add_lt_add h₁ h₂)⟩

@[target]
theorem rat_mul_continuous_lemma {ε K₁ K₂ : α} (ε0 : 0 < ε) :
    ∃ δ > 0, ∀ {a₁ a₂ b₁ b₂ : β}, abv a₁ < K₁ → abv b₂ < K₂ → abv (a₁ - b₁) < δ →
      abv (a₂ - b₂) < δ → abv (a₁ * a₂ - b₁ * b₂) < ε := by sorry

@[target]
theorem rat_inv_continuous_lemma {β : Type*} [DivisionRing β] (abv : β → α) [IsAbsoluteValue abv]
    {ε K : α} (ε0 : 0 < ε) (K0 : 0 < K) :
    ∃ δ > 0, ∀ {a b : β}, K ≤ abv a → K ≤ abv b → abv (a - b) < δ → abv (a⁻¹ - b⁻¹) < ε := by sorry
def IsCauSeq {α : Type*} [LinearOrderedField α] {β : Type*} [Ring β] (abv : β → α) (f : ℕ → β) :
    Prop :=
  ∀ ε > 0, ∃ i, ∀ j ≥ i, abv (f j - f i) < ε

namespace IsCauSeq

variable [LinearOrderedField α] [Ring β] {abv : β → α} [IsAbsoluteValue abv] {f g : ℕ → β}

-- see Note [nolint_ge]
--@[nolint ge_or_gt] -- Porting note: restore attribute
theorem cauchy₂ (hf : IsCauSeq abv f) {ε : α} (ε0 : 0 < ε) :
    ∃ i, ∀ j ≥ i, ∀ k ≥ i, abv (f j - f k) < ε := by
  refine (hf _ (half_pos ε0)).imp fun i hi j ij k ik => ?_
  rw [← add_halves ε]
  refine lt_of_le_of_lt (abv_sub_le abv _ _ _) (add_lt_add (hi _ ij) ?_)
  rw [abv_sub abv]; exact hi _ ik

theorem cauchy₃ (hf : IsCauSeq abv f) {ε : α} (ε0 : 0 < ε) :
    ∃ i, ∀ j ≥ i, ∀ k ≥ j, abv (f k - f j) < ε :=
  let ⟨i, H⟩ := hf.cauchy₂ ε0
  ⟨i, fun _ ij _ jk => H _ (le_trans ij jk) _ ij⟩

lemma bounded (hf : IsCauSeq abv f) : ∃ r, ∀ i, abv (f i) < r := by
  obtain ⟨i, h⟩ := hf _ zero_lt_one
  set R : ℕ → α := @Nat.rec (fun _ => α) (abv (f 0)) fun i c => max c (abv (f i.succ)) with hR
  have : ∀ i, ∀ j ≤ i, abv (f j) ≤ R i := by
    refine Nat.rec (by simp [hR]) ?_
    rintro i hi j (rfl | hj)
    · simp [R]
    · exact (hi j hj).trans (le_max_left _ _)
  refine ⟨R i + 1, fun j ↦ ?_⟩
  obtain hji | hij := le_total j i
  · exact (this i _ hji).trans_lt (lt_add_one _)
  · simpa using (abv_add abv _ _).trans_lt <| add_lt_add_of_le_of_lt (this i _ le_rfl) (h _ hij)

lemma bounded' (hf : IsCauSeq abv f) (x : α) : ∃ r > x, ∀ i, abv (f i) < r :=
  let ⟨r, h⟩ := hf.bounded
  ⟨max r (x + 1), (lt_add_one x).trans_le (le_max_right _ _),
    fun i ↦ (h i).trans_le (le_max_left _ _)⟩

@[target]
lemma const (x : β) : IsCauSeq abv fun _ ↦ x :=
  sorry

@[target]
theorem add (hf : IsCauSeq abv f) (hg : IsCauSeq abv g) : IsCauSeq abv (f + g) := sorry

lemma mul (hf : IsCauSeq abv f) (hg : IsCauSeq abv g) : IsCauSeq abv (f * g) := fun _ ε0 =>
  let ⟨_, _, hF⟩ := hf.bounded' 0
  let ⟨_, _, hG⟩ := hg.bounded' 0
  let ⟨_, δ0, Hδ⟩ := rat_mul_continuous_lemma abv ε0
  let ⟨i, H⟩ := exists_forall_ge_and (hf.cauchy₃ δ0) (hg.cauchy₃ δ0)
  ⟨i, fun j ij =>
    let ⟨H₁, H₂⟩ := H _ le_rfl
    Hδ (hF j) (hG i) (H₁ _ ij) (H₂ _ ij)⟩

@[simp] lemma _root_.isCauSeq_neg : IsCauSeq abv (-f) ↔ IsCauSeq abv f := by
  simp only [IsCauSeq, Pi.neg_apply, ← neg_sub', abv_neg]

protected alias ⟨of_neg, neg⟩ := isCauSeq_neg

end IsCauSeq

/-- `CauSeq β abv` is the type of `β`-valued Cauchy sequences, with respect to the absolute value
function `abv`. -/
def CauSeq {α : Type*} [LinearOrderedField α] (β : Type*) [Ring β] (abv : β → α) : Type _ :=
  { f : ℕ → β // IsCauSeq abv f }

namespace CauSeq

variable [LinearOrderedField α]

section Ring

variable [Ring β] {abv : β → α}

instance : CoeFun (CauSeq β abv) fun _ => ℕ → β :=
  ⟨Subtype.val⟩

@[target, ext]
theorem ext {f g : CauSeq β abv} (h : ∀ i, f i = g i) : f = g := sorry

theorem isCauSeq (f : CauSeq β abv) : IsCauSeq abv f :=
  f.2

theorem cauchy (f : CauSeq β abv) : ∀ {ε}, 0 < ε → ∃ i, ∀ j ≥ i, abv (f j - f i) < ε := @f.2

/-- Given a Cauchy sequence `f`, create a Cauchy sequence from a sequence `g` with
the same values as `f`. -/
def ofEq (f : CauSeq β abv) (g : ℕ → β) (e : ∀ i, f i = g i) : CauSeq β abv :=
  ⟨g, fun ε => by rw [show g = f from (funext e).symm]; exact f.cauchy⟩

variable [IsAbsoluteValue abv]

-- see Note [nolint_ge]
-- @[nolint ge_or_gt] -- Porting note: restore attribute
@[target]
theorem cauchy₂ (f : CauSeq β abv) {ε} :
    0 < ε → ∃ i, ∀ j ≥ i, ∀ k ≥ i, abv (f j - f k) < ε :=
  sorry

@[target]
theorem cauchy₃ (f : CauSeq β abv) {ε} : 0 < ε → ∃ i, ∀ j ≥ i, ∀ k ≥ j, abv (f k - f j) < ε :=
  sorry

theorem bounded (f : CauSeq β abv) : ∃ r, ∀ i, abv (f i) < r := f.2.bounded

@[target]
theorem bounded' (f : CauSeq β abv) (x : α) : ∃ r > x, ∀ i, abv (f i) < r := sorry

instance : Add (CauSeq β abv) :=
  ⟨fun f g => ⟨f + g, f.2.add g.2⟩⟩

@[target, simp, norm_cast]
theorem coe_add (f g : CauSeq β abv) : ⇑(f + g) = (f : ℕ → β) + g :=
  sorry

@[target, simp, norm_cast]
theorem add_apply (f g : CauSeq β abv) (i : ℕ) : (f + g) i = f i + g i :=
  sorry

variable (abv) in
/-- The constant Cauchy sequence. -/
def const (x : β) : CauSeq β abv := ⟨fun _ ↦ x, IsCauSeq.const _⟩

/-- The constant Cauchy sequence -/
local notation "const" => const abv

@[simp, norm_cast]
theorem coe_const (x : β) : (const x : ℕ → β) = Function.const ℕ x :=
  rfl

@[target, simp, norm_cast]
theorem const_apply (x : β) (i : ℕ) : (const x : ℕ → β) i = x :=
  sorry

@[target]
theorem const_inj {x y : β} : (const x : CauSeq β abv) = const y ↔ x = y :=
  sorry

instance : Zero (CauSeq β abv) :=
  ⟨const 0⟩

instance : One (CauSeq β abv) :=
  ⟨const 1⟩

instance : Inhabited (CauSeq β abv) :=
  ⟨0⟩

@[target, simp, norm_cast]
theorem coe_zero : ⇑(0 : CauSeq β abv) = 0 :=
  sorry

@[target, simp, norm_cast]
theorem coe_one : ⇑(1 : CauSeq β abv) = 1 :=
  sorry

@[simp, norm_cast]
theorem zero_apply (i) : (0 : CauSeq β abv) i = 0 :=
  rfl

@[target, simp, norm_cast]
theorem one_apply (i) : (1 : CauSeq β abv) i = 1 :=
  sorry

@[simp]
theorem const_zero : const 0 = 0 :=
  rfl

@[target, simp]
theorem const_one : const 1 = 1 :=
  sorry

@[target]
theorem const_add (x y : β) : const (x + y) = const x + const y :=
  sorry

instance : Mul (CauSeq β abv) := ⟨fun f g ↦ ⟨f * g, f.2.mul g.2⟩⟩

@[target, simp, norm_cast]
theorem coe_mul (f g : CauSeq β abv) : ⇑(f * g) = (f : ℕ → β) * g :=
  sorry

@[target, simp, norm_cast]
theorem mul_apply (f g : CauSeq β abv) (i : ℕ) : (f * g) i = f i * g i :=
  sorry

@[target]
theorem const_mul (x y : β) : const (x * y) = const x * const y :=
  sorry

instance : Neg (CauSeq β abv) := ⟨fun f ↦ ⟨-f, f.2.neg⟩⟩

@[target, simp, norm_cast]
theorem coe_neg (f : CauSeq β abv) : ⇑(-f) = -f :=
  sorry

@[simp, norm_cast]
theorem neg_apply (f : CauSeq β abv) (i) : (-f) i = -f i :=
  rfl

@[target]
theorem const_neg (x : β) : const (-x) = -const x :=
  sorry

instance : Sub (CauSeq β abv) :=
  ⟨fun f g => ofEq (f + -g) (fun x => f x - g x) fun i => by simp [sub_eq_add_neg]⟩

@[simp, norm_cast]
theorem coe_sub (f g : CauSeq β abv) : ⇑(f - g) = (f : ℕ → β) - g :=
  rfl

@[simp, norm_cast]
theorem sub_apply (f g : CauSeq β abv) (i : ℕ) : (f - g) i = f i - g i :=
  rfl

theorem const_sub (x y : β) : const (x - y) = const x - const y :=
  rfl

section SMul

variable {G : Type*} [SMul G β] [IsScalarTower G β β]

instance : SMul G (CauSeq β abv) :=
  ⟨fun a f => (ofEq (const (a • (1 : β)) * f) (a • (f : ℕ → β))) fun _ => smul_one_mul _ _⟩

@[target, simp, norm_cast]
theorem coe_smul (a : G) (f : CauSeq β abv) : ⇑(a • f) = a • (f : ℕ → β) :=
  sorry

@[simp, norm_cast]
theorem smul_apply (a : G) (f : CauSeq β abv) (i : ℕ) : (a • f) i = a • f i :=
  rfl

@[target]
theorem const_smul (a : G) (x : β) : const (a • x) = a • const x :=
  sorry

instance : IsScalarTower G (CauSeq β abv) (CauSeq β abv) :=
  ⟨fun a f g => Subtype.ext <| smul_assoc a (f : ℕ → β) (g : ℕ → β)⟩

end SMul

instance addGroup : AddGroup (CauSeq β abv) :=
  Function.Injective.addGroup Subtype.val Subtype.val_injective rfl coe_add coe_neg coe_sub
    (fun _ _ => coe_smul _ _) fun _ _ => coe_smul _ _

instance instNatCast : NatCast (CauSeq β abv) := ⟨fun n => const n⟩

instance instIntCast : IntCast (CauSeq β abv) := ⟨fun n => const n⟩

instance addGroupWithOne : AddGroupWithOne (CauSeq β abv) :=
  Function.Injective.addGroupWithOne Subtype.val Subtype.val_injective rfl rfl
  coe_add coe_neg coe_sub
  (by intros; rfl)
  (by intros; rfl)
  (by intros; rfl)
  (by intros; rfl)

instance : Pow (CauSeq β abv) ℕ :=
  ⟨fun f n =>
    (ofEq (npowRec n f) fun i => f i ^ n) <| by induction n <;> simp [*, npowRec, pow_succ]⟩

@[target, simp, norm_cast]
theorem coe_pow (f : CauSeq β abv) (n : ℕ) : ⇑(f ^ n) = (f : ℕ → β) ^ n :=
  sorry

@[simp, norm_cast]
theorem pow_apply (f : CauSeq β abv) (n i : ℕ) : (f ^ n) i = f i ^ n :=
  rfl

@[target]
theorem const_pow (x : β) (n : ℕ) : const (x ^ n) = const x ^ n :=
  sorry

instance ring : Ring (CauSeq β abv) :=
  Function.Injective.ring Subtype.val Subtype.val_injective rfl rfl coe_add coe_mul coe_neg coe_sub
    (fun _ _ => coe_smul _ _) (fun _ _ => coe_smul _ _) coe_pow (fun _ => rfl) fun _ => rfl

instance {β : Type*} [CommRing β] {abv : β → α} [IsAbsoluteValue abv] : CommRing (CauSeq β abv) :=
  { CauSeq.ring with
    mul_comm := fun a b => ext fun n => by simp [mul_left_comm, mul_comm] }

/-- `LimZero f` holds when `f` approaches 0. -/
def LimZero {abv : β → α} (f : CauSeq β abv) : Prop :=
  ∀ ε > 0, ∃ i, ∀ j ≥ i, abv (f j) < ε

@[target]
theorem add_limZero {f g : CauSeq β abv} (hf : LimZero f) (hg : LimZero g) : LimZero (f + g)
  | ε, ε0 =>
    (exists_forall_ge_and (hf _ <| half_pos ε0) (hg _ <| half_pos ε0)).imp fun _ H j ij => by
      let ⟨H₁, H₂⟩ := sorry

@[target]
theorem mul_limZero_right (f : CauSeq β abv) {g} (hg : LimZero g) : LimZero (f * g)
  | ε, ε0 =>
    let ⟨F, F0, hF⟩ := sorry

@[target]
theorem mul_limZero_left {f} (g : CauSeq β abv) (hg : LimZero f) : LimZero (f * g)
  | ε, ε0 =>
    let ⟨G, G0, hG⟩ := sorry

theorem neg_limZero {f : CauSeq β abv} (hf : LimZero f) : LimZero (-f) := by
  rw [← neg_one_mul f]
  exact mul_limZero_right _ hf

@[target]
theorem sub_limZero {f g : CauSeq β abv} (hf : LimZero f) (hg : LimZero g) : LimZero (f - g) := by sorry

@[target]
theorem limZero_sub_rev {f g : CauSeq β abv} (hfg : LimZero (f - g)) : LimZero (g - f) := by sorry

@[target]
theorem zero_limZero : LimZero (0 : CauSeq β abv)
  | ε, ε0 => ⟨0, fun j _ => by simpa [abv_zero abv] using ε0⟩

theorem const_limZero {x : β} : LimZero (const x) ↔ x = 0 :=
  sorry

instance equiv : Setoid (CauSeq β abv) :=
  ⟨fun f g => LimZero (f - g),
    ⟨fun f => by simp [zero_limZero],
    fun f ε hε => by simpa using neg_limZero f ε hε,
    fun fg gh => by simpa using add_limZero fg gh⟩⟩

@[target]
theorem add_equiv_add {f1 f2 g1 g2 : CauSeq β abv} (hf : f1 ≈ f2) (hg : g1 ≈ g2) :
    f1 + g1 ≈ f2 + g2 := by sorry

theorem neg_equiv_neg {f g : CauSeq β abv} (hf : f ≈ g) : -f ≈ -g := by
  simpa only [neg_sub'] using neg_limZero hf

theorem sub_equiv_sub {f1 f2 g1 g2 : CauSeq β abv} (hf : f1 ≈ f2) (hg : g1 ≈ g2) :
    f1 - g1 ≈ f2 - g2 := by simpa only [sub_eq_add_neg] using add_equiv_add hf (neg_equiv_neg hg)

@[target]
theorem equiv_def₃ {f g : CauSeq β abv} (h : f ≈ g) {ε : α} (ε0 : 0 < ε) :
    ∃ i, ∀ j ≥ i, ∀ k ≥ j, abv (f k - g j) < ε :=
  sorry

@[target]
theorem limZero_congr {f g : CauSeq β abv} (h : f ≈ g) : LimZero f ↔ LimZero g :=
  sorry

theorem abv_pos_of_not_limZero {f : CauSeq β abv} (hf : ¬LimZero f) :
    ∃ K > 0, ∃ i, ∀ j ≥ i, K ≤ abv (f j) := by
  haveI := Classical.propDecidable
  by_contra nk
  refine hf fun ε ε0 => ?_
  simp? [not_forall] at nk says
    simp only [gt_iff_lt, ge_iff_le, not_exists, not_and, not_forall, Classical.not_imp,
      not_le] at nk
  obtain ⟨i, hi⟩ := f.cauchy₃ (half_pos ε0)
  rcases nk _ (half_pos ε0) i with ⟨j, ij, hj⟩
  refine ⟨j, fun k jk => ?_⟩
  have := lt_of_le_of_lt (abv_add abv _ _) (add_lt_add (hi j ij k jk) hj)
  rwa [sub_add_cancel, add_halves] at this

theorem of_near (f : ℕ → β) (g : CauSeq β abv) (h : ∀ ε > 0, ∃ i, ∀ j ≥ i, abv (f j - g j) < ε) :
    IsCauSeq abv f
  | ε, ε0 =>
    let ⟨i, hi⟩ := exists_forall_ge_and (h _ (half_pos <| half_pos ε0)) (g.cauchy₃ <| half_pos ε0)
    ⟨i, fun j ij => by
      obtain ⟨h₁, h₂⟩ := hi _ le_rfl; rw [abv_sub abv] at h₁
      have := lt_of_le_of_lt (abv_add abv _ _) (add_lt_add (hi _ ij).1 h₁)
      have := lt_of_le_of_lt (abv_add abv _ _) (add_lt_add this (h₂ _ ij))
      rwa [add_halves, add_halves, add_right_comm, sub_add_sub_cancel, sub_add_sub_cancel] at this⟩

theorem not_limZero_of_not_congr_zero {f : CauSeq _ abv} (hf : ¬f ≈ 0) : ¬LimZero f := by
  intro h
  have : LimZero (f - 0) := by simp [h]
  exact hf this

theorem mul_equiv_zero (g : CauSeq _ abv) {f : CauSeq _ abv} (hf : f ≈ 0) : g * f ≈ 0 :=
  have : LimZero (f - 0) := hf
  have : LimZero (g * f) := mul_limZero_right _ <| by simpa
  show LimZero (g * f - 0) by simpa

@[target]
theorem mul_equiv_zero' (g : CauSeq _ abv) {f : CauSeq _ abv} (hf : f ≈ 0) : f * g ≈ 0 :=
  sorry

@[target]
theorem mul_not_equiv_zero {f g : CauSeq _ abv} (hf : ¬f ≈ 0) (hg : ¬g ≈ 0) : ¬f * g ≈ 0 :=
  sorry

@[target]
theorem const_equiv {x y : β} : const x ≈ const y ↔ x = y :=
  sorry

@[target]
theorem mul_equiv_mul {f1 f2 g1 g2 : CauSeq β abv} (hf : f1 ≈ f2) (hg : g1 ≈ g2) :
    f1 * g1 ≈ f2 * g2 := by sorry

theorem smul_equiv_smul {G : Type*} [SMul G β] [IsScalarTower G β β] {f1 f2 : CauSeq β abv} (c : G)
    (hf : f1 ≈ f2) : c • f1 ≈ c • f2 := by
  simpa [const_smul, smul_one_mul _ _] using
    mul_equiv_mul (const_equiv.mpr <| Eq.refl <| c • (1 : β)) hf

@[target]
theorem pow_equiv_pow {f1 f2 : CauSeq β abv} (hf : f1 ≈ f2) (n : ℕ) : f1 ^ n ≈ f2 ^ n := by sorry

end Ring

section IsDomain

variable [Ring β] [IsDomain β] (abv : β → α) [IsAbsoluteValue abv]

@[target]
theorem one_not_equiv_zero : ¬const abv 1 ≈ const abv 0 := sorry

end IsDomain

section DivisionRing

variable [DivisionRing β] {abv : β → α} [IsAbsoluteValue abv]

@[target]
theorem inv_aux {f : CauSeq β abv} (hf : ¬LimZero f) :
    ∀ ε > 0, ∃ i, ∀ j ≥ i, abv ((f j)⁻¹ - (f i)⁻¹) < ε
  | _, ε0 =>
    let ⟨_, K0, HK⟩ := sorry
def inv (f : CauSeq β abv) (hf : ¬LimZero f) : CauSeq β abv :=
  ⟨_, inv_aux hf⟩

@[target, simp, norm_cast]
theorem coe_inv {f : CauSeq β abv} (hf) : ⇑(inv f hf) = (f : ℕ → β)⁻¹ :=
  sorry

@[target, simp, norm_cast]
theorem inv_apply {f : CauSeq β abv} (hf i) : inv f hf i = (f i)⁻¹ :=
  sorry

@[target]
theorem inv_mul_cancel {f : CauSeq β abv} (hf) : inv f hf * f ≈ 1 := sorry

theorem mul_inv_cancel {f : CauSeq β abv} (hf) : f * inv f hf ≈ 1 := fun ε ε0 =>
  let ⟨K, K0, i, H⟩ := abv_pos_of_not_limZero hf
  ⟨i, fun j ij => by simpa [(abv_pos abv).1 (lt_of_lt_of_le K0 (H _ ij)), abv_zero abv] using ε0⟩

@[target]
theorem const_inv {x : β} (hx : x ≠ 0) :
    const abv x⁻¹ = inv (const abv x) (by rwa [const_limZero]) :=
  sorry

end DivisionRing

section Abs

/-- The constant Cauchy sequence -/
local notation "const" => const abs

/-- The entries of a positive Cauchy sequence eventually have a positive lower bound. -/
def Pos (f : CauSeq α abs) : Prop :=
  ∃ K > 0, ∃ i, ∀ j ≥ i, K ≤ f j

@[target]
theorem not_limZero_of_pos {f : CauSeq α abs} : Pos f → ¬LimZero f
  | ⟨_, F0, hF⟩, H =>
    let ⟨_, h⟩ := sorry

theorem const_pos {x : α} : Pos (const x) ↔ 0 < x :=
  ⟨fun ⟨_, K0, _, h⟩ => lt_of_lt_of_le K0 (h _ le_rfl), fun h => ⟨x, h, 0, fun _ _ => le_rfl⟩⟩

theorem add_pos {f g : CauSeq α abs} : Pos f → Pos g → Pos (f + g)
  | ⟨_, F0, hF⟩, ⟨_, G0, hG⟩ =>
    let ⟨i, h⟩ := exists_forall_ge_and hF hG
    ⟨_, _root_.add_pos F0 G0, i, fun _ ij =>
      let ⟨h₁, h₂⟩ := h _ ij
      add_le_add h₁ h₂⟩

@[target]
theorem pos_add_limZero {f g : CauSeq α abs} : Pos f → LimZero g → Pos (f + g)
  | ⟨F, F0, hF⟩, H =>
    let ⟨i, h⟩ := sorry

theorem trichotomy (f : CauSeq α abs) : Pos f ∨ LimZero f ∨ Pos (-f) := by
  rcases Classical.em (LimZero f) with h | h <;> simp [*]
  rcases abv_pos_of_not_limZero h with ⟨K, K0, hK⟩
  rcases exists_forall_ge_and hK (f.cauchy₃ K0) with ⟨i, hi⟩
  refine (le_total 0 (f i)).imp ?_ ?_ <;>
    refine fun h => ⟨K, K0, i, fun j ij => ?_⟩ <;>
    have := (hi _ ij).1 <;>
    obtain ⟨h₁, h₂⟩ := hi _ le_rfl
  · rwa [abs_of_nonneg] at this
    rw [abs_of_nonneg h] at h₁
    exact
      (le_add_iff_nonneg_right _).1
        (le_trans h₁ <| neg_le_sub_iff_le_add'.1 <| le_of_lt (abs_lt.1 <| h₂ _ ij).1)
  · rwa [abs_of_nonpos] at this
    rw [abs_of_nonpos h] at h₁
    rw [← sub_le_sub_iff_right, zero_sub]
    exact le_trans (le_of_lt (abs_lt.1 <| h₂ _ ij).2) h₁

instance : LT (CauSeq α abs) :=
  ⟨fun f g => Pos (g - f)⟩

instance : LE (CauSeq α abs) :=
  ⟨fun f g => f < g ∨ f ≈ g⟩

@[target]
theorem lt_of_lt_of_eq {f g h : CauSeq α abs} (fg : f < g) (gh : g ≈ h) : f < h :=
  sorry

theorem lt_of_eq_of_lt {f g h : CauSeq α abs} (fg : f ≈ g) (gh : g < h) : f < h := by
  have := pos_add_limZero gh (neg_limZero fg)
  rwa [← sub_eq_add_neg, sub_sub_sub_cancel_right] at this

@[target]
theorem lt_trans {f g h : CauSeq α abs} (fg : f < g) (gh : g < h) : f < h :=
  sorry

theorem lt_irrefl {f : CauSeq α abs} : ¬f < f
  | h => not_limZero_of_pos h (by simp [zero_limZero])

theorem le_of_eq_of_le {f g h : CauSeq α abs} (hfg : f ≈ g) (hgh : g ≤ h) : f ≤ h :=
  hgh.elim (Or.inl ∘ CauSeq.lt_of_eq_of_lt hfg) (Or.inr ∘ Setoid.trans hfg)

theorem le_of_le_of_eq {f g h : CauSeq α abs} (hfg : f ≤ g) (hgh : g ≈ h) : f ≤ h :=
  hfg.elim (fun h => Or.inl (CauSeq.lt_of_lt_of_eq h hgh)) fun h => Or.inr (Setoid.trans h hgh)

instance : Preorder (CauSeq α abs) where
  lt := (· < ·)
  le f g := f < g ∨ f ≈ g
  le_refl _ := Or.inr (Setoid.refl _)
  le_trans _ _ _ fg gh :=
    match fg, gh with
    | Or.inl fg, Or.inl gh => Or.inl <| lt_trans fg gh
    | Or.inl fg, Or.inr gh => Or.inl <| lt_of_lt_of_eq fg gh
    | Or.inr fg, Or.inl gh => Or.inl <| lt_of_eq_of_lt fg gh
    | Or.inr fg, Or.inr gh => Or.inr <| Setoid.trans fg gh
  lt_iff_le_not_le _ _ :=
    ⟨fun h => ⟨Or.inl h, not_or_intro (mt (lt_trans h) lt_irrefl) (not_limZero_of_pos h)⟩,
      fun ⟨h₁, h₂⟩ => h₁.resolve_right (mt (fun h => Or.inr (Setoid.symm h)) h₂)⟩

theorem le_antisymm {f g : CauSeq α abs} (fg : f ≤ g) (gf : g ≤ f) : f ≈ g :=
  fg.resolve_left (not_lt_of_le gf)

@[target]
theorem lt_total (f g : CauSeq α abs) : f < g ∨ f ≈ g ∨ g < f :=
  sorry

@[target]
theorem le_total (f g : CauSeq α abs) : f ≤ g ∨ g ≤ f :=
  sorry

@[target]
theorem const_lt {x y : α} : const x < const y ↔ x < y :=
  sorry

@[target]
theorem const_le {x y : α} : const x ≤ const y ↔ x ≤ y := by sorry

@[target]
theorem le_of_exists {f g : CauSeq α abs} (h : ∃ i, ∀ j ≥ i, f j ≤ g j) : f ≤ g :=
  sorry

theorem exists_gt (f : CauSeq α abs) : ∃ a : α, f < const a :=
  let ⟨K, H⟩ := f.bounded
  ⟨K + 1, 1, zero_lt_one, 0, fun i _ => by
    rw [sub_apply, const_apply, le_sub_iff_add_le', add_le_add_iff_right]
    exact le_of_lt (abs_lt.1 (H _)).2⟩

theorem exists_lt (f : CauSeq α abs) : ∃ a : α, const a < f :=
  let ⟨a, h⟩ := (-f).exists_gt
  ⟨-a, show Pos _ by rwa [const_neg, sub_neg_eq_add, add_comm, ← sub_neg_eq_add]⟩

-- so named to match `rat_add_continuous_lemma`
theorem rat_sup_continuous_lemma {ε : α} {a₁ a₂ b₁ b₂ : α} :
    abs (a₁ - b₁) < ε → abs (a₂ - b₂) < ε → abs (a₁ ⊔ a₂ - b₁ ⊔ b₂) < ε := fun h₁ h₂ =>
  (abs_max_sub_max_le_max _ _ _ _).trans_lt (max_lt h₁ h₂)

-- so named to match `rat_add_continuous_lemma`
theorem rat_inf_continuous_lemma {ε : α} {a₁ a₂ b₁ b₂ : α} :
    abs (a₁ - b₁) < ε → abs (a₂ - b₂) < ε → abs (a₁ ⊓ a₂ - b₁ ⊓ b₂) < ε := fun h₁ h₂ =>
  (abs_min_sub_min_le_max _ _ _ _).trans_lt (max_lt h₁ h₂)

instance : Max (CauSeq α abs) :=
  ⟨fun f g =>
    ⟨f ⊔ g, fun _ ε0 =>
      (exists_forall_ge_and (f.cauchy₃ ε0) (g.cauchy₃ ε0)).imp fun _ H _ ij =>
        let ⟨H₁, H₂⟩ := H _ le_rfl
        rat_sup_continuous_lemma (H₁ _ ij) (H₂ _ ij)⟩⟩

instance : Min (CauSeq α abs) :=
  ⟨fun f g =>
    ⟨f ⊓ g, fun _ ε0 =>
      (exists_forall_ge_and (f.cauchy₃ ε0) (g.cauchy₃ ε0)).imp fun _ H _ ij =>
        let ⟨H₁, H₂⟩ := H _ le_rfl
        rat_inf_continuous_lemma (H₁ _ ij) (H₂ _ ij)⟩⟩

@[target, simp, norm_cast]
theorem coe_sup (f g : CauSeq α abs) : ⇑(f ⊔ g) = (f : ℕ → α) ⊔ g :=
  sorry

@[target, simp, norm_cast]
theorem coe_inf (f g : CauSeq α abs) : ⇑(f ⊓ g) = (f : ℕ → α) ⊓ g :=
  sorry

@[target]
theorem sup_limZero {f g : CauSeq α abs} (hf : LimZero f) (hg : LimZero g) : LimZero (f ⊔ g)
  | ε, ε0 =>
    (exists_forall_ge_and (hf _ ε0) (hg _ ε0)).imp fun _ H j ij => by
      let ⟨H₁, H₂⟩ := sorry

@[target]
theorem inf_limZero {f g : CauSeq α abs} (hf : LimZero f) (hg : LimZero g) : LimZero (f ⊓ g)
  | ε, ε0 =>
    (exists_forall_ge_and (hf _ ε0) (hg _ ε0)).imp fun _ H j ij => by
      let ⟨H₁, H₂⟩ := sorry

@[target]
theorem sup_equiv_sup {a₁ b₁ a₂ b₂ : CauSeq α abs} (ha : a₁ ≈ a₂) (hb : b₁ ≈ b₂) :
    a₁ ⊔ b₁ ≈ a₂ ⊔ b₂ := by sorry

theorem inf_equiv_inf {a₁ b₁ a₂ b₂ : CauSeq α abs} (ha : a₁ ≈ a₂) (hb : b₁ ≈ b₂) :
    a₁ ⊓ b₁ ≈ a₂ ⊓ b₂ := by
  intro ε ε0
  obtain ⟨ai, hai⟩ := ha ε ε0
  obtain ⟨bi, hbi⟩ := hb ε ε0
  exact
    ⟨ai ⊔ bi, fun i hi =>
      (abs_min_sub_min_le_max (a₁ i) (b₁ i) (a₂ i) (b₂ i)).trans_lt
        (max_lt (hai i (sup_le_iff.mp hi).1) (hbi i (sup_le_iff.mp hi).2))⟩

protected theorem sup_lt {a b c : CauSeq α abs} (ha : a < c) (hb : b < c) : a ⊔ b < c := by
  obtain ⟨⟨εa, εa0, ia, ha⟩, ⟨εb, εb0, ib, hb⟩⟩ := ha, hb
  refine ⟨εa ⊓ εb, lt_inf_iff.mpr ⟨εa0, εb0⟩, ia ⊔ ib, fun i hi => ?_⟩
  have := min_le_min (ha _ (sup_le_iff.mp hi).1) (hb _ (sup_le_iff.mp hi).2)
  exact this.trans_eq (min_sub_sub_left _ _ _)

protected theorem lt_inf {a b c : CauSeq α abs} (hb : a < b) (hc : a < c) : a < b ⊓ c := by
  obtain ⟨⟨εb, εb0, ib, hb⟩, ⟨εc, εc0, ic, hc⟩⟩ := hb, hc
  refine ⟨εb ⊓ εc, lt_inf_iff.mpr ⟨εb0, εc0⟩, ib ⊔ ic, fun i hi => ?_⟩
  have := min_le_min (hb _ (sup_le_iff.mp hi).1) (hc _ (sup_le_iff.mp hi).2)
  exact this.trans_eq (min_sub_sub_right _ _ _)

@[simp]
protected theorem sup_idem (a : CauSeq α abs) : a ⊔ a = a := Subtype.ext (sup_idem _)

@[simp]
protected theorem inf_idem (a : CauSeq α abs) : a ⊓ a = a := Subtype.ext (inf_idem _)

protected theorem sup_comm (a b : CauSeq α abs) : a ⊔ b = b ⊔ a := Subtype.ext (sup_comm _ _)

protected theorem inf_comm (a b : CauSeq α abs) : a ⊓ b = b ⊓ a := Subtype.ext (inf_comm _ _)

protected theorem sup_eq_right {a b : CauSeq α abs} (h : a ≤ b) : a ⊔ b ≈ b := by
  obtain ⟨ε, ε0 : _ < _, i, h⟩ | h := h
  · intro _ _
    refine ⟨i, fun j hj => ?_⟩
    dsimp
    rw [← max_sub_sub_right]
    rwa [sub_self, max_eq_right, abs_zero]
    rw [sub_nonpos, ← sub_nonneg]
    exact ε0.le.trans (h _ hj)
  · refine Setoid.trans (sup_equiv_sup h (Setoid.refl _)) ?_
    rw [CauSeq.sup_idem]

protected theorem inf_eq_right {a b : CauSeq α abs} (h : b ≤ a) : a ⊓ b ≈ b := by
  obtain ⟨ε, ε0 : _ < _, i, h⟩ | h := h
  · intro _ _
    refine ⟨i, fun j hj => ?_⟩
    dsimp
    rw [← min_sub_sub_right]
    rwa [sub_self, min_eq_right, abs_zero]
    exact ε0.le.trans (h _ hj)
  · refine Setoid.trans (inf_equiv_inf (Setoid.symm h) (Setoid.refl _)) ?_
    rw [CauSeq.inf_idem]

protected theorem sup_eq_left {a b : CauSeq α abs} (h : b ≤ a) : a ⊔ b ≈ a := by
  simpa only [CauSeq.sup_comm] using CauSeq.sup_eq_right h

protected theorem inf_eq_left {a b : CauSeq α abs} (h : a ≤ b) : a ⊓ b ≈ a := by
  simpa only [CauSeq.inf_comm] using CauSeq.inf_eq_right h

protected theorem le_sup_left {a b : CauSeq α abs} : a ≤ a ⊔ b :=
  le_of_exists ⟨0, fun _ _ => le_sup_left⟩

protected theorem inf_le_left {a b : CauSeq α abs} : a ⊓ b ≤ a :=
  le_of_exists ⟨0, fun _ _ => inf_le_left⟩

protected theorem le_sup_right {a b : CauSeq α abs} : b ≤ a ⊔ b :=
  le_of_exists ⟨0, fun _ _ => le_sup_right⟩

protected theorem inf_le_right {a b : CauSeq α abs} : a ⊓ b ≤ b :=
  le_of_exists ⟨0, fun _ _ => inf_le_right⟩

protected theorem sup_le {a b c : CauSeq α abs} (ha : a ≤ c) (hb : b ≤ c) : a ⊔ b ≤ c := by
  obtain ha | ha := ha
  · obtain hb | hb := hb
    · exact Or.inl (CauSeq.sup_lt ha hb)
    · replace ha := le_of_le_of_eq ha.le (Setoid.symm hb)
      refine le_of_le_of_eq (Or.inr ?_) hb
      exact CauSeq.sup_eq_right ha
  · replace hb := le_of_le_of_eq hb (Setoid.symm ha)
    refine le_of_le_of_eq (Or.inr ?_) ha
    exact CauSeq.sup_eq_left hb

protected theorem le_inf {a b c : CauSeq α abs} (hb : a ≤ b) (hc : a ≤ c) : a ≤ b ⊓ c := by
  obtain hb | hb := hb
  · obtain hc | hc := hc
    · exact Or.inl (CauSeq.lt_inf hb hc)
    · replace hb := le_of_eq_of_le (Setoid.symm hc) hb.le
      refine le_of_eq_of_le hc (Or.inr ?_)
      exact Setoid.symm (CauSeq.inf_eq_right hb)
  · replace hc := le_of_eq_of_le (Setoid.symm hb) hc
    refine le_of_eq_of_le hb (Or.inr ?_)
    exact Setoid.symm (CauSeq.inf_eq_left hc)

/-! Note that `DistribLattice (CauSeq α abs)` is not true because there is no `PartialOrder`. -/


protected theorem sup_inf_distrib_left (a b c : CauSeq α abs) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) :=
  ext fun _ ↦ max_min_distrib_left _ _ _

protected theorem sup_inf_distrib_right (a b c : CauSeq α abs) : a ⊓ b ⊔ c = (a ⊔ c) ⊓ (b ⊔ c) :=
  ext fun _ ↦ max_min_distrib_right _ _ _

end Abs

end CauSeq
