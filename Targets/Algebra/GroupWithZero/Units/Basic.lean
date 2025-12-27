import VerifiedAgora.tagger
/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Lean.Meta.CongrTheorems
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Nontriviality
import Mathlib.Tactic.Spread
import Mathlib.Util.AssertExists

/-!
# Lemmas about units in a `MonoidWithZero` or a `GroupWithZero`.

We also define `Ring.inverse`, a globally defined function on any ring
(in fact any `MonoidWithZero`), which inverts units and sends non-units to zero.
-/

-- Guard against import creep
assert_not_exists DenselyOrdered Equiv Subtype.restrict Multiplicative


variable {α M₀ G₀ : Type*}
variable [MonoidWithZero M₀]

namespace Units

/-- An element of the unit group of a nonzero monoid with zero represented as an element
    of the monoid is nonzero. -/
@[simp]
theorem ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) ≠ 0 :=
  left_ne_zero_of_mul_eq_one u.mul_inv

-- We can't use `mul_eq_zero` + `Units.ne_zero` in the next two lemmas because we don't assume
-- `Nonzero M₀`.
@[simp]
theorem mul_left_eq_zero (u : M₀ˣ) {a : M₀} : a * u = 0 ↔ a = 0 :=
  ⟨fun h => by simpa using mul_eq_zero_of_left h ↑u⁻¹, fun h => mul_eq_zero_of_left h u⟩

@[simp]
theorem mul_right_eq_zero (u : M₀ˣ) {a : M₀} : ↑u * a = 0 ↔ a = 0 :=
  ⟨fun h => by simpa using mul_eq_zero_of_right (↑u⁻¹) h, mul_eq_zero_of_right (u : M₀)⟩

end Units

namespace IsUnit

@[target]
theorem ne_zero [Nontrivial M₀] {a : M₀} (ha : IsUnit a) : a ≠ 0 :=
  sorry

@[target]
theorem mul_right_eq_zero {a b : M₀} (ha : IsUnit a) : a * b = 0 ↔ b = 0 :=
  sorry

@[target]
theorem mul_left_eq_zero {a b : M₀} (hb : IsUnit b) : a * b = 0 ↔ a = 0 :=
  sorry

end IsUnit

@[simp]
theorem isUnit_zero_iff : IsUnit (0 : M₀) ↔ (0 : M₀) = 1 :=
  ⟨fun ⟨⟨_, a, (a0 : 0 * a = 1), _⟩, rfl⟩ => by rwa [zero_mul] at a0, fun h =>
    @isUnit_of_subsingleton _ _ (subsingleton_of_zero_eq_one h) 0⟩

@[target]
theorem not_isUnit_zero [Nontrivial M₀] : ¬IsUnit (0 : M₀) :=
  sorry

namespace Ring

open Classical in
/-- Introduce a function `inverse` on a monoid with zero `M₀`, which sends `x` to `x⁻¹` if `x` is
invertible and to `0` otherwise.  This definition is somewhat ad hoc, but one needs a fully (rather
than partially) defined inverse function for some purposes, including for calculus.

Note that while this is in the `Ring` namespace for brevity, it requires the weaker assumption
`MonoidWithZero M₀` instead of `Ring M₀`. -/
noncomputable def inverse : M₀ → M₀ := fun x => if h : IsUnit x then ((h.unit⁻¹ : M₀ˣ) : M₀) else 0

/-- By definition, if `x` is invertible then `inverse x = x⁻¹`. -/
@[target, simp]
theorem inverse_unit (u : M₀ˣ) : inverse (u : M₀) = (u⁻¹ : M₀ˣ) := by sorry

theorem IsUnit.ringInverse {x : M₀} (h : IsUnit x) : IsUnit (inverse x) :=
  match h with
  | ⟨u, hu⟩ => hu ▸ ⟨u⁻¹, (inverse_unit u).symm⟩

theorem inverse_of_isUnit {x : M₀} (h : IsUnit x) : inverse x = ((h.unit⁻¹ : M₀ˣ) : M₀) := dif_pos h

/-- By definition, if `x` is not invertible then `inverse x = 0`. -/
@[target, simp]
theorem inverse_non_unit (x : M₀) (h : ¬IsUnit x) : inverse x = 0 :=
  sorry

theorem mul_inverse_cancel (x : M₀) (h : IsUnit x) : x * inverse x = 1 := by
  rcases h with ⟨u, rfl⟩
  rw [inverse_unit, Units.mul_inv]

@[target]
theorem inverse_mul_cancel (x : M₀) (h : IsUnit x) : inverse x * x = 1 := by sorry

@[target]
theorem mul_inverse_cancel_right (x y : M₀) (h : IsUnit x) : y * x * inverse x = y := by sorry

theorem inverse_mul_cancel_right (x y : M₀) (h : IsUnit x) : y * inverse x * x = y := by
  rw [mul_assoc, inverse_mul_cancel x h, mul_one]

@[target]
theorem mul_inverse_cancel_left (x y : M₀) (h : IsUnit x) : x * (inverse x * y) = y := by sorry

theorem inverse_mul_cancel_left (x y : M₀) (h : IsUnit x) : inverse x * (x * y) = y := by
  rw [← mul_assoc, inverse_mul_cancel x h, one_mul]

@[target]
theorem inverse_mul_eq_iff_eq_mul (x y z : M₀) (h : IsUnit x) : inverse x * y = z ↔ y = x * z :=
  sorry

theorem eq_mul_inverse_iff_mul_eq (x y z : M₀) (h : IsUnit z) : x = y * inverse z ↔ x * z = y :=
  ⟨fun h1 => by rw [h1, inverse_mul_cancel_right _ _ h],
  fun h1 => by rw [← h1, mul_inverse_cancel_right _ _ h]⟩

variable (M₀)

@[simp]
theorem inverse_one : inverse (1 : M₀) = 1 :=
  inverse_unit 1

@[target, simp]
theorem inverse_zero : inverse (0 : M₀) = 0 := by sorry

variable {M₀}

end Ring

theorem IsUnit.ring_inverse {a : M₀} : IsUnit a → IsUnit (Ring.inverse a)
  | ⟨u, hu⟩ => hu ▸ ⟨u⁻¹, (Ring.inverse_unit u).symm⟩

@[simp]
theorem isUnit_ring_inverse {a : M₀} : IsUnit (Ring.inverse a) ↔ IsUnit a :=
  ⟨fun h => by
    cases subsingleton_or_nontrivial M₀
    · convert h
    · contrapose h
      rw [Ring.inverse_non_unit _ h]
      exact not_isUnit_zero
      ,
    IsUnit.ring_inverse⟩

namespace Units

variable [GroupWithZero G₀]

/-- Embed a non-zero element of a `GroupWithZero` into the unit group.
  By combining this function with the operations on units,
  or the `/ₚ` operation, it is possible to write a division
  as a partial function with three arguments. -/
def mk0 (a : G₀) (ha : a ≠ 0) : G₀ˣ :=
  ⟨a, a⁻¹, mul_inv_cancel₀ ha, inv_mul_cancel₀ ha⟩

@[target, simp]
theorem mk0_one (h := sorry

@[target, simp]
theorem val_mk0 {a : G₀} (h : a ≠ 0) : (mk0 a h : G₀) = a :=
  sorry

@[target, simp]
theorem mk0_val (u : G₀ˣ) (h : (u : G₀) ≠ 0) : mk0 (u : G₀) h = u :=
  sorry

theorem mul_inv' (u : G₀ˣ) : u * (u : G₀)⁻¹ = 1 :=
  mul_inv_cancel₀ u.ne_zero

@[target]
theorem inv_mul' (u : G₀ˣ) : (u⁻¹ : G₀) * u = 1 :=
  sorry

@[simp]
theorem mk0_inj {a b : G₀} (ha : a ≠ 0) (hb : b ≠ 0) : Units.mk0 a ha = Units.mk0 b hb ↔ a = b :=
  ⟨fun h => by injection h, fun h => Units.ext h⟩

/-- In a group with zero, an existential over a unit can be rewritten in terms of `Units.mk0`. -/
theorem exists0 {p : G₀ˣ → Prop} : (∃ g : G₀ˣ, p g) ↔ ∃ (g : G₀) (hg : g ≠ 0), p (Units.mk0 g hg) :=
  ⟨fun ⟨g, pg⟩ => ⟨g, g.ne_zero, (g.mk0_val g.ne_zero).symm ▸ pg⟩,
  fun ⟨g, hg, pg⟩ => ⟨Units.mk0 g hg, pg⟩⟩

/-- An alternative version of `Units.exists0`. This one is useful if Lean cannot
figure out `p` when using `Units.exists0` from right to left. -/
@[target]
theorem exists0' {p : ∀ g : G₀, g ≠ 0 → Prop} :
    (∃ (g : G₀) (hg : g ≠ 0), p g hg) ↔ ∃ g : G₀ˣ, p g g.ne_zero :=
  sorry

@[target, simp]
theorem exists_iff_ne_zero {p : G₀ → Prop} : (∃ u : G₀ˣ, p u) ↔ ∃ x ≠ 0, p x := by sorry

@[target]
theorem _root_.GroupWithZero.eq_zero_or_unit (a : G₀) : a = 0 ∨ ∃ u : G₀ˣ, a = u := by sorry

end Units

section GroupWithZero
variable [GroupWithZero G₀] {a b c : G₀} {m n : ℕ}

@[target]
theorem IsUnit.mk0 (x : G₀) (hx : x ≠ 0) : IsUnit x :=
  sorry

@[simp]
theorem isUnit_iff_ne_zero : IsUnit a ↔ a ≠ 0 :=
  (Units.exists_iff_ne_zero (p := (· = a))).trans (by simp)

alias ⟨_, Ne.isUnit⟩ := isUnit_iff_ne_zero

-- Porting note: can't add this attribute?
-- https://github.com/leanprover-community/mathlib4/issues/740
-- attribute [protected] Ne.is_unit

-- see Note [lower instance priority]
instance (priority := 10) GroupWithZero.noZeroDivisors : NoZeroDivisors G₀ :=
  { (‹_› : GroupWithZero G₀) with
    eq_zero_or_eq_zero_of_mul_eq_zero := @fun a b h => by
      contrapose! h
      exact (Units.mk0 a h.1 * Units.mk0 b h.2).ne_zero }

-- Can't be put next to the other `mk0` lemmas because it depends on the
-- `NoZeroDivisors` instance, which depends on `mk0`.
@[target, simp]
theorem Units.mk0_mul (x y : G₀) (hxy) :
    Units.mk0 (x * y) hxy =
      Units.mk0 x (mul_ne_zero_iff.mp hxy).1 * Units.mk0 y (mul_ne_zero_iff.mp hxy).2 := by sorry

@[target]
theorem div_ne_zero (ha : a ≠ 0) (hb : b ≠ 0) : a / b ≠ 0 := by sorry

@[target, simp]
theorem div_eq_zero_iff : a / b = 0 ↔ a = 0 ∨ b = 0 := by sorry

theorem div_ne_zero_iff : a / b ≠ 0 ↔ a ≠ 0 ∧ b ≠ 0 :=
  div_eq_zero_iff.not.trans not_or

@[simp] lemma div_self (h : a ≠ 0) : a / a = 1 := h.isUnit.div_self

@[target]
lemma eq_mul_inv_iff_mul_eq₀ (hc : c ≠ 0) : a = b * c⁻¹ ↔ a * c = b :=
  sorry

@[target]
lemma eq_inv_mul_iff_mul_eq₀ (hb : b ≠ 0) : a = b⁻¹ * c ↔ b * a = c :=
  sorry

@[target]
lemma inv_mul_eq_iff_eq_mul₀ (ha : a ≠ 0) : a⁻¹ * b = c ↔ b = a * c :=
  sorry

lemma mul_inv_eq_iff_eq_mul₀ (hb : b ≠ 0) : a * b⁻¹ = c ↔ a = c * b :=
  hb.isUnit.mul_inv_eq_iff_eq_mul

@[target]
lemma mul_inv_eq_one₀ (hb : b ≠ 0) : a * b⁻¹ = 1 ↔ a = b := sorry

@[target]
lemma inv_mul_eq_one₀ (ha : a ≠ 0) : a⁻¹ * b = 1 ↔ a = b := sorry

@[target]
lemma mul_eq_one_iff_eq_inv₀ (hb : b ≠ 0) : a * b = 1 ↔ a = b⁻¹ := sorry

lemma mul_eq_one_iff_inv_eq₀ (ha : a ≠ 0) : a * b = 1 ↔ a⁻¹ = b := ha.isUnit.mul_eq_one_iff_inv_eq

/-- A variant of `eq_mul_inv_iff_mul_eq₀` that moves the nonzero hypothesis to another variable. -/
lemma mul_eq_of_eq_mul_inv₀ (ha : a ≠ 0) (h : a = c * b⁻¹) : a * b = c := by
  rwa [← eq_mul_inv_iff_mul_eq₀]; rintro rfl; simp [ha] at h

/-- A variant of `eq_inv_mul_iff_mul_eq₀` that moves the nonzero hypothesis to another variable. -/
@[target]
lemma mul_eq_of_eq_inv_mul₀ (hb : b ≠ 0) (h : b = a⁻¹ * c) : a * b = c := by sorry
@[target]
lemma eq_mul_of_inv_mul_eq₀ (hc : c ≠ 0) (h : b⁻¹ * a = c) : a = b * c := by sorry
lemma eq_mul_of_mul_inv_eq₀ (hb : b ≠ 0) (h : a * c⁻¹ = b) : a = b * c := by
  rwa [← mul_inv_eq_iff_eq_mul₀]; rintro rfl; simp [hb.symm] at h

@[simp] lemma div_mul_cancel₀ (a : G₀) (h : b ≠ 0) : a / b * b = a := h.isUnit.div_mul_cancel _

lemma mul_one_div_cancel (h : a ≠ 0) : a * (1 / a) = 1 := h.isUnit.mul_one_div_cancel

@[target]
lemma one_div_mul_cancel (h : a ≠ 0) : 1 / a * a = 1 := sorry

lemma div_left_inj' (hc : c ≠ 0) : a / c = b / c ↔ a = b := hc.isUnit.div_left_inj

@[field_simps] lemma div_eq_iff (hb : b ≠ 0) : a / b = c ↔ a = c * b := hb.isUnit.div_eq_iff

@[field_simps] lemma eq_div_iff (hb : b ≠ 0) : c = a / b ↔ c * b = a := hb.isUnit.eq_div_iff

-- TODO: Swap RHS around
@[target]
lemma div_eq_iff_mul_eq (hb : b ≠ 0) : a / b = c ↔ c * b = a := sorry

@[target]
lemma eq_div_iff_mul_eq (hc : c ≠ 0) : a = b / c ↔ a * c = b := sorry

lemma div_eq_of_eq_mul (hb : b ≠ 0) : a = c * b → a / b = c := hb.isUnit.div_eq_of_eq_mul

lemma eq_div_of_mul_eq (hc : c ≠ 0) : a * c = b → a = b / c := hc.isUnit.eq_div_of_mul_eq

lemma div_eq_one_iff_eq (hb : b ≠ 0) : a / b = 1 ↔ a = b := hb.isUnit.div_eq_one_iff_eq

@[target]
lemma div_mul_cancel_right₀ (hb : b ≠ 0) (a : G₀) : b / (a * b) = a⁻¹ :=
  sorry

@[target]
lemma mul_div_mul_right (a b : G₀) (hc : c ≠ 0) : a * c / (b * c) = a / b :=
  sorry

-- TODO: Duplicate of `mul_inv_cancel_right₀`
@[target]
lemma mul_mul_div (a : G₀) (hb : b ≠ 0) : a = a * b * (1 / b) := sorry

lemma div_div_div_cancel_right₀ (hc : c ≠ 0) (a b : G₀) : a / c / (b / c) = a / b := by
  rw [div_div_eq_mul_div, div_mul_cancel₀ _ hc]

@[target]
lemma div_mul_div_cancel₀ (hb : b ≠ 0) : a / b * (b / c) = a / c := by sorry

lemma div_mul_cancel_of_imp (h : b = 0 → a = 0) : a / b * b = a := by
  obtain rfl | hb := eq_or_ne b 0 <;>  simp [*]

lemma mul_div_cancel_of_imp (h : b = 0 → a = 0) : a * b / b = a := by
  obtain rfl | hb := eq_or_ne b 0 <;>  simp [*]

@[simp] lemma divp_mk0 (a : G₀) (hb : b ≠ 0) : a /ₚ Units.mk0 b hb = a / b := divp_eq_div _ _

@[target]
lemma pow_sub₀ (a : G₀) (ha : a ≠ 0) (h : n ≤ m) : a ^ (m - n) = a ^ m * (a ^ n)⁻¹ := by sorry

lemma pow_sub_of_lt (a : G₀) (h : n < m) : a ^ (m - n) = a ^ m * (a ^ n)⁻¹ := by
  obtain rfl | ha := eq_or_ne a 0
  · rw [zero_pow (Nat.ne_of_gt <| Nat.sub_pos_of_lt h), zero_pow (by omega), zero_mul]
  · exact pow_sub₀ _ ha <| Nat.le_of_lt h

@[target]
lemma inv_pow_sub₀ (ha : a ≠ 0) (h : n ≤ m) : a⁻¹ ^ (m - n) = (a ^ m)⁻¹ * a ^ n := by sorry

@[target]
lemma inv_pow_sub_of_lt (a : G₀) (h : n < m) : a⁻¹ ^ (m - n) = (a ^ m)⁻¹ * a ^ n := by sorry

lemma zpow_sub₀ (ha : a ≠ 0) (m n : ℤ) : a ^ (m - n) = a ^ m / a ^ n := by
  rw [Int.sub_eq_add_neg, zpow_add₀ ha, zpow_neg, div_eq_mul_inv]

@[target]
lemma zpow_natCast_sub_natCast₀ (ha : a ≠ 0) (m n : ℕ) : a ^ (m - n : ℤ) = a ^ m / a ^ n := by sorry

lemma zpow_natCast_sub_one₀ (ha : a ≠ 0) (n : ℕ) : a ^ (n - 1 : ℤ) = a ^ n / a := by
  simpa using zpow_sub₀ ha n 1

@[target]
lemma zpow_one_sub_natCast₀ (ha : a ≠ 0) (n : ℕ) : a ^ (1 - n : ℤ) = a / a ^ n := by sorry

@[target]
lemma zpow_ne_zero {a : G₀} : ∀ n : ℤ, a ≠ 0 → a ^ n ≠ 0
  | (_ : ℕ) => by rw [zpow_natCast]; exact pow_ne_zero _
  | .negSucc n => fun ha ↦ by rw [zpow_negSucc]; exact inv_ne_zero (pow_ne_zero _ ha)

lemma eq_zero_of_zpow_eq_zero {n : ℤ} : a ^ n = 0 → a = 0 := sorry

@[target]
lemma zpow_eq_zero_iff {n : ℤ} (hn : n ≠ 0) : a ^ n = 0 ↔ a = 0 :=
  sorry

lemma zpow_ne_zero_iff {n : ℤ} (hn : n ≠ 0) : a ^ n ≠ 0 ↔ a ≠ 0 := (zpow_eq_zero_iff hn).ne

lemma zpow_neg_mul_zpow_self (n : ℤ) (ha : a ≠ 0) : a ^ (-n) * a ^ n = 1 := by
  rw [zpow_neg]; exact inv_mul_cancel₀ (zpow_ne_zero n ha)

theorem Ring.inverse_eq_inv (a : G₀) : Ring.inverse a = a⁻¹ := by
  obtain rfl | ha := eq_or_ne a 0
  · simp
  · exact Ring.inverse_unit (Units.mk0 a ha)

@[target, simp]
theorem Ring.inverse_eq_inv' : (Ring.inverse : G₀ → G₀) = Inv.inv :=
  sorry

end GroupWithZero

section CommGroupWithZero

-- comm
variable [CommGroupWithZero G₀] {a b c d : G₀}

-- see Note [lower instance priority]
instance (priority := 10) CommGroupWithZero.toCancelCommMonoidWithZero :
    CancelCommMonoidWithZero G₀ :=
  { GroupWithZero.toCancelMonoidWithZero,
    CommGroupWithZero.toCommMonoidWithZero with }

-- See note [lower instance priority]
instance (priority := 100) CommGroupWithZero.toDivisionCommMonoid :
    DivisionCommMonoid G₀ where
  __ := ‹CommGroupWithZero G₀›
  __ := GroupWithZero.toDivisionMonoid

@[target]
lemma div_mul_cancel_left₀ (ha : a ≠ 0) (b : G₀) : a / (a * b) = b⁻¹ :=
  sorry

lemma mul_div_cancel_left_of_imp (h : a = 0 → b = 0) : a * b / a = b := by
  rw [mul_comm, mul_div_cancel_of_imp h]

@[target]
lemma mul_div_cancel_of_imp' (h : b = 0 → a = 0) : b * (a / b) = a := by sorry

lemma mul_div_cancel₀ (a : G₀) (hb : b ≠ 0) : b * (a / b) = a :=
  hb.isUnit.mul_div_cancel _

@[target]
lemma mul_div_mul_left (a b : G₀) (hc : c ≠ 0) : c * a / (c * b) = a / b :=
  sorry

lemma mul_eq_mul_of_div_eq_div (a c : G₀) (hb : b ≠ 0) (hd : d ≠ 0)
    (h : a / b = c / d) : a * d = c * b := by
  rw [← mul_one a, ← div_self hb, ← mul_comm_div, h, div_mul_eq_mul_div, div_mul_cancel₀ _ hd]

@[field_simps] lemma div_eq_div_iff (hb : b ≠ 0) (hd : d ≠ 0) : a / b = c / d ↔ a * d = c * b :=
  hb.isUnit.div_eq_div_iff hd.isUnit

/-- The `CommGroupWithZero` version of `div_eq_div_iff_div_eq_div`. -/
@[target]
lemma div_eq_div_iff_div_eq_div' (hb : b ≠ 0) (hc : c ≠ 0) : a / b = c / d ↔ a / c = b / d := by sorry

@[simp] lemma div_div_cancel₀ (ha : a ≠ 0) : a / (a / b) = b := ha.isUnit.div_div_cancel

@[deprecated (since := "2024-11-25")] alias div_div_cancel' := div_div_cancel₀

@[target]
lemma div_div_cancel_left' (ha : a ≠ 0) : a / b / a = b⁻¹ := sorry

lemma div_helper (b : G₀) (h : a ≠ 0) : 1 / (a * b) * a = 1 / b := by
  rw [div_mul_eq_mul_div, one_mul, div_mul_cancel_left₀ h, one_div]

@[target]
lemma div_div_div_cancel_left' (a b : G₀) (hc : c ≠ 0) : c / a / (c / b) = b / a := by sorry

@[simp] lemma div_mul_div_cancel₀' (ha : a ≠ 0) (b c : G₀) : a / b * (c / a) = c / b := by
  rw [mul_comm, div_mul_div_cancel₀ ha]

end CommGroupWithZero

section NoncomputableDefs

variable {M : Type*} [Nontrivial M]

open Classical in
/-- Constructs a `GroupWithZero` structure on a `MonoidWithZero`
  consisting only of units and 0. -/
noncomputable def groupWithZeroOfIsUnitOrEqZero [hM : MonoidWithZero M]
    (h : ∀ a : M, IsUnit a ∨ a = 0) : GroupWithZero M :=
  { hM with
    inv := fun a => if h0 : a = 0 then 0 else ↑((h a).resolve_right h0).unit⁻¹,
    inv_zero := dif_pos rfl,
    mul_inv_cancel := fun a h0 => by
      change (a * if h0 : a = 0 then 0 else ↑((h a).resolve_right h0).unit⁻¹) = 1
      rw [dif_neg h0, Units.mul_inv_eq_iff_eq_mul, one_mul, IsUnit.unit_spec],
    exists_pair_ne := Nontrivial.exists_pair_ne }

/-- Constructs a `CommGroupWithZero` structure on a `CommMonoidWithZero`
  consisting only of units and 0. -/
noncomputable def commGroupWithZeroOfIsUnitOrEqZero [hM : CommMonoidWithZero M]
    (h : ∀ a : M, IsUnit a ∨ a = 0) : CommGroupWithZero M :=
  { groupWithZeroOfIsUnitOrEqZero h, hM with }

end NoncomputableDefs
