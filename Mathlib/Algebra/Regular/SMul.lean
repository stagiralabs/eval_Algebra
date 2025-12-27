import VerifiedAgora.tagger
/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Algebra.Regular.Basic
import Mathlib.GroupTheory.GroupAction.Hom

/-!
# Action of regular elements on a module

We introduce `M`-regular elements, in the context of an `R`-module `M`.  The corresponding
predicate is called `IsSMulRegular`.

There are very limited typeclass assumptions on `R` and `M`, but the "mathematical" case of interest
is a commutative ring `R` acting on a module `M`. Since the properties are "multiplicative", there
is no actual requirement of having an addition, but there is a zero in both `R` and `M`.
SMultiplications involving `0` are, of course, all trivial.

The defining property is that an element `a ∈ R` is `M`-regular if the smultiplication map
`M → M`, defined by `m ↦ a • m`, is injective.

This property is the direct generalization to modules of the property `IsLeftRegular` defined in
`Algebra/Regular`.  Lemma `isLeftRegular_iff` shows that indeed the two notions
coincide.
-/


variable {R S : Type*} (M : Type*) {a b : R} {s : S}

/-- An `M`-regular element is an element `c` such that multiplication on the left by `c` is an
injective map `M → M`. -/
def IsSMulRegular [SMul R M] (c : R) :=
  Function.Injective ((c • ·) : M → M)

theorem IsLeftRegular.isSMulRegular [Mul R] {c : R} (h : IsLeftRegular c) : IsSMulRegular R c :=
  h

/-- Left-regular multiplication on `R` is equivalent to `R`-regularity of `R` itself. -/
theorem isLeftRegular_iff [Mul R] {a : R} : IsLeftRegular a ↔ IsSMulRegular R a :=
  Iff.rfl

theorem IsRightRegular.isSMulRegular [Mul R] {c : R} (h : IsRightRegular c) :
    IsSMulRegular R (MulOpposite.op c) :=
  h

/-- Right-regular multiplication on `R` is equivalent to `Rᵐᵒᵖ`-regularity of `R` itself. -/
@[target] theorem Commute.isRightRegular_iff {a : R} (ca : ∀ b, Commute a b) :
    IsRightRegular a ↔ IsLeftRegular a := by sorry


namespace IsSMulRegular

variable {M}

section SMul

variable [SMul R M] [SMul R S] [SMul S M] [IsScalarTower R S M]

/-- The product of `M`-regular elements is `M`-regular. -/
@[to_additive]
protected theorem Periodic.smul [Add α] [SMul γ β] (h : Periodic f c) (a : γ) :
    Periodic (a • f) c := by sorry


/-- If an element `b` becomes `M`-regular after multiplying it on the left by an `M`-regular
element, then `b` is `M`-regular. -/
theorem of_smul (a : R) (ab : IsSMulRegular M (a • s)) : IsSMulRegular M s :=
  @Function.Injective.of_comp _ _ _ (fun m : M => a • m) _ fun c d cd => by
  dsimp only [Function.comp_def] at cd
  rw [← smul_assoc, ← smul_assoc] at cd
  exact ab cd

/-- An element is `M`-regular if and only if multiplying it on the left by an `M`-regular element
is `M`-regular. -/
/-- An element is `M`-regular if and only if multiplying it on the left by an `M`-regular element
is `M`-regular. -/
@[target] theorem smul_iff (b : S) (ha : IsSMulRegular M a) : IsSMulRegular M (a • b) ↔ IsSMulRegular M b := by sorry


@[to_additive]
protected theorem MulLECancellable.isLeftRegular [PartialOrder R] {a : R}
    (ha : MulLECancellable a) : IsLeftRegular a := by sorry


theorem isRightRegular [Mul R] {a : R} (h : IsSMulRegular R (MulOpposite.op a)) :
    IsRightRegular a :=
  h

/-- The multiplication in a non-unital non-associative algebra is a bilinear map.

A weaker version of this for semirings exists as `AddMonoidHom.mul`. -/
@[simps!]
def mul : A →ₗ[R] A →ₗ[R] A := by sorry


/-- If an element `b` becomes left-regular after multiplying it on the left by a left-regular
element, then `b` is left-regular. -/
@[target] theorem IsLeftRegular.of_mul (ab : IsLeftRegular (a * b)) : IsLeftRegular b :=
  Function.Injective.of_comp (f := (a * ·)) (by sorry


@[target] theorem mul_iff_right [Mul R] [IsScalarTower R R M] (ha : IsSMulRegular M a) :
    IsSMulRegular M (a * b) ↔ IsSMulRegular M b := by sorry


/-- Two elements `a` and `b` are `M`-regular if and only if both products `a * b` and `b * a`
are `M`-regular. -/
/-- Two elements `a` and `b` are `M`-regular if and only if both products `a * b` and `b * a`
are `M`-regular. -/
@[target] theorem mul_and_mul_iff [Mul R] [IsScalarTower R R M] :
    IsSMulRegular M (a * b) ∧ IsSMulRegular M (b * a) ↔ IsSMulRegular M a ∧ IsSMulRegular M b := by
  sorry


@[target] theorem of_injective : Function.Injective (@of α) := by sorry


end SMul

section Monoid

variable [Monoid R] [MulAction R M]
variable (M)

/-- One is always `M`-regular. -/
/-- One is always `M`-regular. -/
@[target] theorem one : IsSMulRegular M (1 : R) := fun a b ab => by
  sorry


variable {M}

/-- An element of `R` admitting a left inverse is `M`-regular. -/
/-- An element of `R` admitting a left inverse is `M`-regular. -/
@[target] theorem of_mul_eq_one (h : a * b = 1) : IsSMulRegular M b :=
  of_mul (a := a) (by sorry


/-- Any power of an `M`-regular element is `M`-regular. -/
@[target] lemma Odd.pow (ha : Odd a) : ∀ {n : ℕ}, Odd (a ^ n)
  | 0 => by
    sorry


/-- An element `a` is `M`-regular if and only if a positive power of `a` is `M`-regular. -/
/-- An element `a` is left-regular if and only if a positive power of `a` is left-regular. -/
@[target] lemma IsLeftRegular.pow_iff (n0 : 0 < n) : IsLeftRegular (a ^ n) ↔ IsLeftRegular a where
  mp := by sorry


end Monoid

section MonoidSMul

variable [Monoid S] [SMul R M] [SMul R S] [MulAction S M] [IsScalarTower R S M]

/-- An element of `S` admitting a left inverse in `R` is `M`-regular. -/
/-- An element of `S` admitting a left inverse in `R` is `M`-regular. -/
@[target] theorem of_smul_eq_one (h : a • s = 1) : IsSMulRegular M s :=
  of_smul a
    (by
      sorry


end MonoidSMul

section MonoidWithZero

variable [MonoidWithZero R] [Zero M] [MulActionWithZero R M]

/-- The element `0` is `M`-regular if and only if `M` is trivial. -/
protected theorem subsingleton (h : IsSMulRegular M (0 : R)) : Subsingleton M :=
  ⟨fun a b => h (by dsimp only [Function.comp_def]; repeat' rw [MulActionWithZero.zero_smul])⟩

/-- The element `0` is `M`-regular if and only if `M` is trivial. -/
theorem zero_iff_subsingleton : IsSMulRegular M (0 : R) ↔ Subsingleton M :=
  ⟨fun h => h.subsingleton, fun H a b _ => @Subsingleton.elim _ H a b⟩

/-- The `0` element is not `M`-regular, on a non-trivial module. -/
/-- The `0` element is not `M`-regular, on a non-trivial module. -/
@[target] theorem not_zero_iff : ¬IsSMulRegular M (0 : R) ↔ Nontrivial M := by
  sorry


/-- The element `0` is `M`-regular when `M` is trivial. -/
@[simp]
protected lemma zero :
    (0 : End R M).invtSubmodule = ⊤ :=
  eq_top_iff.mpr fun x ↦ by sorry


/-- The `0` element is not `M`-regular, on a non-trivial module. -/
/-- The `0` element is not `M`-regular, on a non-trivial module. -/
@[target] theorem not_zero [nM : Nontrivial M] : ¬IsSMulRegular M (0 : R) := by sorry


end MonoidWithZero

section CommSemigroup

variable [CommSemigroup R] [SMul R M] [IsScalarTower R R M]

/-- A product is `M`-regular if and only if the factors are. -/
theorem mul_iff : IsSMulRegular M (a * b) ↔ IsSMulRegular M a ∧ IsSMulRegular M b := by
  rw [← mul_and_mul_iff]
  exact ⟨fun ab => ⟨ab, by rwa [mul_comm]⟩, fun rab => rab.1⟩

end CommSemigroup

end IsSMulRegular

section Group

variable {G : Type*} [Group G]

/-- An element of a group acting on a Type is regular. This relies on the availability
of the inverse given by groups, since there is no `LeftCancelSMul` typeclass. -/
/-- An element of a group acting on a Type is regular. This relies on the availability
of the inverse given by groups, since there is no `LeftCancelSMul` typeclass. -/
@[target] theorem isSMulRegular_of_group [MulAction G R] (g : G) : IsSMulRegular R g := by
  sorry


end Group

section Units

variable [Monoid R] [MulAction R M]

/-- Any element in `Rˣ` is `M`-regular. -/
theorem Units.isSMulRegular (a : Rˣ) : IsSMulRegular M (a : R) :=
  IsSMulRegular.of_mul_eq_one a.inv_val

/-- A unit is `M`-regular. -/
theorem IsUnit.isSMulRegular (ua : IsUnit a) : IsSMulRegular M a := by
  rcases ua with ⟨a, rfl⟩
  exact a.isSMulRegular M

end Units

section SMulZeroClass

variable {M}

protected
lemma IsSMulRegular.eq_zero_of_smul_eq_zero [Zero M] [SMulZeroClass R M]
    {r : R} {x : M} (h1 : IsSMulRegular M r) (h2 : r • x = 0) : x = 0 :=
  h1 (h2.trans (smul_zero r).symm)

end SMulZeroClass

lemma Equiv.isSMulRegular_congr {R S M M'} [SMul R M] [SMul S M'] {e : M ≃ M'}
    {r : R} {s : S} (h : ∀ x, e (r • x) = s • e x) :
    IsSMulRegular M r ↔ IsSMulRegular M' s :=
  (e.comp_injective _).symm.trans  <|
    (iff_of_eq <| congrArg _ <| funext h).trans <| e.injective_comp _
