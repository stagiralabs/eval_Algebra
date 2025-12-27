import VerifiedAgora.tagger
/-
Copyright (c) 2021 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Star.Pi
import Mathlib.Algebra.Star.Rat

/-!
# Self-adjoint, skew-adjoint and normal elements of a star additive group

This file defines `selfAdjoint R` (resp. `skewAdjoint R`), where `R` is a star additive group,
as the additive subgroup containing the elements that satisfy `star x = x` (resp. `star x = -x`).
This includes, for instance, (skew-)Hermitian operators on Hilbert spaces.

We also define `IsStarNormal R`, a `Prop` that states that an element `x` satisfies
`star x * x = x * star x`.

## Implementation notes

* When `R` is a `StarModule R₂ R`, then `selfAdjoint R` has a natural
  `Module (selfAdjoint R₂) (selfAdjoint R)` structure. However, doing this literally would be
  undesirable since in the main case of interest (`R₂ = ℂ`) we want `Module ℝ (selfAdjoint R)`
  and not `Module (selfAdjoint ℂ) (selfAdjoint R)`. We solve this issue by adding the typeclass
  `[TrivialStar R₃]`, of which `ℝ` is an instance (registered in `Data/Real/Basic`), and then
  add a `[Module R₃ (selfAdjoint R)]` instance whenever we have
  `[Module R₃ R] [TrivialStar R₃]`. (Another approach would have been to define
  `[StarInvariantScalars R₃ R]` to express the fact that `star (x • v) = x • star v`, but
  this typeclass would have the disadvantage of taking two type arguments.)

## TODO

* Define `IsSkewAdjoint` to match `IsSelfAdjoint`.
* Define `fun z x => z * x * star z` (i.e. conjugation by `z`) as a monoid action of `R` on `R`
  (similar to the existing `ConjAct` for groups), and then state the fact that `selfAdjoint R` is
  invariant under it.

-/

open Function

variable {R A : Type*}

/-- An element is self-adjoint if it is equal to its star. -/
def IsSelfAdjoint [Star R] (x : R) : Prop :=
  star x = x

/-- An element of a star monoid is normal if it commutes with its adjoint. -/
@[mk_iff]
class IsStarNormal [Mul R] [Star R] (x : R) : Prop where
  /-- A normal element of a star monoid commutes with its adjoint. -/
  star_comm_self : Commute (star x) x

export IsStarNormal (star_comm_self)

theorem star_comm_self' [Mul R] [Star R] (x : R) [IsStarNormal x] : star x * x = x * star x :=
  IsStarNormal.star_comm_self

namespace IsSelfAdjoint

-- named to match `Commute.allₓ`
/-- All elements are self-adjoint when `star` is trivial. -/
theorem all [Star R] [TrivialStar R] (r : R) : IsSelfAdjoint r :=
  star_trivial _

@[target]
theorem star_eq [Star R] {x : R} (hx : IsSelfAdjoint x) : star x = x :=
  sorry

theorem _root_.isSelfAdjoint_iff [Star R] {x : R} : IsSelfAdjoint x ↔ star x = x :=
  Iff.rfl

@[target, simp]
theorem star_iff [InvolutiveStar R] {x : R} : IsSelfAdjoint (star x) ↔ IsSelfAdjoint x := by sorry

@[simp]
theorem star_mul_self [Mul R] [StarMul R] (x : R) : IsSelfAdjoint (star x * x) := by
  simp only [IsSelfAdjoint, star_mul, star_star]

@[simp]
theorem mul_star_self [Mul R] [StarMul R] (x : R) : IsSelfAdjoint (x * star x) := by
  simpa only [star_star] using star_mul_self (star x)

/-- Self-adjoint elements commute if and only if their product is self-adjoint. -/
@[target]
lemma commute_iff {R : Type*} [Mul R] [StarMul R] {x y : R}
    (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) : Commute x y ↔ IsSelfAdjoint (x * y) := by sorry
@[target, aesop 10% apply]
theorem map {F R S : Type*} [Star R] [Star S] [FunLike F R S] [StarHomClass F R S]
    {x : R} (hx : IsSelfAdjoint x) (f : F) : IsSelfAdjoint (f x) :=
  sorry

@[deprecated (since := "2024-09-07")] alias starHom_apply := map

/- note: this lemma is *not* marked as `simp` so that Lean doesn't look for a `[TrivialStar R]`
instance every time it sees `⊢ IsSelfAdjoint (f x)`, which will likely occur relatively often. -/
@[target]
theorem _root_.isSelfAdjoint_map {F R S : Type*} [Star R] [Star S] [FunLike F R S]
    [StarHomClass F R S] [TrivialStar R] (f : F) (x : R) : IsSelfAdjoint (f x) :=
  sorry

@[deprecated (since := "2024-09-07")] alias _root_.isSelfAdjoint_starHom_apply := isSelfAdjoint_map

section AddMonoid

variable [AddMonoid R] [StarAddMonoid R]

variable (R) in
@[simp] protected theorem zero : IsSelfAdjoint (0 : R) := star_zero R

@[target, aesop 90% apply]
theorem add {x y : R} (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) : IsSelfAdjoint (x + y) := by sorry

end AddMonoid

section AddGroup

variable [AddGroup R] [StarAddMonoid R]

@[aesop safe apply]
theorem neg {x : R} (hx : IsSelfAdjoint x) : IsSelfAdjoint (-x) := by
  simp only [isSelfAdjoint_iff, star_neg, hx.star_eq]

@[target, aesop 90% apply]
theorem sub {x y : R} (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) : IsSelfAdjoint (x - y) := by sorry

end AddGroup

section AddCommMonoid

variable [AddCommMonoid R] [StarAddMonoid R]

@[simp]
theorem add_star_self (x : R) : IsSelfAdjoint (x + star x) := by
  simp only [isSelfAdjoint_iff, add_comm, star_add, star_star]

@[target, simp]
theorem star_add_self (x : R) : IsSelfAdjoint (star x + x) := by sorry

end AddCommMonoid

section Semigroup

variable [Semigroup R] [StarMul R]

@[aesop safe apply]
theorem conjugate {x : R} (hx : IsSelfAdjoint x) (z : R) : IsSelfAdjoint (z * x * star z) := by
  simp only [isSelfAdjoint_iff, star_mul, star_star, mul_assoc, hx.star_eq]

@[aesop safe apply]
theorem conjugate' {x : R} (hx : IsSelfAdjoint x) (z : R) : IsSelfAdjoint (star z * x * z) := by
  simp only [isSelfAdjoint_iff, star_mul, star_star, mul_assoc, hx.star_eq]

@[target, aesop 90% apply]
theorem conjugate_self {x : R} (hx : IsSelfAdjoint x) {z : R} (hz : IsSelfAdjoint z) :
    IsSelfAdjoint (z * x * z) := by sorry

@[aesop 10% apply]
theorem isStarNormal {x : R} (hx : IsSelfAdjoint x) : IsStarNormal x :=
  ⟨by simp only [Commute, SemiconjBy, hx.star_eq]⟩

end Semigroup

section MulOneClass

variable [MulOneClass R] [StarMul R]
variable (R)

@[simp] protected theorem one : IsSelfAdjoint (1 : R) :=
  star_one R

end MulOneClass

section Monoid

variable [Monoid R] [StarMul R]

@[aesop safe apply]
theorem pow {x : R} (hx : IsSelfAdjoint x) (n : ℕ) : IsSelfAdjoint (x ^ n) := by
  simp only [isSelfAdjoint_iff, star_pow, hx.star_eq]

end Monoid

section Semiring

variable [Semiring R] [StarRing R]

@[simp]
protected theorem natCast (n : ℕ) : IsSelfAdjoint (n : R) :=
  star_natCast _

@[simp]
protected theorem ofNat (n : ℕ) [n.AtLeastTwo] : IsSelfAdjoint (ofNat(n) : R) :=
  .natCast n

end Semiring

section CommSemigroup

variable [CommSemigroup R] [StarMul R]

theorem mul {x y : R} (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) : IsSelfAdjoint (x * y) := by
  simp only [isSelfAdjoint_iff, star_mul', hx.star_eq, hy.star_eq]

end CommSemigroup

section CommSemiring
variable {α : Type*} [CommSemiring α] [StarRing α] {a : α}

open scoped ComplexConjugate

@[target]
lemma conj_eq (ha : IsSelfAdjoint a) : conj a = a := sorry

end CommSemiring

section Ring

variable [Ring R] [StarRing R]

@[simp]
protected theorem intCast (z : ℤ) : IsSelfAdjoint (z : R) :=
  star_intCast _

end Ring

section Group

variable [Group R] [StarMul R]

@[target, aesop safe apply]
theorem inv {x : R} (hx : IsSelfAdjoint x) : IsSelfAdjoint x⁻¹ := by sorry

@[target, aesop safe apply]
theorem zpow {x : R} (hx : IsSelfAdjoint x) (n : ℤ) : IsSelfAdjoint (x ^ n) := by sorry

end Group

section GroupWithZero

variable [GroupWithZero R] [StarMul R]

@[target, aesop safe apply]
theorem inv₀ {x : R} (hx : IsSelfAdjoint x) : IsSelfAdjoint x⁻¹ := by sorry

@[target, aesop safe apply]
theorem zpow₀ {x : R} (hx : IsSelfAdjoint x) (n : ℤ) : IsSelfAdjoint (x ^ n) := by sorry

end GroupWithZero

@[simp]
protected lemma nnratCast [DivisionSemiring R] [StarRing R] (q : ℚ≥0) :
    IsSelfAdjoint (q : R) :=
  star_nnratCast _

section DivisionRing

variable [DivisionRing R] [StarRing R]

@[simp]
protected theorem ratCast (x : ℚ) : IsSelfAdjoint (x : R) :=
  star_ratCast _

end DivisionRing

section Semifield

variable [Semifield R] [StarRing R]

theorem div {x y : R} (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) : IsSelfAdjoint (x / y) := by
  simp only [isSelfAdjoint_iff, star_div₀, hx.star_eq, hy.star_eq]

end Semifield

section SMul

@[target, aesop safe apply]
theorem smul [Star R] [AddMonoid A] [StarAddMonoid A] [SMul R A] [StarModule R A]
    {r : R} (hr : IsSelfAdjoint r) {x : A} (hx : IsSelfAdjoint x) :
    IsSelfAdjoint (r • x) := by sorry

@[target]
theorem smul_iff [Monoid R] [StarMul R] [AddMonoid A] [StarAddMonoid A]
    [MulAction R A] [StarModule R A] {r : R} (hr : IsSelfAdjoint r) (hu : IsUnit r) {x : A} :
    IsSelfAdjoint (r • x) ↔ IsSelfAdjoint x := by sorry

end SMul

end IsSelfAdjoint

variable (R)

/-- The self-adjoint elements of a star additive group, as an additive subgroup. -/
def selfAdjoint [AddGroup R] [StarAddMonoid R] : AddSubgroup R where
  carrier := { x | IsSelfAdjoint x }
  zero_mem' := star_zero R
  add_mem' hx := hx.add
  neg_mem' hx := hx.neg

/-- The skew-adjoint elements of a star additive group, as an additive subgroup. -/
def skewAdjoint [AddCommGroup R] [StarAddMonoid R] : AddSubgroup R where
  carrier := { x | star x = -x }
  zero_mem' := show star (0 : R) = -0 by simp only [star_zero, neg_zero]
  add_mem' := @fun x y (hx : star x = -x) (hy : star y = -y) =>
    show star (x + y) = -(x + y) by rw [star_add x y, hx, hy, neg_add]
  neg_mem' := @fun x (hx : star x = -x) => show star (-x) = - -x by simp only [hx, star_neg]

variable {R}

namespace selfAdjoint

section AddGroup

variable [AddGroup R] [StarAddMonoid R]

theorem mem_iff {x : R} : x ∈ selfAdjoint R ↔ star x = x := by
  rw [← AddSubgroup.mem_carrier]
  exact Iff.rfl

@[simp, norm_cast]
theorem star_val_eq {x : selfAdjoint R} : star (x : R) = x :=
  x.prop

instance : Inhabited (selfAdjoint R) :=
  ⟨0⟩

end AddGroup

instance isStarNormal [NonUnitalRing R] [StarRing R] (x : selfAdjoint R) :
    IsStarNormal (x : R) :=
  x.prop.isStarNormal

section Ring

variable [Ring R] [StarRing R]

instance : One (selfAdjoint R) :=
  ⟨⟨1, .one R⟩⟩

@[simp, norm_cast]
theorem val_one : ↑(1 : selfAdjoint R) = (1 : R) :=
  rfl

instance [Nontrivial R] : Nontrivial (selfAdjoint R) :=
  ⟨⟨0, 1, ne_of_apply_ne Subtype.val zero_ne_one⟩⟩

instance : NatCast (selfAdjoint R) where
  natCast n := ⟨n, .natCast _⟩

instance : IntCast (selfAdjoint R) where
  intCast n := ⟨n, .intCast _⟩

instance : Pow (selfAdjoint R) ℕ where
  pow x n := ⟨(x : R) ^ n, x.prop.pow n⟩

@[target, simp, norm_cast]
theorem val_pow (x : selfAdjoint R) (n : ℕ) : ↑(x ^ n) = (x : R) ^ n :=
  sorry

end Ring

section NonUnitalCommRing

variable [NonUnitalCommRing R] [StarRing R]

instance : Mul (selfAdjoint R) where
  mul x y := ⟨(x : R) * y, x.prop.mul y.prop⟩

@[target, simp, norm_cast]
theorem val_mul (x y : selfAdjoint R) : ↑(x * y) = (x : R) * y :=
  sorry

end NonUnitalCommRing

section CommRing

variable [CommRing R] [StarRing R]

instance : CommRing (selfAdjoint R) :=
  Function.Injective.commRing _ Subtype.coe_injective (selfAdjoint R).coe_zero val_one
    (selfAdjoint R).coe_add val_mul (selfAdjoint R).coe_neg (selfAdjoint R).coe_sub
    (by intros; rfl) (by intros; rfl) val_pow
    (fun _ => rfl) fun _ => rfl

end CommRing

section Field

variable [Field R] [StarRing R]

instance : Inv (selfAdjoint R) where
  inv x := ⟨x.val⁻¹, x.prop.inv₀⟩

@[target, simp, norm_cast]
theorem val_inv (x : selfAdjoint R) : ↑x⁻¹ = (x : R)⁻¹ :=
  sorry

instance : Div (selfAdjoint R) where
  div x y := ⟨x / y, x.prop.div y.prop⟩

@[target, simp, norm_cast]
theorem val_div (x y : selfAdjoint R) : ↑(x / y) = (x / y : R) :=
  sorry

instance : Pow (selfAdjoint R) ℤ where
  pow x z := ⟨(x : R) ^ z, x.prop.zpow₀ z⟩

@[simp, norm_cast]
theorem val_zpow (x : selfAdjoint R) (z : ℤ) : ↑(x ^ z) = (x : R) ^ z :=
  rfl

instance instNNRatCast : NNRatCast (selfAdjoint R) where
  nnratCast q := ⟨q, .nnratCast q⟩

instance instRatCast : RatCast (selfAdjoint R) where
  ratCast q := ⟨q, .ratCast q⟩

@[simp, norm_cast] lemma val_nnratCast (q : ℚ≥0) : (q : selfAdjoint R) = (q : R) := rfl
@[simp, norm_cast] lemma val_ratCast (q : ℚ) : (q : selfAdjoint R) = (q : R) := rfl

instance instSMulNNRat : SMul ℚ≥0 (selfAdjoint R) where
  smul a x := ⟨a • (x : R), by rw [NNRat.smul_def]; exact .mul (.nnratCast a) x.prop⟩

instance instSMulRat : SMul ℚ (selfAdjoint R) where
  smul a x := ⟨a • (x : R), by rw [Rat.smul_def]; exact .mul (.ratCast a) x.prop⟩

@[simp, norm_cast] lemma val_nnqsmul (q : ℚ≥0) (x : selfAdjoint R) : ↑(q • x) = q • (x : R) := rfl
@[simp, norm_cast] lemma val_qsmul (q : ℚ) (x : selfAdjoint R) : ↑(q • x) = q • (x : R) := rfl

instance instField : Field (selfAdjoint R) :=
  Subtype.coe_injective.field _  (selfAdjoint R).coe_zero val_one
    (selfAdjoint R).coe_add val_mul (selfAdjoint R).coe_neg (selfAdjoint R).coe_sub
    val_inv val_div (swap (selfAdjoint R).coe_nsmul) (by intros; rfl) val_nnqsmul
    val_qsmul val_pow val_zpow (fun _ => rfl) (fun _ => rfl) val_nnratCast val_ratCast

end Field

section SMul

variable [Star R] [TrivialStar R] [AddGroup A] [StarAddMonoid A]

instance [SMul R A] [StarModule R A] : SMul R (selfAdjoint A) where
  smul r x := ⟨r • (x : A), (IsSelfAdjoint.all _).smul x.prop⟩

@[simp, norm_cast]
theorem val_smul [SMul R A] [StarModule R A] (r : R) (x : selfAdjoint A) : ↑(r • x) = r • (x : A) :=
  rfl

instance [Monoid R] [MulAction R A] [StarModule R A] : MulAction R (selfAdjoint A) :=
  Function.Injective.mulAction Subtype.val Subtype.coe_injective val_smul

instance [Monoid R] [DistribMulAction R A] [StarModule R A] : DistribMulAction R (selfAdjoint A) :=
  Function.Injective.distribMulAction (selfAdjoint A).subtype Subtype.coe_injective val_smul

end SMul

section Module

variable [Star R] [TrivialStar R] [AddCommGroup A] [StarAddMonoid A]

instance [Semiring R] [Module R A] [StarModule R A] : Module R (selfAdjoint A) :=
  Function.Injective.module R (selfAdjoint A).subtype Subtype.coe_injective val_smul

end Module

end selfAdjoint

namespace skewAdjoint

section AddGroup

variable [AddCommGroup R] [StarAddMonoid R]

theorem mem_iff {x : R} : x ∈ skewAdjoint R ↔ star x = -x := by
  rw [← AddSubgroup.mem_carrier]
  exact Iff.rfl

@[target, simp, norm_cast]
theorem star_val_eq {x : skewAdjoint R} : star (x : R) = -x :=
  sorry

instance : Inhabited (skewAdjoint R) :=
  ⟨0⟩

end AddGroup

section Ring

variable [Ring R] [StarRing R]

theorem conjugate {x : R} (hx : x ∈ skewAdjoint R) (z : R) : z * x * star z ∈ skewAdjoint R := by
  simp only [mem_iff, star_mul, star_star, mem_iff.mp hx, neg_mul, mul_neg, mul_assoc]

@[target]
theorem conjugate' {x : R} (hx : x ∈ skewAdjoint R) (z : R) : star z * x * z ∈ skewAdjoint R := by sorry

@[target]
theorem isStarNormal_of_mem {x : R} (hx : x ∈ skewAdjoint R) : IsStarNormal x :=
  sorry

instance (x : skewAdjoint R) : IsStarNormal (x : R) :=
  isStarNormal_of_mem (SetLike.coe_mem _)

end Ring

section SMul

variable [Star R] [TrivialStar R] [AddCommGroup A] [StarAddMonoid A]

@[aesop safe apply (rule_sets := [SetLike])]
theorem smul_mem [Monoid R] [DistribMulAction R A] [StarModule R A] (r : R) {x : A}
    (h : x ∈ skewAdjoint A) : r • x ∈ skewAdjoint A := by
  rw [mem_iff, star_smul, star_trivial, mem_iff.mp h, smul_neg r]

instance [Monoid R] [DistribMulAction R A] [StarModule R A] : SMul R (skewAdjoint A) where
  smul r x := ⟨r • (x : A), smul_mem r x.prop⟩

@[target, simp, norm_cast]
theorem val_smul [Monoid R] [DistribMulAction R A] [StarModule R A] (r : R) (x : skewAdjoint A) :
    ↑(r • x) = r • (x : A) :=
  sorry

instance [Monoid R] [DistribMulAction R A] [StarModule R A] : DistribMulAction R (skewAdjoint A) :=
  Function.Injective.distribMulAction (skewAdjoint A).subtype Subtype.coe_injective val_smul

instance [Semiring R] [Module R A] [StarModule R A] : Module R (skewAdjoint A) :=
  Function.Injective.module R (skewAdjoint A).subtype Subtype.coe_injective val_smul

end SMul

end skewAdjoint

/-- Scalar multiplication of a self-adjoint element by a skew-adjoint element produces a
skew-adjoint element. -/
theorem IsSelfAdjoint.smul_mem_skewAdjoint [Ring R] [AddCommGroup A] [Module R A] [StarAddMonoid R]
    [StarAddMonoid A] [StarModule R A] {r : R} (hr : r ∈ skewAdjoint R) {a : A}
    (ha : IsSelfAdjoint a) : r • a ∈ skewAdjoint A :=
  (star_smul _ _).trans <| (congr_arg₂ _ hr ha).trans <| neg_smul _ _

/-- Scalar multiplication of a skew-adjoint element by a skew-adjoint element produces a
self-adjoint element. -/
@[target]
theorem isSelfAdjoint_smul_of_mem_skewAdjoint [Ring R] [AddCommGroup A] [Module R A]
    [StarAddMonoid R] [StarAddMonoid A] [StarModule R A] {r : R} (hr : r ∈ skewAdjoint R) {a : A}
    (ha : a ∈ skewAdjoint A) : IsSelfAdjoint (r • a) :=
  sorry

-- see Note [lower instance priority]
instance (priority := 100) TrivialStar.isStarNormal [Mul R] [StarMul R] [TrivialStar R]
    {x : R} : IsStarNormal x :=
  ⟨by rw [star_trivial]⟩

-- see Note [lower instance priority]
instance (priority := 100) CommMonoid.isStarNormal [CommMonoid R] [StarMul R] {x : R} :
    IsStarNormal x :=
  ⟨mul_comm _ _⟩


namespace Pi
variable {ι : Type*} {α : ι → Type*} [∀ i, Star (α i)] {f : ∀ i, α i}

protected lemma isSelfAdjoint : IsSelfAdjoint f ↔ ∀ i, IsSelfAdjoint (f i) := funext_iff

alias ⟨_root_.IsSelfAdjoint.apply, _⟩ := Pi.isSelfAdjoint

end Pi
