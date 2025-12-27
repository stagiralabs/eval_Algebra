import VerifiedAgora.tagger
/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Group.Instances

/-!
# Maps (semi)conjugating a shift to a shift

Denote by $S^1$ the unit circle `UnitAddCircle`.
A common way to study a self-map $f\colon S^1\to S^1$ of degree `1`
is to lift it to a map $\tilde f\colon \mathbb R\to \mathbb R$
such that $\tilde f(x + 1) = \tilde f(x)+1$ for all `x`.

In this file we define a structure and a typeclass
for bundled maps satisfying `f (x + a) = f x + b`.

We use parameters `a` and `b` instead of `1` to accommodate for two use cases:

- maps between circles of different lengths;
- self-maps $f\colon S^1\to  S^1$ of degree other than one,
  including orientation-reversing maps.
-/

assert_not_exists Finset

open Function Set

/-- A bundled map `f : G → H` such that `f (x + a) = f x + b` for all `x`,
denoted as `f: G →+c[a, b] H`.

One can think about `f` as a lift to `G` of a map between two `AddCircle`s. -/
structure AddConstMap (G H : Type*) [Add G] [Add H] (a : G) (b : H) where
  /-- The underlying function of an `AddConstMap`.
  Use automatic coercion to function instead. -/
  protected toFun : G → H
  /-- An `AddConstMap` satisfies `f (x + a) = f x + b`. Use `map_add_const` instead. -/
  map_add_const' (x : G) : toFun (x + a) = toFun x + b

@[inherit_doc]
scoped [AddConstMap] notation:25 G " →+c[" a ", " b "] " H => AddConstMap G H a b

/-- Typeclass for maps satisfying `f (x + a) = f x + b`.

Note that `a` and `b` are `outParam`s,
so one should not add instances like
`[AddConstMapClass F G H a b] : AddConstMapClass F G H (-a) (-b)`. -/
class AddConstMapClass (F : Type*) (G H : outParam Type*) [Add G] [Add H]
    (a : outParam G) (b : outParam H) [FunLike F G H] : Prop where
  /-- A map of `AddConstMapClass` class semiconjugates shift by `a` to the shift by `b`:
  `∀ x, f (x + a) = f x + b`. -/
  map_add_const (f : F) (x : G) : f (x + a) = f x + b

namespace AddConstMapClass

/-!
### Properties of `AddConstMapClass` maps

In this section we prove properties like `f (x + n • a) = f x + n • b`.
-/

scoped [AddConstMapClass] attribute [simp] map_add_const

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

protected theorem semiconj [Add G] [Add H] [AddConstMapClass F G H a b] (f : F) :
    Semiconj f (· + a) (· + b) :=
  map_add_const f

@[target] theorem map_add_nsmul [AddMonoid G] [AddMonoid H] [AddConstMapClass F G H a b]
    (f : F) (x : G) (n : ℕ) : f (x + n • a) = f x + n • b := by
  sorry


@[target] theorem map_add_nat [AddMonoidWithOne G] [AddMonoidWithOne H] [AddConstMapClass F G H 1 1]
    (f : F) (x : G) (n : ℕ) : f (x + n) = f x + n := by sorry


@[target] theorem map_add_one [AddMonoidWithOne G] [Add H] [AddConstMapClass F G H 1 b]
    (f : F) (x : G) : f (x + 1) = f x + b := by sorry


@[target] theorem map_add_ofNat [AddMonoidWithOne G] [AddMonoidWithOne H] [AddConstMapClass F G H 1 1]
    (f : F) (x : G) (n : ℕ) [n.AtLeastTwo] :
    f (x + ofNat(n)) = f x + ofNat(n) := by sorry


theorem map_add_nat [AddMonoidWithOne G] [AddMonoidWithOne H] [AddConstMapClass F G H 1 1]
    (f : F) (x : G) (n : ℕ) : f (x + n) = f x + n := by simp

theorem map_add_ofNat [AddMonoidWithOne G] [AddMonoidWithOne H] [AddConstMapClass F G H 1 1]
    (f : F) (x : G) (n : ℕ) [n.AtLeastTwo] :
    f (x + ofNat(n)) = f x + ofNat(n) := map_add_nat f x n

@[target] theorem map_const [AddZeroClass G] [Add H] [AddConstMapClass F G H a b] (f : F) :
    f a = f 0 + b := by
  sorry


/-- A ring isomorphism sends one to one. -/
protected theorem map_one : f 1 = 1 := by sorry


@[scoped simp]
theorem map_nsmul_const [AddMonoid G] [AddMonoid H] [AddConstMapClass F G H a b]
    (f : F) (n : ℕ) : f (n • a) = f 0 + n • b := by
  simpa using map_add_nsmul f 0 n

@[target] theorem map_nat [AddMonoidWithOne G] [AddMonoidWithOne H] [AddConstMapClass F G H 1 1]
    (f : F) (n : ℕ) : f n = f 0 + n := by sorry


@[target] theorem map_ofNat [AddMonoidWithOne G] [AddMonoidWithOne H] [AddConstMapClass F G H 1 1]
    (f : F) (n : ℕ) [n.AtLeastTwo] :
    f ofNat(n) = f 0 + ofNat(n) := by sorry


theorem map_nat [AddMonoidWithOne G] [AddMonoidWithOne H] [AddConstMapClass F G H 1 1]
    (f : F) (n : ℕ) : f n = f 0 + n := by simp

theorem map_ofNat [AddMonoidWithOne G] [AddMonoidWithOne H] [AddConstMapClass F G H 1 1]
    (f : F) (n : ℕ) [n.AtLeastTwo] :
    f ofNat(n) = f 0 + ofNat(n) := map_nat f n

@[target] theorem map_const_add [AddCommSemigroup G] [Add H] [AddConstMapClass F G H a b]
    (f : F) (x : G) : f (a + x) = f x + b := by
  sorry


@[target] theorem map_one_add [AddCommMonoidWithOne G] [Add H] [AddConstMapClass F G H 1 b]
    (f : F) (x : G) : f (1 + x) = f x + b := by sorry


@[target] theorem map_nsmul_add [AddCommMonoid G] [AddMonoid H] [AddConstMapClass F G H a b]
    (f : F) (n : ℕ) (x : G) : f (n • a + x) = f x + n • b := by
  sorry


@[target] theorem map_nat_add [AddCommMonoidWithOne G] [AddMonoidWithOne H] [AddConstMapClass F G H 1 1]
    (f : F) (n : ℕ) (x : G) : f (↑n + x) = f x + n := by sorry


@[target] theorem map_ofNat_add [AddCommMonoidWithOne G] [AddMonoidWithOne H] [AddConstMapClass F G H 1 1]
    (f : F) (n : ℕ) [n.AtLeastTwo] (x : G) :
    f (ofNat(n) + x) = f x + ofNat(n) := by sorry


theorem map_nat_add [AddCommMonoidWithOne G] [AddMonoidWithOne H] [AddConstMapClass F G H 1 1]
    (f : F) (n : ℕ) (x : G) : f (↑n + x) = f x + n := by simp

theorem map_ofNat_add [AddCommMonoidWithOne G] [AddMonoidWithOne H] [AddConstMapClass F G H 1 1]
    (f : F) (n : ℕ) [n.AtLeastTwo] (x : G) :
    f (ofNat(n) + x) = f x + ofNat(n) :=
  map_nat_add f n x

@[target] theorem map_sub_nsmul [AddGroup G] [AddGroup H] [AddConstMapClass F G H a b]
    (f : F) (x : G) (n : ℕ) : f (x - n • a) = f x - n • b := by
  sorry


@[target] theorem map_sub_const [AddGroup G] [AddGroup H] [AddConstMapClass F G H a b]
    (f : F) (x : G) : f (x - a) = f x - b := by
  sorry


@[target] theorem map_sub_one [AddGroup G] [One G] [AddGroup H] [AddConstMapClass F G H 1 b]
    (f : F) (x : G) : f (x - 1) = f x - b := by sorry


@[scoped simp]
theorem map_sub_nat' [AddGroupWithOne G] [AddGroup H] [AddConstMapClass F G H 1 b]
    (f : F) (x : G) (n : ℕ) : f (x - n) = f x - n • b := by
  simpa using map_sub_nsmul f x n

@[scoped simp]
theorem map_sub_ofNat' [AddGroupWithOne G] [AddGroup H] [AddConstMapClass F G H 1 b]
    (f : F) (x : G) (n : ℕ) [n.AtLeastTwo] :
    f (x - ofNat(n)) = f x - ofNat(n) • b :=
  map_sub_nat' f x n

@[target] theorem map_add_zsmul [AddGroup G] [AddGroup H] [AddConstMapClass F G H a b]
    (f : F) (x : G) : ∀ n : ℤ, f (x + n • a) = f x + n • b
  | (n : ℕ) => by sorry


@[target] theorem map_zsmul_const [AddGroup G] [AddGroup H] [AddConstMapClass F G H a b]
    (f : F) (n : ℤ) : f (n • a) = f 0 + n • b := by
  sorry


@[target] theorem map_add_int [AddGroupWithOne G] [AddGroupWithOne H] [AddConstMapClass F G H 1 1]
    (f : F) (x : G) (n : ℤ) : f (x + n) = f x + n := by sorry


theorem map_add_int [AddGroupWithOne G] [AddGroupWithOne H] [AddConstMapClass F G H 1 1]
    (f : F) (x : G) (n : ℤ) : f (x + n) = f x + n := by simp

@[target] theorem map_sub_zsmul [AddGroup G] [AddGroup H] [AddConstMapClass F G H a b]
    (f : F) (x : G) (n : ℤ) : f (x - n • a) = f x - n • b := by
  sorry


@[target] theorem map_sub_int [AddGroupWithOne G] [AddGroupWithOne H] [AddConstMapClass F G H 1 1]
    (f : F) (x : G) (n : ℤ) : f (x - n) = f x - n := by sorry


theorem map_sub_int [AddGroupWithOne G] [AddGroupWithOne H] [AddConstMapClass F G H 1 1]
    (f : F) (x : G) (n : ℤ) : f (x - n) = f x - n := by simp

@[target] theorem map_zsmul_add [AddCommGroup G] [AddGroup H] [AddConstMapClass F G H a b]
    (f : F) (n : ℤ) (x : G) : f (n • a + x) = f x + n • b := by
  sorry


@[target] theorem map_int_add [AddCommGroupWithOne G] [AddGroupWithOne H] [AddConstMapClass F G H 1 1]
    (f : F) (n : ℤ) (x : G) : f (↑n + x) = f x + n := by sorry


theorem map_int_add [AddCommGroupWithOne G] [AddGroupWithOne H] [AddConstMapClass F G H 1 1]
    (f : F) (n : ℤ) (x : G) : f (↑n + x) = f x + n := by simp

@[target] theorem map_fract {R : Type*} [LinearOrderedRing R] [FloorRing R] [AddGroup H]
    [FunLike F R H] [AddConstMapClass F R H 1 b] (f : F) (x : R) :
    f (Int.fract x) = f x - ⌊x⌋ • b := by sorry


open scoped Relator in
/-- Auxiliary lemmas for the "monotonicity on a fundamental interval implies monotonicity" lemmas.
We formulate it for any relation so that the proof works both for `Monotone` and `StrictMono`. -/
protected theorem rel_map_of_Icc [LinearOrderedAddCommGroup G] [Archimedean G] [AddGroup H]
    [AddConstMapClass F G H a b] {f : F} {R : H → H → Prop} [IsTrans H R]
    [hR : CovariantClass H H (fun x y ↦ y + x) R] (ha : 0 < a) {l : G}
    (hf : ∀ x ∈ Icc l (l + a), ∀ y ∈ Icc l (l + a), x < y → R (f x) (f y)) :
    ((· < ·) ⇒ R) f f := fun x y hxy ↦ by
  replace hR := hR.elim
  have ha' : 0 ≤ a := ha.le
  -- Shift both points by `m • a` so that `l ≤ x < l + a`
  wlog hx : x ∈ Ico l (l + a) generalizing x y
  · rcases existsUnique_sub_zsmul_mem_Ico ha x l with ⟨m, hm, -⟩
    suffices R (f (x - m • a)) (f (y - m • a)) by simpa using hR (m • b) this
    exact this _ _ (by simpa) hm
  · -- Now find `n` such that `l + n • a < y ≤ l + (n + 1) • a`
    rcases existsUnique_sub_zsmul_mem_Ioc ha y l with ⟨n, hny, -⟩
    rcases lt_trichotomy n 0 with hn | rfl | hn
    · -- Since `l ≤ x ≤ y`, the case `n < 0` is impossible
      refine absurd ?_ hxy.not_le
      calc
        y ≤ l + a + n • a := sub_le_iff_le_add.1 hny.2
        _ = l + (n + 1) • a := by rw [add_comm n, add_smul, one_smul, add_assoc]
        _ ≤ l + 0 • a := add_le_add_left (zsmul_le_zsmul_left ha.le (by omega)) _
        _ ≤ x := by simpa using hx.1
    · -- If `n = 0`, then `l < y ≤ l + a`, hence we can apply the assumption
      exact hf x (Ico_subset_Icc_self hx) y (by simpa using Ioc_subset_Icc_self hny) hxy
    · -- In the remaining case `0 < n` we use transitivity.
      -- If `R = (· < ·)`, then the proof looks like
      -- `f x < f (l + a) ≤ f (l + n • a) < f y`
      trans f (l + (1 : ℤ) • a)
      · rw [one_zsmul]
        exact hf x (Ico_subset_Icc_self hx) (l + a) (by simpa) hx.2
      have hy : R (f (l + n • a)) (f y) := by
        rw [← sub_add_cancel y (n • a), map_add_zsmul, map_add_zsmul]
        refine hR _ <| hf _ ?_ _ (Ioc_subset_Icc_self hny) hny.1; simpa
      rw [← Int.add_one_le_iff, zero_add] at hn
      rcases hn.eq_or_lt with rfl | hn; · assumption
      trans f (l + n • a)
      · refine Int.rel_of_forall_rel_succ_of_lt R (f := (f <| l + · • a)) (fun k ↦ ?_) hn
        simp_rw [add_comm k 1, add_zsmul, ← add_assoc, one_zsmul, map_add_zsmul]
        refine hR (k • b) (hf _ ?_ _ ?_ ?_) <;> simpa
      · assumption

@[target] theorem monotone_iff_Icc [LinearOrderedAddCommGroup G] [Archimedean G] [OrderedAddCommGroup H]
    [AddConstMapClass F G H a b] {f : F} (ha : 0 < a) (l : G) :
    Monotone f ↔ MonotoneOn f (Icc l (l + a)) := by sorry


@[target] theorem antitone_iff_Icc [LinearOrderedAddCommGroup G] [Archimedean G] [OrderedAddCommGroup H]
    [AddConstMapClass F G H a b] {f : F} (ha : 0 < a) (l : G) :
    Antitone f ↔ AntitoneOn f (Icc l (l + a)) := by sorry


@[target] theorem strictMono_iff_Icc [LinearOrderedAddCommGroup G] [Archimedean G] [OrderedAddCommGroup H]
    [AddConstMapClass F G H a b] {f : F} (ha : 0 < a) (l : G) :
    StrictMono f ↔ StrictMonoOn f (Icc l (l + a)) := by sorry


@[target] theorem strictAnti_iff_Icc [LinearOrderedAddCommGroup G] [Archimedean G] [OrderedAddCommGroup H]
    [AddConstMapClass F G H a b] {f : F} (ha : 0 < a) (l : G) :
    StrictAnti f ↔ StrictAntiOn f (Icc l (l + a)) := by sorry


end AddConstMapClass

open AddConstMapClass

namespace AddConstMap

section Add

variable {G H : Type*} [Add G] [Add H] {a : G} {b : H}

/-!
### Coercion to function
-/

instance : FunLike (G →+c[a, b] H) G H where
  coe := AddConstMap.toFun
  coe_injective' | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

@[target] theorem coe_mk (f : A → B) (h₁ h₂ h₃ h₄) : ⇑(⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩ : A →ₛₙₐ[φ] B) = f := by sorry

@[target] theorem mk_coe (f : A →ₛₙₐ[φ] B) (h₁ h₂ h₃ h₄) : (⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩ : A →ₛₙₐ[φ] B) = f := by
  sorry

@[target] theorem toFun_eq_coe (f : A →ₛₙₐ[φ] B) : f.toFun = ⇑f := by sorry


instance : AddConstMapClass (G →+c[a, b] H) G H a b where
  map_add_const f := f.map_add_const'

@[ext] protected theorem ext {f g : G →+c[a, b] H} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

initialize_simps_projections AddConstMap (toFun → coe, as_prefix coe)

/-!
### Constructions about `G →+c[a, b] H`
-/

/-- The identity map as `G →+c[a, a] G`. -/
@[simps (config := .asFn)]
protected def id : G →+c[a, a] G := ⟨id, fun _ ↦ rfl⟩

instance : Inhabited (G →+c[a, a] G) := ⟨.id⟩

/-- Composition of two `AddConstMap`s. -/
set_option linter.unusedVariables false in
/-- The composition of morphisms is a morphism. -/
def comp (f : B →ₛₙₐ[ψ] C) (g : A →ₛₙₐ[φ] B) [κ : MonoidHom.CompTriple φ ψ χ] :
    A →ₛₙₐ[χ] C := by sorry


@[target] theorem comp_id : φ.comp (AlgHom.id R A) = φ := by sorry

@[target] theorem id_comp : (AlgHom.id R B).comp φ = φ := by sorry


/-- Change constants `a` and `b` in `(f : G →+c[a, b] H)` to improve definitional equalities. -/
/-- Change constants `a` and `b` in `(f : G →+c[a, b] H)` to improve definitional equalities. -/
@[simps (config := by sorry


/-- If `f` is an `AddConstMap`, then so is `(c +ᵥ f ·)`. -/
instance {K : Type*} [VAdd K H] [VAddAssocClass K H H] : VAdd K (G →+c[a, b] H) :=
  ⟨fun c f ↦ ⟨c +ᵥ ⇑f, fun x ↦ by simp [vadd_add_assoc]⟩⟩

@[target] theorem coe_vadd {K : Type*} [VAdd K H] [VAddAssocClass K H H] (c : K) (f : G →+c[a, b] H) :
    ⇑(c +ᵥ f) = c +ᵥ ⇑f := by sorry


instance {K : Type*} [AddMonoid K] [AddAction K H] [VAddAssocClass K H H] :
    AddAction K (G →+c[a, b] H) :=
  DFunLike.coe_injective.addAction _ coe_vadd

/-!
### Monoid structure on endomorphisms `G →+c[a, a] G`
-/

instance : Mul (G →+c[a, a] G) := ⟨comp⟩
instance : One (G →+c[a, a] G) := ⟨.id⟩

instance : Pow (G →+c[a, a] G) ℕ where
  pow f n := ⟨f^[n], Commute.iterate_left (AddConstMapClass.semiconj f) _⟩

instance : Monoid (G →+c[a, a] G) :=
  DFunLike.coe_injective.monoid (M₂ := Function.End G) _ rfl (fun _ _ ↦ rfl) fun _ _ ↦ rfl

@[target] theorem mul_def {f g : MonoidAlgebra k G} :
    f * g = f.sum fun a₁ b₁ => g.sum fun a₂ b₂ => single (a₁ * a₂) (b₁ * b₂) := by
  sorry

@[simp, push_cast] theorem coe_mul (f g : G →+c[a, a] G) : ⇑(f * g) = f ∘ g := rfl

@[target] theorem one_def : (1 : MonoidAlgebra k G) = single 1 1 := by sorry

@[target] theorem coe_one : (↑(1 : R) : A) = 1 := by sorry


@[target] theorem coe_pow (a : R) (n : ℕ) : (↑(a ^ n : R) : A) = (a : A) ^ n := by sorry


theorem pow_apply (f : G →+c[a, a] G) (n : ℕ) (x : G) : (f ^ n) x = f^[n] x := rfl

/-- Coercion to functions as a monoid homomorphism to `Function.End G`. -/
/-- Turn a centroid homomorphism into an additive monoid endomorphism. -/
def toEnd (f : CentroidHom α) : AddMonoid.End α := by sorry


end Add

section AddZeroClass

variable {G H K : Type*} [Add G] [AddZeroClass H] {a : G} {b : H}

/-!
### Multiplicative action on `(b : H) × (G →+c[a, b] H)`

If `K` acts distributively on `H`, then for each `f : G →+c[a, b] H`
we define `(AddConstMap.smul c f : G →+c[a, c • b] H)`.

One can show that this defines a multiplicative action of `K` on `(b : H) × (G →+c[a, b] H)`
but we don't do this at the moment because we don't need this.
-/

/-- Pointwise scalar multiplication of `f : G →+c[a, b] H` as a map `G →+c[a, c • b] H`. -/
@[to_additive]
protected theorem Periodic.smul [Add α] [SMul γ β] (h : Periodic f c) (a : γ) :
    Periodic (a • f) c := by sorry


end AddZeroClass

section AddMonoid

variable {G : Type*} [AddMonoid G] {a : G}

/-- The map that sends `c` to a translation by `c`
as a monoid homomorphism from `Multiplicative G` to `G →+c[a, a] G`. -/
/-- The map that sends `c` to a translation by `c`
as a monoid homomorphism from `Multiplicative G` to `G →+c[a, a] G`. -/
@[simps! (config := .asFn)]
def addLeftHom : Multiplicative G →* (G →+c[a, a] G) where
  toFun c := c.toAdd +ᵥ .id
  map_one' := by sorry


end AddMonoid

section AddCommGroup

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H] {a : G} {b : H}

/-- If `f : G → H` is an `AddConstMap`, then so is `fun x ↦ -f (-x)`. -/
/-- If `f : G → H` is an `AddConstMap`, then so is `fun x ↦ -f (-x)`. -/
@[simps! apply_coe]
def conjNeg : (G →+c[a, b] H) ≃ (G →+c[a, b] H) :=
  Involutive.toPerm (fun f ↦ ⟨fun x ↦ - f (-x), fun _ ↦ by sorry


@[target] theorem conjNeg_symm : (conjNeg (a := by sorry


end AddCommGroup

section FloorRing

variable {R G : Type*} [LinearOrderedRing R] [FloorRing R] [AddGroup G] (a : G)

/-- A map `f : R →+c[1, a] G` is defined by its values on `Set.Ico 0 1`. -/
/-- A map `f : R →+c[1, a] G` is defined by its values on `Set.Ico 0 1`. -/
def mkFract : (Ico (0 : R) 1 → G) ≃ (R →+c[1, a] G) where
  toFun f := ⟨fun x ↦ f ⟨Int.fract x, Int.fract_nonneg _, Int.fract_lt_one _⟩ + ⌊x⌋ • a, fun x ↦ by
    sorry


end FloorRing

end AddConstMap
