import VerifiedAgora.tagger
/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.AddConstMap.Basic

/-!
# Equivalences conjugating `(· + a)` to `(· + b)`

In this file we define `AddConstEquiv G H a b` (notation: `G ≃+c[a, b] H`)
to be the type of equivalences such that `∀ x, f (x + a) = f x + b`.

We also define the corresponding typeclass and prove some basic properties.
-/

assert_not_exists Finset

open Function
open scoped AddConstMap

/-- An equivalence between `G` and `H` conjugating `(· + a)` to `(· + b)`,
denoted as `G ≃+c[a, b] H`. -/
structure AddConstEquiv (G H : Type*) [Add G] [Add H] (a : G) (b : H)
  extends G ≃ H, G →+c[a, b] H

/-- Interpret an `AddConstEquiv` as an `Equiv`. -/
add_decl_doc AddConstEquiv.toEquiv

/-- Interpret an `AddConstEquiv` as an `AddConstMap`. -/
add_decl_doc AddConstEquiv.toAddConstMap

@[inherit_doc]
scoped [AddConstMap] notation:25 G " ≃+c[" a ", " b "] " H => AddConstEquiv G H a b

namespace AddConstEquiv

variable {G H K : Type*} [Add G] [Add H] [Add K] {a : G} {b : H} {c : K}

lemma toEquiv_injective : Injective (toEquiv : (G ≃+c[a, b] H) → G ≃ H)
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

instance {G H : Type*} [Add G] [Add H] {a : G} {b : H} :
    EquivLike (G ≃+c[a, b] H) G H where
  coe f := f.toEquiv
  inv f := f.toEquiv.symm
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' _ _ h _ := toEquiv_injective <| DFunLike.ext' h

instance {G H : Type*} [Add G] [Add H] {a : G} {b : H} :
    AddConstMapClass (G ≃+c[a, b] H) G H a b where
  map_add_const f x := f.map_add_const' x

@[target] theorem Algebra.ext {S : Type u} {A : Type v} [CommSemiring S] [Semiring A] (h1 h2 : Algebra S A)
    (h : ∀ (r : S) (x : A), (by sorry


@[target] lemma toEquiv_inj {e₁ e₂ : G ≃+c[a, b] H} : e₁.toEquiv = e₂.toEquiv ↔ e₁ = e₂ := by sorry


@[target] theorem coe_toEquiv (f : R ≃+* S) : ⇑(f : R ≃ S) = f := by sorry


/-- Inverse map of an `AddConstEquiv`, as an `AddConstEquiv`. -/
@[target] lemma symm {A B : CSA K} (h : IsBrauerEquivalent A B) : IsBrauerEquivalent B A := by sorry


/-- A custom projection for `simps`. -/
def Simps.symm_apply (e : G ≃+c[a, b] H) : H → G := e.symm

initialize_simps_projections AddConstEquiv (toFun → apply, invFun → symm_apply)

@[target] theorem symm_symm (e : R ≃+* S) : e.symm.symm = e := by sorry


/-- The identity map as an `AddConstEquiv`. -/
@[target] lemma refl (A : CSA K) : IsBrauerEquivalent A A := by sorry


@[target] theorem symm_refl : (RingEquiv.refl R).symm = RingEquiv.refl R := by sorry


/-- Composition of `AddConstEquiv`s, as an `AddConstEquiv`. -/
open Matrix in
@[target] lemma trans {A B C : CSA K} (hAB : IsBrauerEquivalent A B) (hBC : IsBrauerEquivalent B C) :
    IsBrauerEquivalent A C := by
  sorry


@[target] lemma trans_refl (e : G ≃+c[a, b] H) : e.trans (.refl b) = e := by sorry

@[target] lemma refl_trans (e : G ≃+c[a, b] H) : (refl a).trans e = e := by sorry


@[target] theorem self_trans_symm (e : R ≃+* S) : e.trans e.symm = RingEquiv.refl R := by sorry


@[target] theorem symm_trans_self (e : R ≃+* S) : e.symm.trans e = RingEquiv.refl S := by sorry


instance instOne : One (G ≃+c[a, a] G) := ⟨.refl _⟩
instance instMul : Mul (G ≃+c[a, a] G) := ⟨fun f g ↦ g.trans f⟩
instance instInv : Inv (G ≃+c[a, a] G) := ⟨.symm⟩
instance instDiv : Div (G ≃+c[a, a] G) := ⟨fun f g ↦ f * g⁻¹⟩

instance instPowNat : Pow (G ≃+c[a, a] G) ℕ where
  pow e n := ⟨e^n, (e.toAddConstMap^n).map_add_const'⟩

instance instPowInt : Pow (G ≃+c[a, a] G) ℤ where
  pow e n := ⟨e^n,
    match n with
    | .ofNat n => (e^n).map_add_const'
    | .negSucc n => (e.symm^(n + 1)).map_add_const'⟩

instance instGroup : Group (G ≃+c[a, a] G) :=
  toEquiv_injective.group _ rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    fun _ _ ↦ rfl

/-- Projection from `G ≃+c[a, a] G` to permutations `G ≃ G`, as a monoid homomorphism. -/
/-- Monoid homomorphism from ring automorphisms to permutations. -/
def toPerm : RingAut R →* Equiv.Perm R where
  toFun := by sorry


/-- Projection from `G ≃+c[a, a] G` to `G →+c[a, a] G`, as a monoid homomorphism. -/
@[simps! apply]
def toAddConstMapHom : (G ≃+c[a, a] G) →* (G →+c[a, a] G) where
  toFun := toAddConstMap
  map_mul' _ _ := rfl
  map_one' := rfl

/-- Group equivalence between `G ≃+c[a, a] G` and the units of `G →+c[a, a] G`. -/
@[simps!]
def equivUnits : (G ≃+c[a, a] G) ≃* (G →+c[a, a] G)ˣ where
  toFun := toAddConstMapHom.toHomUnits
  invFun u :=
    { toEquiv := Equiv.Perm.equivUnitsEnd.symm <| Units.map AddConstMap.toEnd u
      map_add_const' := u.1.2 }
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

end AddConstEquiv
