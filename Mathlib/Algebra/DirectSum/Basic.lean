import VerifiedAgora.tagger
/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.Group.Submonoid.Operations
import Mathlib.Data.DFinsupp.Sigma
import Mathlib.Data.DFinsupp.Submonoid

/-!
# Direct sum

This file defines the direct sum of abelian groups, indexed by a discrete type.

## Notation

`⨁ i, β i` is the n-ary direct sum `DirectSum`.
This notation is in the `DirectSum` locale, accessible after `open DirectSum`.

## References

* https://en.wikipedia.org/wiki/Direct_sum
-/

open Function

universe u v w u₁

variable (ι : Type v) (β : ι → Type w)

/-- `DirectSum ι β` is the direct sum of a family of additive commutative monoids `β i`.

Note: `open DirectSum` will enable the notation `⨁ i, β i` for `DirectSum ι β`. -/
/-- `DirectSum ι β` is the direct sum of a family of additive commutative monoids `β i`.

Note: `open DirectSum` will enable the notation `⨁ i, β i` for `DirectSum ι β`. -/
def DirectSum [∀ i, AddCommMonoid (β i)] : Type _ := by sorry

instance [∀ i, AddCommMonoid (β i)] : Inhabited (DirectSum ι β) :=
  inferInstanceAs (Inhabited (Π₀ i, β i))

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/10754): Added addCommMonoid instance manually
instance [∀ i, AddCommMonoid (β i)] : AddCommMonoid (DirectSum ι β) :=
  inferInstanceAs (AddCommMonoid (Π₀ i, β i))

instance [∀ i, AddCommMonoid (β i)] : DFunLike (DirectSum ι β) _ fun i : ι => β i :=
  inferInstanceAs (DFunLike (Π₀ i, β i) _ _)

instance [∀ i, AddCommMonoid (β i)] : CoeFun (DirectSum ι β) fun _ => ∀ i : ι, β i :=
  inferInstanceAs (CoeFun (Π₀ i, β i) fun _ => ∀ i : ι, β i)

/-- `⨁ i, f i` is notation for `DirectSum _ f` and equals the direct sum of `fun i ↦ f i`.
Taking the direct sum over multiple arguments is possible, e.g. `⨁ (i) (j), f i j`. -/
scoped[DirectSum] notation3 "⨁ "(...)", "r:(scoped f => DirectSum _ f) => r

-- Porting note: The below recreates some of the lean3 notation, not fully yet
-- section
-- open Batteries.ExtendedBinder
-- syntax (name := bigdirectsum) "⨁ " extBinders ", " term : term
-- macro_rules (kind := bigdirectsum)
--   | `(⨁ $_:ident, $y:ident → $z:ident) => `(DirectSum _ (fun $y ↦ $z))
--   | `(⨁ $x:ident, $p) => `(DirectSum _ (fun $x ↦ $p))
--   | `(⨁ $_:ident : $t:ident, $p) => `(DirectSum _ (fun $t ↦ $p))
--   | `(⨁ ($x:ident) ($y:ident), $p) => `(DirectSum _ (fun $x ↦ fun $y ↦ $p))
-- end

instance [DecidableEq ι] [∀ i, AddCommMonoid (β i)] [∀ i, DecidableEq (β i)] :
    DecidableEq (DirectSum ι β) :=
  inferInstanceAs <| DecidableEq (Π₀ i, β i)

namespace DirectSum

variable {ι}

section AddCommGroup

variable [∀ i, AddCommGroup (β i)]

instance : AddCommGroup (DirectSum ι β) :=
  inferInstanceAs (AddCommGroup (Π₀ i, β i))
variable {β}

@[target] theorem sub_apply (f g : CentroidHom α) (a : α) : (f - g) a = f a - g a := by sorry


end AddCommGroup

variable [∀ i, AddCommMonoid (β i)]

@[target] theorem Algebra.ext {S : Type u} {A : Type v} [CommSemiring S] [Semiring A] (h1 h2 : Algebra S A)
    (h : ∀ (r : S) (x : A), (by sorry


@[target] theorem zero_apply (a : A) : (0 : A →ₛₙₐ[φ] B) a = 0 := by sorry


variable {β}

@[target] theorem add_apply (f g : CentroidHom α) (a : α) : (f + g) a = f a + g a := by sorry


section DecidableEq

variable [DecidableEq ι]

variable (β)

/-- `mk β s x` is the element of `⨁ i, β i` that is zero outside `s`
and has coefficient `x i` for `i` in `s`. -/
/-- A constructor for a subbimodule which demands closure under the two sets of scalars
individually, rather than jointly via their tensor product.

Note that `R` plays no role but it is convenient to make this generalisation to support the cases
`R = ℕ` and `R = ℤ` which both show up naturally. See also `Subbimodule.baseChange`. -/
@[simps]
def mk (p : AddSubmonoid M) (hA : ∀ (a : A) {m : M}, m ∈ p → a • m ∈ p)
    (hB : ∀ (b : B) {m : M}, m ∈ p → b • m ∈ p) : Submodule (A ⊗[R] B) M :=
  { p with
    carrier := p
    smul_mem' := fun ab m =>
      TensorProduct.induction_on ab (fun _ => by sorry


/-- `of i` is the natural inclusion map from `β i` to `⨁ i, β i`. -/
/-- Embeds an element of `α` into `FreeMonoid α` as a singleton list. -/
@[to_additive "Embeds an element of `α` into `FreeAddMonoid α` as a singleton list."]
def of (x : α) : FreeMonoid α := by sorry


variable {β}

@[target] theorem of_eq_same (i : ι) (x : β i) : (of _ i x) i = x := by sorry


@[target] theorem of_eq_of_ne (i j : ι) (x : β i) (h : i ≠ j) : (of _ i x) j = 0 := by sorry


/-- The embedding of a unital magma into its magma algebra. -/
@[simps]
def of [MulOneClass G] : G →* MonoidAlgebra k G := by sorry


@[target] theorem mk_apply_of_mem {s : Finset ι} {f : ∀ i : (↑s : Set ι), β i.val} {n : ι} (hn : n ∈ s) :
    mk β s f n = f ⟨n, hn⟩ := by
  sorry


@[target] theorem mk_apply_of_not_mem {s : Finset ι} {f : ∀ i : (↑s : Set ι), β i.val} {n : ι} (hn : n ∉ s) :
    mk β s f n = 0 := by
  sorry


@[to_additive (attr := by sorry


@[simp]
theorem support_of [∀ (i : ι) (x : β i), Decidable (x ≠ 0)] (i : ι) (x : β i) (h : x ≠ 0) :
    (of _ i x).support = {i} :=
  DFinsupp.support_single_ne_zero h

@[target] theorem support_of_subset [∀ (i : ι) (x : β i), Decidable (x ≠ 0)] {i : ι} {b : β i} :
    (of _ i b).support ⊆ {i} := by sorry


theorem sum_support_of [∀ (i : ι) (x : β i), Decidable (x ≠ 0)] (x : ⨁ i, β i) :
    (∑ i ∈ x.support, of β i (x i)) = x :=
  DFinsupp.sum_single

theorem sum_univ_of [Fintype ι] (x : ⨁ i, β i) :
    ∑ i ∈ Finset.univ, of β i (x i) = x := by
  apply DFinsupp.ext (fun i ↦ ?_)
  rw [DFinsupp.finset_sum_apply]
  simp [of_apply]

@[target] theorem mk_injective [Monoid M] [Subsingleton Mˣ] : Function.Injective (@Associates.mk M _) := by sorry


@[target] theorem of_injective : Function.Injective (@of α) := by sorry


@[elab_as_elim]
protected theorem induction_on {C : (⨁ i, β i) → Prop} (x : ⨁ i, β i) (H_zero : C 0)
    (H_basic : ∀ (i : ι) (x : β i), C (of β i x))
    (H_plus : ∀ x y, C x → C y → C (x + y)) : C x := by
  apply DFinsupp.induction x H_zero
  intro i b f h1 h2 ih
  solve_by_elim

/-- If two additive homomorphisms from `⨁ i, β i` are equal on each `of β i y`,
then they are equal. -/
/-- If two additive homomorphisms from `⨁ i, β i` are equal on each `of β i y`,
then they are equal. -/
@[target] theorem addHom_ext {γ : Type*} [AddMonoid γ] ⦃f g : (⨁ i, β i) →+ γ⦄
    (H : ∀ (i : ι) (y : β i), f (of _ i y) = g (of _ i y)) : f = g := by sorry


/-- If two additive homomorphisms from `⨁ i, β i` are equal on each `of β i y`,
then they are equal.

See note [partially-applied ext lemmas]. -/
@[ext high]
theorem addHom_ext' {γ : Type*} [AddMonoid γ] ⦃f g : (⨁ i, β i) →+ γ⦄
    (H : ∀ i : ι, f.comp (of _ i) = g.comp (of _ i)) : f = g :=
  addHom_ext fun i => DFunLike.congr_fun <| H i

variable {γ : Type u₁} [AddCommMonoid γ]

section ToAddMonoid

variable (φ : ∀ i, β i →+ γ) (ψ : (⨁ i, β i) →+ γ)

-- Porting note: The elaborator is struggling with `liftAddHom`. Passing it `β` explicitly helps.
-- This applies to roughly the remainder of the file.

/-- `toAddMonoid φ` is the natural homomorphism from `⨁ i, β i` to `γ`
induced by a family `φ` of homomorphisms `β i → γ`. -/
/-- `toAddMonoid φ` is the natural homomorphism from `⨁ i, β i` to `γ`
induced by a family `φ` of homomorphisms `β i → γ`. -/
def toAddMonoid : (⨁ i, β i) →+ γ := by sorry


@[target] theorem toAddMonoid_of (i) (x : β i) : toAddMonoid φ (of β i x) = φ i x := by sorry


theorem toAddMonoid.unique (f : ⨁ i, β i) : ψ f = toAddMonoid (fun i => ψ.comp (of β i)) f := by
  congr
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` applies addHom_ext' here, which isn't what we want.
  apply DFinsupp.addHom_ext'
  simp [toAddMonoid, of]

@[target] theorem CommMonoid.toMonoid_injective {M : Type u} :
    Function.Injective (@CommMonoid.toMonoid M) := by
  sorry


@[target] lemma toAddMonoid_inj {f g : ∀ i, β i →+ γ} : toAddMonoid f = toAddMonoid g ↔ f = g := by sorry


end ToAddMonoid

section FromAddMonoid

/-- `fromAddMonoid φ` is the natural homomorphism from `γ` to `⨁ i, β i`
induced by a family `φ` of homomorphisms `γ → β i`.

Note that this is not an isomorphism. Not every homomorphism `γ →+ ⨁ i, β i` arises in this way. -/
def fromAddMonoid : (⨁ i, γ →+ β i) →+ γ →+ ⨁ i, β i :=
  toAddMonoid fun i => AddMonoidHom.compHom (of β i)

@[target] theorem fromAddMonoid_of (i : ι) (f : γ →+ β i) : fromAddMonoid (of _ i f) = (of _ i).comp f := by
  sorry


@[target] theorem fromAddMonoid_of_apply (i : ι) (f : γ →+ β i) (x : γ) :
    fromAddMonoid (of _ i f) x = of _ i (f x) := by
      sorry


end FromAddMonoid

variable (β)

-- TODO: generalize this to remove the assumption `S ⊆ T`.
/-- `setToSet β S T h` is the natural homomorphism `⨁ (i : S), β i → ⨁ (i : T), β i`,
where `h : S ⊆ T`. -/
/-- `setToSet β S T h` is the natural homomorphism `⨁ (i : S), β i → ⨁ (i : T), β i`,
where `h : S ⊆ T`. -/
def setToSet (S T : Set ι) (H : S ⊆ T) : (⨁ i : S, β i) →+ ⨁ i : T, β i := by sorry


end DecidableEq

instance unique [∀ i, Subsingleton (β i)] : Unique (⨁ i, β i) :=
  DFinsupp.unique

/-- A direct sum over an empty type is trivial. -/
instance uniqueOfIsEmpty [IsEmpty ι] : Unique (⨁ i, β i) :=
  DFinsupp.uniqueOfIsEmpty

/-- The natural equivalence between `⨁ _ : ι, M` and `M` when `Unique ι`. -/
protected def id (M : Type v) (ι : Type* := PUnit) [AddCommMonoid M] [Unique ι] :
    (⨁ _ : ι, M) ≃+ M :=
  {
    DirectSum.toAddMonoid fun _ =>
      AddMonoidHom.id
        M with
    toFun := DirectSum.toAddMonoid fun _ => AddMonoidHom.id M
    invFun := of (fun _ => M) default
    left_inv := fun x =>
      DirectSum.induction_on x (by rw [AddMonoidHom.map_zero, AddMonoidHom.map_zero])
        (fun p x => by rw [Unique.default_eq p, toAddMonoid_of]; rfl) fun x y ihx ihy => by
        rw [AddMonoidHom.map_add, AddMonoidHom.map_add, ihx, ihy]
    right_inv := fun _ => toAddMonoid_of _ _ _ }

section CongrLeft

variable {κ : Type*}

/-- Reindexing terms of a direct sum. -/
/-- Reindexing terms of a direct sum. -/
def equivCongrLeft (h : ι ≃ κ) : (⨁ i, β i) ≃+ ⨁ k, β (h.symm k) := by sorry


@[target] theorem equivCongrLeft_apply (h : ι ≃ κ) (f : ⨁ i, β i) (k : κ) :
    equivCongrLeft h f k = f (h.symm k) := by
  sorry


end CongrLeft

section Option

variable {α : Option ι → Type w} [∀ i, AddCommMonoid (α i)]

/-- Isomorphism obtained by separating the term of index `none` of a direct sum over `Option ι`. -/
@[simps!]
noncomputable def addEquivProdDirectSum : (⨁ i, α i) ≃+ α none × ⨁ i, α (some i) :=
  { DFinsupp.equivProdDFinsupp with map_add' := DFinsupp.equivProdDFinsupp_add }

end Option

section Sigma

variable [DecidableEq ι] {α : ι → Type u} {δ : ∀ i, α i → Type w} [∀ i j, AddCommMonoid (δ i j)]

/-- The natural map between `⨁ (i : Σ i, α i), δ i.1 i.2` and `⨁ i (j : α i), δ i j`. -/
/-- The natural map between `⨁ (i : Σ i, α i), δ i.1 i.2` and `⨁ i (j : α i), δ i j`. -/
def sigmaCurry : (⨁ i : Σ _i, _, δ i.1 i.2) →+ ⨁ (i) (j), δ i j where
  toFun := by sorry


@[simp]
theorem sigmaCurry_apply (f : ⨁ i : Σ _i, _, δ i.1 i.2) (i : ι) (j : α i) :
    sigmaCurry f i j = f ⟨i, j⟩ :=
  DFinsupp.sigmaCurry_apply (δ := δ) _ i j

/-- The natural map between `⨁ i (j : α i), δ i j` and `Π₀ (i : Σ i, α i), δ i.1 i.2`, inverse of
`curry`. -/
def sigmaUncurry : (⨁ (i) (j), δ i j) →+ ⨁ i : Σ _i, _, δ i.1 i.2 where
  toFun := DFinsupp.sigmaUncurry
  map_zero' := DFinsupp.sigmaUncurry_zero
  map_add' := DFinsupp.sigmaUncurry_add

@[target] theorem sigmaUncurry_apply (f : ⨁ (i) (j), δ i j) (i : ι) (j : α i) :
    sigmaUncurry f ⟨i, j⟩ = f i j := by sorry


/-- The natural map between `⨁ (i : Σ i, α i), δ i.1 i.2` and `⨁ i (j : α i), δ i j`. -/
/-- The natural map between `⨁ (i : Σ i, α i), δ i.1 i.2` and `⨁ i (j : α i), δ i j`. -/
def sigmaCurryEquiv : (⨁ i : Σ _i, _, δ i.1 i.2) ≃+ ⨁ (i) (j), δ i j := by sorry


end Sigma

/-- The canonical embedding from `⨁ i, A i` to `M` where `A` is a collection of `AddSubmonoid M`
indexed by `ι`.

When `S = Submodule _ M`, this is available as a `LinearMap`, `DirectSum.coe_linearMap`. -/
protected def coeAddMonoidHom {M S : Type*} [DecidableEq ι] [AddCommMonoid M] [SetLike S M]
    [AddSubmonoidClass S M] (A : ι → S) : (⨁ i, A i) →+ M :=
  toAddMonoid fun i => AddSubmonoidClass.subtype (A i)

@[target] theorem coeAddMonoidHom_eq_dfinsupp_sum [DecidableEq ι]
    {M S : Type*} [DecidableEq M] [AddCommMonoid M]
    [SetLike S M] [AddSubmonoidClass S M] (A : ι → S) (x : DirectSum ι fun i => A i) :
    DirectSum.coeAddMonoidHom A x = DFinsupp.sum x fun i => (fun x : A i => ↑x) := by
  sorry


@[target] theorem coeAddMonoidHom_of {M S : Type*} [DecidableEq ι] [AddCommMonoid M] [SetLike S M]
    [AddSubmonoidClass S M] (A : ι → S) (i : ι) (x : A i) :
    DirectSum.coeAddMonoidHom A (of (fun i => A i) i x) = x := by sorry


@[target] theorem coe_of_apply {M S : Type*} [DecidableEq ι] [AddCommMonoid M] [SetLike S M]
    [AddSubmonoidClass S M] {A : ι → S} (i j : ι) (x : A i) :
    (of (fun i ↦ {x // x ∈ A i}) i x j : M) = if i = j then x else 0 := by
  sorry


/-- The `DirectSum` formed by a collection of additive submonoids (or subgroups, or submodules) of
`M` is said to be internal if the canonical map `(⨁ i, A i) →+ M` is bijective.

For the alternate statement in terms of independence and spanning, see
`DirectSum.subgroup_isInternal_iff_iSupIndep_and_supr_eq_top` and
`DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top`. -/
def IsInternal {M S : Type*} [DecidableEq ι] [AddCommMonoid M] [SetLike S M]
    [AddSubmonoidClass S M] (A : ι → S) : Prop :=
  Function.Bijective (DirectSum.coeAddMonoidHom A)

theorem IsInternal.addSubmonoid_iSup_eq_top {M : Type*} [DecidableEq ι] [AddCommMonoid M]
    (A : ι → AddSubmonoid M) (h : IsInternal A) : iSup A = ⊤ := by
  rw [AddSubmonoid.iSup_eq_mrange_dfinsupp_sumAddHom, AddMonoidHom.mrange_eq_top]
  exact Function.Bijective.surjective h

variable {M S : Type*} [AddCommMonoid M] [SetLike S M] [AddSubmonoidClass S M]

@[target] theorem support_subset [DecidableEq ι] [DecidableEq M] (A : ι → S) (x : DirectSum ι fun i => A i) :
    (Function.support fun i => (x i : M)) ⊆ ↑(DFinsupp.support x) := by
  sorry


@[target] theorem finite_support (A : ι → S) (x : DirectSum ι fun i => A i) :
    (Function.support fun i => (x i : M)).Finite := by
  sorry

  classical
  exact (DFinsupp.support x).finite_toSet.subset (DirectSum.support_subset _ x)

end DirectSum

/-- The canonical isomorphism of a finite direct sum of additive commutative monoids
and the corresponding finite product. -/
def DirectSum.addEquivProd {ι : Type*} [Fintype ι] (G : ι → Type*) [(i : ι) → AddCommMonoid (G i)] :
    DirectSum ι G ≃+ ((i : ι) → G i) :=
  ⟨DFinsupp.equivFunOnFintype, fun g h ↦ funext fun _ ↦ by
    simp only [DFinsupp.equivFunOnFintype, Equiv.toFun_as_coe, Equiv.coe_fn_mk, add_apply,
      Pi.add_apply]⟩
