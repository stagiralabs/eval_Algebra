import VerifiedAgora.tagger
/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Chris Hughes, Mario Carneiro, Yury Kudryashov
-/
import Mathlib.Data.Int.Cast.Prod
import Mathlib.Algebra.GroupWithZero.Prod
import Mathlib.Algebra.Ring.CompTypeclasses
import Mathlib.Algebra.Ring.Equiv

/-!
# Semiring, ring etc structures on `R × S`

In this file we define two-binop (`Semiring`, `Ring` etc) structures on `R × S`. We also prove
trivial `simp` lemmas, and define the following operations on `RingHom`s and similarly for
`NonUnitalRingHom`s:

* `fst R S : R × S →+* R`, `snd R S : R × S →+* S`: projections `Prod.fst` and `Prod.snd`
  as `RingHom`s;
* `f.prod g : R →+* S × T`: sends `x` to `(f x, g x)`;
* `f.prod_map g : R × S → R' × S'`: `Prod.map f g` as a `RingHom`,
  sends `(x, y)` to `(f x, g y)`.
-/


variable {R R' S S' T : Type*}

namespace Prod

/-- Product of two distributive types is distributive. -/
instance instDistrib [Distrib R] [Distrib S] : Distrib (R × S) :=
  { left_distrib := fun _ _ _ => mk.inj_iff.mpr ⟨left_distrib _ _ _, left_distrib _ _ _⟩
    right_distrib := fun _ _ _ => mk.inj_iff.mpr ⟨right_distrib _ _ _, right_distrib _ _ _⟩ }

/-- Product of two `NonUnitalNonAssocSemiring`s is a `NonUnitalNonAssocSemiring`. -/
instance instNonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] :
    NonUnitalNonAssocSemiring (R × S) :=
  { inferInstanceAs (AddCommMonoid (R × S)),
    inferInstanceAs (Distrib (R × S)),
    inferInstanceAs (MulZeroClass (R × S)) with }

/-- Product of two `NonUnitalSemiring`s is a `NonUnitalSemiring`. -/
instance instNonUnitalSemiring [NonUnitalSemiring R] [NonUnitalSemiring S] :
    NonUnitalSemiring (R × S) :=
  { inferInstanceAs (NonUnitalNonAssocSemiring (R × S)),
    inferInstanceAs (SemigroupWithZero (R × S)) with }

/-- Product of two `NonAssocSemiring`s is a `NonAssocSemiring`. -/
instance instNonAssocSemiring [NonAssocSemiring R] [NonAssocSemiring S] :
    NonAssocSemiring (R × S) :=
  { inferInstanceAs (NonUnitalNonAssocSemiring (R × S)),
    inferInstanceAs (MulZeroOneClass (R × S)),
    inferInstanceAs (AddMonoidWithOne (R × S)) with }

/-- Product of two semirings is a semiring. -/
instance instSemiring [Semiring R] [Semiring S] : Semiring (R × S) :=
  { inferInstanceAs (NonUnitalSemiring (R × S)),
    inferInstanceAs (NonAssocSemiring (R × S)),
    inferInstanceAs (MonoidWithZero (R × S)) with }

/-- Product of two `NonUnitalCommSemiring`s is a `NonUnitalCommSemiring`. -/
instance instNonUnitalCommSemiring [NonUnitalCommSemiring R] [NonUnitalCommSemiring S] :
    NonUnitalCommSemiring (R × S) :=
  { inferInstanceAs (NonUnitalSemiring (R × S)), inferInstanceAs (CommSemigroup (R × S)) with }

/-- Product of two commutative semirings is a commutative semiring. -/
instance instCommSemiring [CommSemiring R] [CommSemiring S] : CommSemiring (R × S) :=
  { inferInstanceAs (Semiring (R × S)), inferInstanceAs (CommMonoid (R × S)) with }

instance instNonUnitalNonAssocRing [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S] :
    NonUnitalNonAssocRing (R × S) :=
  { inferInstanceAs (AddCommGroup (R × S)),
    inferInstanceAs (NonUnitalNonAssocSemiring (R × S)) with }

instance instNonUnitalRing [NonUnitalRing R] [NonUnitalRing S] : NonUnitalRing (R × S) :=
  { inferInstanceAs (NonUnitalNonAssocRing (R × S)),
    inferInstanceAs (NonUnitalSemiring (R × S)) with }

instance instNonAssocRing [NonAssocRing R] [NonAssocRing S] : NonAssocRing (R × S) :=
  { inferInstanceAs (NonUnitalNonAssocRing (R × S)),
    inferInstanceAs (NonAssocSemiring (R × S)),
    inferInstanceAs (AddGroupWithOne (R × S)) with }

/-- Product of two rings is a ring. -/
instance instRing [Ring R] [Ring S] : Ring (R × S) :=
  { inferInstanceAs (Semiring (R × S)),
    inferInstanceAs (AddCommGroup (R × S)),
    inferInstanceAs (AddGroupWithOne (R × S)) with }

/-- Product of two `NonUnitalCommRing`s is a `NonUnitalCommRing`. -/
instance instNonUnitalCommRing [NonUnitalCommRing R] [NonUnitalCommRing S] :
    NonUnitalCommRing (R × S) :=
  { inferInstanceAs (NonUnitalRing (R × S)), inferInstanceAs (CommSemigroup (R × S)) with }

/-- Product of two commutative rings is a commutative ring. -/
instance instCommRing [CommRing R] [CommRing S] : CommRing (R × S) :=
  { inferInstanceAs (Ring (R × S)), inferInstanceAs (CommMonoid (R × S)) with }

end Prod

namespace NonUnitalRingHom

variable (R S) [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S]

/-- Given non-unital semirings `R`, `S`, the natural projection homomorphism from `R × S` to `R`. -/
/-- First projection as `AlgHom`. -/
def fst : A × B →ₐ[R] A := by sorry


/-- Given non-unital semirings `R`, `S`, the natural projection homomorphism from `R × S` to `S`. -/
/-- Second projection as `AlgHom`. -/
def snd : A × B →ₐ[R] B := by sorry


variable {R S}

@[target] theorem coe_fst : ⇑(fst R S) = Prod.fst := by sorry


@[target] theorem coe_snd : ⇑(snd R S) = Prod.snd := by sorry


section Prod

variable [NonUnitalNonAssocSemiring T] (f : R →ₙ+* S) (g : R →ₙ+* T)

/-- Combine two non-unital ring homomorphisms `f : R →ₙ+* S`, `g : R →ₙ+* T` into
`f.prod g : R →ₙ+* S × T` given by `(f.prod g) x = (f x, g x)` -/
protected def prod (f : R →ₙ+* S) (g : R →ₙ+* T) : R →ₙ+* S × T :=
  { MulHom.prod (f : MulHom R S) (g : MulHom R T), AddMonoidHom.prod (f : R →+ S) (g : R →+ T) with
    toFun := fun x => (f x, g x) }

/-- The `Pi.prod` of two morphisms is a morphism. -/
@[simps!]
def prod (f : A →ₐ[R] B) (g : A →ₐ[R] C) : A →ₐ[R] B × C :=
  { f.toRingHom.prod g.toRingHom with
    commutes' := fun r => by
      sorry


@[target] theorem fst_comp_prod : (fst S T).comp (f.prod g) = f := by sorry


@[target] theorem snd_comp_prod : (snd S T).comp (f.prod g) = g := by sorry


@[target] theorem prod_unique (f : R →ₙ+* S × T) : ((fst S T).comp f).prod ((snd S T).comp f) = f :=
  ext fun x => by sorry


end Prod

section prodMap

variable [NonUnitalNonAssocSemiring R'] [NonUnitalNonAssocSemiring S'] [NonUnitalNonAssocSemiring T]
variable (f : R →ₙ+* R') (g : S →ₙ+* S')

/-- `Prod.map` as a `NonUnitalRingHom`. -/
/-- `Prod.map` of two algebra homomorphisms. -/
def prodMap {D : Type*} [Semiring D] [Algebra R D] (f : A →ₐ[R] B) (g : C →ₐ[R] D) :
    A × C →ₐ[R] B × D :=
  { toRingHom := f.toRingHom.prodMap g.toRingHom
    commutes' := fun r => by sorry


@[target] theorem prodMap_def : prodMap f g = (f.comp (fst R S)).prod (g.comp (snd R S)) := by sorry


@[target] theorem coe_prodMap : ⇑(prodMap f g) = Prod.map f g := by sorry


@[target] theorem prod_comp_prodMap (f : T →ₙ+* R) (g : T →ₙ+* S) (f' : R →ₙ+* R') (g' : S →ₙ+* S') :
    (f'.prodMap g').comp (f.prod g) = (f'.comp f).prod (g'.comp g) := by sorry


end prodMap

end NonUnitalRingHom

namespace RingHom

variable (R S) [NonAssocSemiring R] [NonAssocSemiring S]

/-- Given semirings `R`, `S`, the natural projection homomorphism from `R × S` to `R`. -/
def fst : R × S →+* R :=
  { MonoidHom.fst R S, AddMonoidHom.fst R S with toFun := Prod.fst }

/-- Given semirings `R`, `S`, the natural projection homomorphism from `R × S` to `S`. -/
def snd : R × S →+* S :=
  { MonoidHom.snd R S, AddMonoidHom.snd R S with toFun := Prod.snd }

instance (R S) [Semiring R] [Semiring S] : RingHomSurjective (fst R S) := ⟨(⟨⟨·, 0⟩, rfl⟩)⟩
instance (R S) [Semiring R] [Semiring S] : RingHomSurjective (snd R S) := ⟨(⟨⟨0, ·⟩, rfl⟩)⟩

variable {R S}

@[simp]
theorem coe_fst : ⇑(fst R S) = Prod.fst :=
  rfl

@[simp]
theorem coe_snd : ⇑(snd R S) = Prod.snd :=
  rfl

section Prod

variable [NonAssocSemiring T] (f : R →+* S) (g : R →+* T)

/-- Combine two ring homomorphisms `f : R →+* S`, `g : R →+* T` into `f.prod g : R →+* S × T`
given by `(f.prod g) x = (f x, g x)` -/
protected def prod (f : R →+* S) (g : R →+* T) : R →+* S × T :=
  { MonoidHom.prod (f : R →* S) (g : R →* T), AddMonoidHom.prod (f : R →+ S) (g : R →+ T) with
    toFun := fun x => (f x, g x) }

@[simp]
theorem prod_apply (x) : f.prod g x = (f x, g x) :=
  rfl

@[simp]
theorem fst_comp_prod : (fst S T).comp (f.prod g) = f :=
  ext fun _ => rfl

@[simp]
theorem snd_comp_prod : (snd S T).comp (f.prod g) = g :=
  ext fun _ => rfl

theorem prod_unique (f : R →+* S × T) : ((fst S T).comp f).prod ((snd S T).comp f) = f :=
  ext fun x => by simp only [prod_apply, coe_fst, coe_snd, comp_apply]

end Prod

section prodMap

variable [NonAssocSemiring R'] [NonAssocSemiring S'] [NonAssocSemiring T]
variable (f : R →+* R') (g : S →+* S')

/-- `Prod.map` as a `RingHom`. -/
def prodMap : R × S →+* R' × S' :=
  (f.comp (fst R S)).prod (g.comp (snd R S))

theorem prodMap_def : prodMap f g = (f.comp (fst R S)).prod (g.comp (snd R S)) :=
  rfl

@[simp]
theorem coe_prodMap : ⇑(prodMap f g) = Prod.map f g :=
  rfl

theorem prod_comp_prodMap (f : T →+* R) (g : T →+* S) (f' : R →+* R') (g' : S →+* S') :
    (f'.prodMap g').comp (f.prod g) = (f'.comp f).prod (g'.comp g) :=
  rfl

end prodMap

end RingHom

namespace RingEquiv

variable [NonAssocSemiring R] [NonAssocSemiring S] [NonAssocSemiring R'] [NonAssocSemiring S']

/-- Swapping components as an equivalence of (semi)rings. -/
/-- Swapping components as an equivalence of (semi)rings. -/
def prodComm : R × S ≃+* S × R := by sorry


@[target] theorem coe_prodComm : ⇑(prodComm : R × S ≃+* S × R) = Prod.swap := by sorry


@[target] theorem coe_prodComm_symm : ⇑(prodComm : R × S ≃+* S × R).symm = Prod.swap := by sorry


@[target] theorem fst_comp_coe_prodComm :
    (RingHom.fst S R).comp ↑(prodComm : R × S ≃+* S × R) = RingHom.snd R S := by sorry


@[target] theorem snd_comp_coe_prodComm :
    (RingHom.snd S R).comp ↑(prodComm : R × S ≃+* S × R) = RingHom.fst R S := by sorry


section

variable (R R' S S')

/-- Four-way commutativity of `Prod`. The name matches `mul_mul_mul_comm`. -/
/-- Four-way commutativity of `Prod`. The name matches `mul_mul_mul_comm`. -/
@[simps apply]
def prodProdProdComm : (R × R') × S × S' ≃+* (R × S) × R' × S' := by sorry


@[target] theorem prodProdProdComm_symm : (prodProdProdComm R R' S S').symm = prodProdProdComm R S R' S' := by sorry


@[target] theorem prodProdProdComm_toAddEquiv :
    (prodProdProdComm R R' S S' : _ ≃+ _) = AddEquiv.prodProdProdComm R R' S S' := by sorry


@[target] theorem prodProdProdComm_toMulEquiv :
    (prodProdProdComm R R' S S' : _ ≃* _) = MulEquiv.prodProdProdComm R R' S S' := by sorry


@[target] theorem prodProdProdComm_toEquiv :
    (prodProdProdComm R R' S S' : _ ≃ _) = Equiv.prodProdProdComm R R' S S' := by sorry


end

variable (R S) [Subsingleton S]

/-- A ring `R` is isomorphic to `R × S` when `S` is the zero ring -/
/-- A ring `R` is isomorphic to `R × S` when `S` is the zero ring -/
@[simps]
def prodZeroRing : R ≃+* R × S where
  toFun x := (x, 0)
  invFun := Prod.fst
  map_add' := by simp
  map_mul' := by simp
  left_inv _ := rfl
  right_inv x := by sorry


/-- A ring `R` is isomorphic to `S × R` when `S` is the zero ring -/
/-- A ring `R` is isomorphic to `S × R` when `S` is the zero ring -/
@[simps]
def zeroRingProd : R ≃+* S × R where
  toFun x := (0, x)
  invFun := Prod.snd
  map_add' := by simp
  map_mul' := by simp
  left_inv _ := rfl
  right_inv x := by sorry


end RingEquiv

/-- The product of two nontrivial rings is not a domain -/
/-- The product of two nontrivial rings is not a domain -/
@[target] theorem false_of_nontrivial_of_product_domain (R S : Type*) [Ring R] [Ring S] [IsDomain (R × S)]
    [Nontrivial R] [Nontrivial S] : False := by
  sorry
