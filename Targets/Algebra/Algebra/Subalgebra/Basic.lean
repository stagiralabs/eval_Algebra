import VerifiedAgora.tagger
/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Algebra.Algebra.Operations
import Mathlib.Algebra.Algebra.NonUnitalSubalgebra

/-!
# Subalgebras over Commutative Semiring

In this file we define `Subalgebra`s and the usual operations on them (`map`, `comap`).

More lemmas about `adjoin` can be found in `RingTheory.Adjoin`.
-/

universe u u' v w w'

/-- A subalgebra is a sub(semi)ring that includes the range of `algebraMap`. -/
structure Subalgebra (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] [Algebra R A] extends
  Subsemiring A : Type v where
  /-- The image of `algebraMap` is contained in the underlying set of the subalgebra -/
  algebraMap_mem' : ∀ r, algebraMap R A r ∈ carrier
  zero_mem' := (algebraMap R A).map_zero ▸ algebraMap_mem' 0
  one_mem' := (algebraMap R A).map_one ▸ algebraMap_mem' 1

/-- Reinterpret a `Subalgebra` as a `Subsemiring`. -/
add_decl_doc Subalgebra.toSubsemiring

namespace Subalgebra

variable {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}
variable [CommSemiring R]
variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

instance : SetLike (Subalgebra R A) A where
  coe s := s.carrier
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.coe_injective' h

instance SubsemiringClass : SubsemiringClass (Subalgebra R A) A where
  add_mem {s} := add_mem (s := s.toSubsemiring)
  mul_mem {s} := mul_mem (s := s.toSubsemiring)
  one_mem {s} := one_mem s.toSubsemiring
  zero_mem {s} := zero_mem s.toSubsemiring

initialize_simps_projections Subalgebra (carrier → coe, as_prefix coe)

@[simp]
theorem mem_toSubsemiring {S : Subalgebra R A} {x} : x ∈ S.toSubsemiring ↔ x ∈ S :=
  Iff.rfl

@[target]
theorem mem_carrier {s : Subalgebra R A} {x : A} : x ∈ s.carrier ↔ x ∈ s :=
  sorry

@[ext]
theorem ext {S T : Subalgebra R A} (h : ∀ x : A, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h

@[target, simp]
theorem coe_toSubsemiring (S : Subalgebra R A) : (↑S.toSubsemiring : Set A) = S :=
  sorry

theorem toSubsemiring_injective :
    Function.Injective (toSubsemiring : Subalgebra R A → Subsemiring A) := fun S T h =>
  ext fun x => by rw [← mem_toSubsemiring, ← mem_toSubsemiring, h]

theorem toSubsemiring_inj {S U : Subalgebra R A} : S.toSubsemiring = U.toSubsemiring ↔ S = U :=
  toSubsemiring_injective.eq_iff

/-- Copy of a subalgebra with a new `carrier` equal to the old one. Useful to fix definitional
equalities. -/
@[simps coe toSubsemiring]
protected def copy (S : Subalgebra R A) (s : Set A) (hs : s = ↑S) : Subalgebra R A :=
  { S.toSubsemiring.copy s hs with
    carrier := s
    algebraMap_mem' := hs.symm ▸ S.algebraMap_mem' }

@[target]
theorem copy_eq (S : Subalgebra R A) (s : Set A) (hs : s = ↑S) : S.copy s hs = S :=
  sorry

variable (S : Subalgebra R A)

instance instSMulMemClass : SMulMemClass (Subalgebra R A) R A where
  smul_mem {S} r x hx := (Algebra.smul_def r x).symm ▸ mul_mem (S.algebraMap_mem' r) hx

@[aesop safe apply (rule_sets := [SetLike])]
theorem _root_.algebraMap_mem {S R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    [SetLike S A] [OneMemClass S A] [SMulMemClass S R A] (s : S) (r : R) :
    algebraMap R A r ∈ s :=
  Algebra.algebraMap_eq_smul_one (A := A) r ▸ SMulMemClass.smul_mem r (one_mem s)

protected theorem algebraMap_mem (r : R) : algebraMap R A r ∈ S :=
  algebraMap_mem S r

theorem rangeS_le : (algebraMap R A).rangeS ≤ S.toSubsemiring := fun _x ⟨r, hr⟩ =>
  hr ▸ S.algebraMap_mem r

theorem range_subset : Set.range (algebraMap R A) ⊆ S := fun _x ⟨r, hr⟩ => hr ▸ S.algebraMap_mem r

@[target]
theorem range_le : Set.range (algebraMap R A) ≤ S :=
  sorry

@[target]
theorem smul_mem {x : A} (hx : x ∈ S) (r : R) : r • x ∈ S :=
  sorry
def toNonUnitalSubalgebra (S : Subalgebra R A) : NonUnitalSubalgebra R A where
  __ := S
  smul_mem' r _x hx := S.smul_mem hx r

lemma one_mem_toNonUnitalSubalgebra (S : Subalgebra R A) : (1 : A) ∈ S.toNonUnitalSubalgebra :=
  S.one_mem

instance {R A : Type*} [CommRing R] [Ring A] [Algebra R A] : SubringClass (Subalgebra R A) A :=
  { Subalgebra.SubsemiringClass with
    neg_mem := fun {S x} hx => neg_one_smul R x ▸ S.smul_mem hx _ }

protected theorem neg_mem {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (S : Subalgebra R A) {x : A} (hx : x ∈ S) : -x ∈ S :=
  neg_mem hx

protected theorem sub_mem {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (S : Subalgebra R A) {x y : A} (hx : x ∈ S) (hy : y ∈ S) : x - y ∈ S :=
  sub_mem hx hy

protected theorem zsmul_mem {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (S : Subalgebra R A) {x : A} (hx : x ∈ S) (n : ℤ) : n • x ∈ S :=
  zsmul_mem hx n

protected theorem intCast_mem {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (S : Subalgebra R A) (n : ℤ) : (n : A) ∈ S :=
  intCast_mem S n

/-- The projection from a subalgebra of `A` to an additive submonoid of `A`. -/
@[simps coe]
def toAddSubmonoid {R : Type u} {A : Type v} [CommSemiring R] [Semiring A] [Algebra R A]
    (S : Subalgebra R A) : AddSubmonoid A :=
  S.toSubsemiring.toAddSubmonoid

/-- A subalgebra over a ring is also a `Subring`. -/
@[simps toSubsemiring]
def toSubring {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A] (S : Subalgebra R A) :
    Subring A :=
  { S.toSubsemiring with neg_mem' := S.neg_mem }

@[target, simp]
theorem mem_toSubring {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    {S : Subalgebra R A} {x} : x ∈ S.toSubring ↔ x ∈ S :=
  sorry

@[target, simp]
theorem coe_toSubring {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (S : Subalgebra R A) : (↑S.toSubring : Set A) = S :=
  sorry

theorem toSubring_injective {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A] :
    Function.Injective (toSubring : Subalgebra R A → Subring A) := fun S T h =>
  ext fun x => by rw [← mem_toSubring, ← mem_toSubring, h]

@[target]
theorem toSubring_inj {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    {S U : Subalgebra R A} : S.toSubring = U.toSubring ↔ S = U :=
  sorry

instance : Inhabited S :=
  ⟨(0 : S.toSubsemiring)⟩

section

/-! `Subalgebra`s inherit structure from their `Subsemiring` / `Semiring` coercions. -/


instance toSemiring {R A} [CommSemiring R] [Semiring A] [Algebra R A] (S : Subalgebra R A) :
    Semiring S :=
  S.toSubsemiring.toSemiring

instance toCommSemiring {R A} [CommSemiring R] [CommSemiring A] [Algebra R A] (S : Subalgebra R A) :
    CommSemiring S :=
  S.toSubsemiring.toCommSemiring

instance toRing {R A} [CommRing R] [Ring A] [Algebra R A] (S : Subalgebra R A) : Ring S :=
  S.toSubring.toRing

instance toCommRing {R A} [CommRing R] [CommRing A] [Algebra R A] (S : Subalgebra R A) :
    CommRing S :=
  S.toSubring.toCommRing

end

/-- The forgetful map from `Subalgebra` to `Submodule` as an `OrderEmbedding` -/
def toSubmodule : Subalgebra R A ↪o Submodule R A where
  toEmbedding :=
    { toFun := fun S =>
        { S with
          carrier := S
          smul_mem' := fun c {x} hx ↦
            (Algebra.smul_def c x).symm ▸ mul_mem (S.range_le ⟨c, rfl⟩) hx }
      inj' := fun _ _ h ↦ ext fun x ↦ SetLike.ext_iff.mp h x }
  map_rel_iff' := SetLike.coe_subset_coe.symm.trans SetLike.coe_subset_coe

/- TODO: bundle other forgetful maps between algebraic substructures, e.g.
  `toSubsemiring` and `toSubring` in this file. -/
@[target, simp]
theorem mem_toSubmodule {x} : x ∈ (toSubmodule S) ↔ x ∈ S := sorry

@[target, simp]
theorem coe_toSubmodule (S : Subalgebra R A) : (toSubmodule S : Set A) = S := sorry

@[target]
theorem toSubmodule_injective : Function.Injective (toSubmodule : Subalgebra R A → Submodule R A) :=
  sorry


instance (priority := low) module' [Semiring R'] [SMul R' R] [Module R' A] [IsScalarTower R' R A] :
    Module R' S :=
  S.toSubmodule.module'

instance : Module R S :=
  S.module'

instance [Semiring R'] [SMul R' R] [Module R' A] [IsScalarTower R' R A] : IsScalarTower R' R S :=
  inferInstanceAs (IsScalarTower R' R (toSubmodule S))

/- More general form of `Subalgebra.algebra`.

This instance should have low priority since it is slow to fail:
before failing, it will cause a search through all `SMul R' R` instances,
which can quickly get expensive.
-/
instance (priority := 500) algebra' [CommSemiring R'] [SMul R' R] [Algebra R' A]
    [IsScalarTower R' R A] :
    Algebra R' S where
  algebraMap := (algebraMap R' A).codRestrict S fun x => by
    rw [Algebra.algebraMap_eq_smul_one, ← smul_one_smul R x (1 : A), ←
      Algebra.algebraMap_eq_smul_one]
    exact algebraMap_mem S _
  commutes' := fun _ _ => Subtype.eq <| Algebra.commutes _ _
  smul_def' := fun _ _ => Subtype.eq <| Algebra.smul_def _ _

instance algebra : Algebra R S := S.algebra'

end

instance noZeroSMulDivisors_bot [NoZeroSMulDivisors R A] : NoZeroSMulDivisors R S :=
  ⟨fun {c} {x : S} h =>
    have : c = 0 ∨ (x : A) = 0 := eq_zero_or_eq_zero_of_smul_eq_zero (congr_arg Subtype.val h)
    this.imp_right (@Subtype.ext_iff _ _ x 0).mpr⟩

protected theorem coe_add (x y : S) : (↑(x + y) : A) = ↑x + ↑y := rfl

protected theorem coe_mul (x y : S) : (↑(x * y) : A) = ↑x * ↑y := rfl

protected theorem coe_zero : ((0 : S) : A) = 0 := rfl

protected theorem coe_one : ((1 : S) : A) = 1 := rfl

protected theorem coe_neg {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    {S : Subalgebra R A} (x : S) : (↑(-x) : A) = -↑x := rfl

protected theorem coe_sub {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    {S : Subalgebra R A} (x y : S) : (↑(x - y) : A) = ↑x - ↑y := rfl

@[target, simp, norm_cast]
theorem coe_smul [Semiring R'] [SMul R' R] [Module R' A] [IsScalarTower R' R A] (r : R') (x : S) :
    (↑(r • x) : A) = r • (x : A) := sorry

@[simp, norm_cast]
theorem coe_algebraMap [CommSemiring R'] [SMul R' R] [Algebra R' A] [IsScalarTower R' R A]
    (r : R') : ↑(algebraMap R' S r) = algebraMap R' A r := rfl

protected theorem coe_pow (x : S) (n : ℕ) : (↑(x ^ n) : A) = (x : A) ^ n :=
  SubmonoidClass.coe_pow x n

protected theorem coe_eq_zero {x : S} : (x : A) = 0 ↔ x = 0 :=
  ZeroMemClass.coe_eq_zero

protected theorem coe_eq_one {x : S} : (x : A) = 1 ↔ x = 1 :=
  OneMemClass.coe_eq_one

-- todo: standardize on the names these morphisms
-- compare with submodule.subtype
/-- Embedding of a subalgebra into the algebra. -/
def val : S →ₐ[R] A :=
  { toFun := ((↑) : S → A)
    map_zero' := rfl
    map_one' := rfl
    map_add' := fun _ _ ↦ rfl
    map_mul' := fun _ _ ↦ rfl
    commutes' := fun _ ↦ rfl }

@[simp]
theorem coe_val : (S.val : S → A) = ((↑) : S → A) := rfl

@[target]
theorem val_apply (x : S) : S.val x = (x : A) := sorry

@[simp]
theorem toSubsemiring_subtype : S.toSubsemiring.subtype = (S.val : S →+* A) := rfl

@[simp]
theorem toSubring_subtype {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (S : Subalgebra R A) :
    S.toSubring.subtype = (S.val : S →+* A) := rfl

/-- Linear equivalence between `S : Submodule R A` and `S`. Though these types are equal,
we define it as a `LinearEquiv` to avoid type equalities. -/
def toSubmoduleEquiv (S : Subalgebra R A) : toSubmodule S ≃ₗ[R] S :=
  LinearEquiv.ofEq _ _ rfl

/-- Transport a subalgebra via an algebra homomorphism. -/
@[simps! coe toSubsemiring]
def map (f : A →ₐ[R] B) (S : Subalgebra R A) : Subalgebra R B :=
  { S.toSubsemiring.map (f : A →+* B) with
    algebraMap_mem' := fun r => f.commutes r ▸ Set.mem_image_of_mem _ (S.algebraMap_mem r) }

@[target]
theorem map_mono {S₁ S₂ : Subalgebra R A} {f : A →ₐ[R] B} : S₁ ≤ S₂ → S₁.map f ≤ S₂.map f :=
  sorry

@[target]
theorem map_injective {f : A →ₐ[R] B} (hf : Function.Injective f) : Function.Injective (map f) :=
  sorry

@[simp]
theorem map_id (S : Subalgebra R A) : S.map (AlgHom.id R A) = S :=
  SetLike.coe_injective <| Set.image_id _

@[target]
theorem map_map (S : Subalgebra R A) (g : B →ₐ[R] C) (f : A →ₐ[R] B) :
    (S.map f).map g = S.map (g.comp f) :=
  sorry

@[target, simp]
theorem mem_map {S : Subalgebra R A} {f : A →ₐ[R] B} {y : B} : y ∈ map f S ↔ ∃ x ∈ S, f x = y :=
  sorry

@[target]
theorem map_toSubmodule {S : Subalgebra R A} {f : A →ₐ[R] B} :
    (toSubmodule <| S.map f) = S.toSubmodule.map f.toLinearMap :=
  sorry
@[simps! coe toSubsemiring]
def comap (f : A →ₐ[R] B) (S : Subalgebra R B) : Subalgebra R A :=
  { S.toSubsemiring.comap (f : A →+* B) with
    algebraMap_mem' := fun r =>
      show f (algebraMap R A r) ∈ S from (f.commutes r).symm ▸ S.algebraMap_mem r }

attribute [norm_cast] coe_comap

@[target]
theorem map_le {S : Subalgebra R A} {f : A →ₐ[R] B} {U : Subalgebra R B} :
    map f S ≤ U ↔ S ≤ comap f U :=
  sorry

@[target]
theorem gc_map_comap (f : A →ₐ[R] B) : GaloisConnection (map f) (comap f) := sorry

@[simp]
theorem mem_comap (S : Subalgebra R B) (f : A →ₐ[R] B) (x : A) : x ∈ S.comap f ↔ f x ∈ S :=
  Iff.rfl

instance noZeroDivisors {R A : Type*} [CommSemiring R] [Semiring A] [NoZeroDivisors A]
    [Algebra R A] (S : Subalgebra R A) : NoZeroDivisors S :=
  inferInstanceAs (NoZeroDivisors S.toSubsemiring)

instance isDomain {R A : Type*} [CommRing R] [Ring A] [IsDomain A] [Algebra R A]
    (S : Subalgebra R A) : IsDomain S :=
  inferInstanceAs (IsDomain S.toSubring)

end Subalgebra

namespace SubalgebraClass

variable {S R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
variable [SetLike S A] [SubsemiringClass S A] [hSR : SMulMemClass S R A] (s : S)

instance (priority := 75) toAlgebra : Algebra R s where
  algebraMap := {
    toFun r := ⟨algebraMap R A r, algebraMap_mem s r⟩
    map_one' := Subtype.ext <| by simp
    map_mul' _ _ := Subtype.ext <| by simp
    map_zero' := Subtype.ext <| by simp
    map_add' _ _ := Subtype.ext <| by simp}
  commutes' r x := Subtype.ext <| Algebra.commutes r (x : A)
  smul_def' r x := Subtype.ext <| (algebraMap_smul A r (x : A)).symm

@[target, simp, norm_cast]
lemma coe_algebraMap (r : R) : (algebraMap R s r : A) = algebraMap R A r := sorry
def val (s : S) : s →ₐ[R] A :=
  { SubsemiringClass.subtype s, SMulMemClass.subtype s with
    toFun := (↑)
    commutes' := fun _ ↦ rfl }

@[target, simp]
theorem coe_val : (val s : s → A) = ((↑) : s → A) :=
  sorry

end SubalgebraClass

namespace Submodule

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
variable (p : Submodule R A)

/-- A submodule containing `1` and closed under multiplication is a subalgebra. -/
@[simps coe toSubsemiring]
def toSubalgebra (p : Submodule R A) (h_one : (1 : A) ∈ p)
    (h_mul : ∀ x y, x ∈ p → y ∈ p → x * y ∈ p) : Subalgebra R A :=
  { p with
    mul_mem' := fun hx hy ↦ h_mul _ _ hx hy
    one_mem' := h_one
    algebraMap_mem' := fun r => by
      rw [Algebra.algebraMap_eq_smul_one]
      exact p.smul_mem _ h_one }

@[target, simp]
theorem mem_toSubalgebra {p : Submodule R A} {h_one h_mul} {x} :
    x ∈ p.toSubalgebra h_one h_mul ↔ x ∈ p := sorry

@[target]
theorem toSubalgebra_mk (s : Submodule R A) (h1 hmul) :
    s.toSubalgebra h1 hmul =
      Subalgebra.mk ⟨⟨⟨s, @hmul⟩, h1⟩, s.add_mem, s.zero_mem⟩
        (by intro r; rw [Algebra.algebraMap_eq_smul_one]; apply s.smul_mem _ h1) :=
  sorry

@[target, simp]
theorem toSubalgebra_toSubmodule (p : Submodule R A) (h_one h_mul) :
    Subalgebra.toSubmodule (p.toSubalgebra h_one h_mul) = p :=
  sorry

@[simp]
theorem _root_.Subalgebra.toSubmodule_toSubalgebra (S : Subalgebra R A) :
    (S.toSubmodule.toSubalgebra S.one_mem fun _ _ => S.mul_mem) = S :=
  SetLike.coe_injective rfl

end Submodule

namespace AlgHom

variable {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}
variable [CommSemiring R]
variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]
variable (φ : A →ₐ[R] B)

/-- Range of an `AlgHom` as a subalgebra. -/
@[simps! coe toSubsemiring]
protected def range (φ : A →ₐ[R] B) : Subalgebra R B :=
  { φ.toRingHom.rangeS with algebraMap_mem' := fun r => ⟨algebraMap R A r, φ.commutes r⟩ }

@[simp]
theorem mem_range (φ : A →ₐ[R] B) {y : B} : y ∈ φ.range ↔ ∃ x, φ x = y :=
  RingHom.mem_rangeS

theorem mem_range_self (φ : A →ₐ[R] B) (x : A) : φ x ∈ φ.range :=
  φ.mem_range.2 ⟨x, rfl⟩

@[target]
theorem range_comp (f : A →ₐ[R] B) (g : B →ₐ[R] C) : (g.comp f).range = f.range.map g :=
  sorry

theorem range_comp_le_range (f : A →ₐ[R] B) (g : B →ₐ[R] C) : (g.comp f).range ≤ g.range :=
  SetLike.coe_mono (Set.range_comp_subset_range f g)

/-- Restrict the codomain of an algebra homomorphism. -/
def codRestrict (f : A →ₐ[R] B) (S : Subalgebra R B) (hf : ∀ x, f x ∈ S) : A →ₐ[R] S :=
  { RingHom.codRestrict (f : A →+* B) S hf with commutes' := fun r => Subtype.eq <| f.commutes r }

@[target, simp]
theorem val_comp_codRestrict (f : A →ₐ[R] B) (S : Subalgebra R B) (hf : ∀ x, f x ∈ S) :
    S.val.comp (f.codRestrict S hf) = f :=
  sorry

@[target, simp]
theorem coe_codRestrict (f : A →ₐ[R] B) (S : Subalgebra R B) (hf : ∀ x, f x ∈ S) (x : A) :
    ↑(f.codRestrict S hf x) = f x :=
  sorry

@[target]
theorem injective_codRestrict (f : A →ₐ[R] B) (S : Subalgebra R B) (hf : ∀ x, f x ∈ S) :
    Function.Injective (f.codRestrict S hf) ↔ Function.Injective f :=
  sorry

@[target]
theorem rangeRestrict_surjective (f : A →ₐ[R] B) : Function.Surjective (f.rangeRestrict) :=
  sorry
instance fintypeRange [Fintype A] [DecidableEq B] (φ : A →ₐ[R] B) : Fintype φ.range :=
  Set.fintypeRange φ

end AlgHom

namespace AlgEquiv

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

/-- Restrict an algebra homomorphism with a left inverse to an algebra isomorphism to its range.

This is a computable alternative to `AlgEquiv.ofInjective`. -/
def ofLeftInverse {g : B → A} {f : A →ₐ[R] B} (h : Function.LeftInverse g f) : A ≃ₐ[R] f.range :=
  { f.rangeRestrict with
    toFun := f.rangeRestrict
    invFun := g ∘ f.range.val
    left_inv := h
    right_inv := fun x =>
      Subtype.ext <|
        let ⟨x', hx'⟩ := f.mem_range.mp x.prop
        show f (g x) = x by rw [← hx', h x'] }

@[simp]
theorem ofLeftInverse_apply {g : B → A} {f : A →ₐ[R] B} (h : Function.LeftInverse g f) (x : A) :
    ↑(ofLeftInverse h x) = f x :=
  rfl

@[target, simp]
theorem ofLeftInverse_symm_apply {g : B → A} {f : A →ₐ[R] B} (h : Function.LeftInverse g f)
    (x : f.range) : (ofLeftInverse h).symm x = g x :=
  sorry

@[target, simp]
theorem ofInjective_apply (f : A →ₐ[R] B) (hf : Function.Injective f) (x : A) :
    ↑(ofInjective f hf x) = f x :=
  sorry
@[simps!]
def subalgebraMap (e : A ≃ₐ[R] B) (S : Subalgebra R A) : S ≃ₐ[R] S.map (e : A →ₐ[R] B) :=
  { e.toRingEquiv.subsemiringMap S.toSubsemiring with
    commutes' := fun r => by
      ext; dsimp only; erw [RingEquiv.subsemiringMap_apply_coe]
      exact e.commutes _ }

end AlgEquiv

namespace Algebra

variable (R : Type u) {A : Type v} {B : Type w}
variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

/-- The minimal subalgebra that includes `s`. -/
@[simps toSubsemiring]
def adjoin (s : Set A) : Subalgebra R A :=
  { Subsemiring.closure (Set.range (algebraMap R A) ∪ s) with
    algebraMap_mem' := fun r => Subsemiring.subset_closure <| Or.inl ⟨r, rfl⟩ }

variable {R}

protected theorem gc : GaloisConnection (adjoin R : Set A → Subalgebra R A) (↑) := fun s S =>
  ⟨fun H => le_trans (le_trans Set.subset_union_right Subsemiring.subset_closure) H,
   fun H => show Subsemiring.closure (Set.range (algebraMap R A) ∪ s) ≤ S.toSubsemiring from
      Subsemiring.closure_le.2 <| Set.union_subset S.range_subset H⟩

/-- Galois insertion between `adjoin` and `coe`. -/
protected def gi : GaloisInsertion (adjoin R : Set A → Subalgebra R A) (↑) where
  choice s hs := (adjoin R s).copy s <| le_antisymm (Algebra.gc.le_u_l s) hs
  gc := Algebra.gc
  le_l_u S := (Algebra.gc (S : Set A) (adjoin R S)).1 <| le_rfl
  choice_eq _ _ := Subalgebra.copy_eq _ _ _

instance : CompleteLattice (Subalgebra R A) where
  __ := GaloisInsertion.liftCompleteLattice Algebra.gi
  bot := (Algebra.ofId R A).range
  bot_le _S := fun _a ⟨_r, hr⟩ => hr ▸ algebraMap_mem _ _

theorem sup_def (S T : Subalgebra R A) : S ⊔ T = adjoin R (S ∪ T : Set A) := rfl

@[target]
theorem sSup_def (S : Set (Subalgebra R A)) : sSup S = adjoin R (⋃₀ (SetLike.coe '' S)) := sorry

@[target, simp]
theorem coe_top : (↑(⊤ : Subalgebra R A) : Set A) = Set.univ := sorry

@[simp]
theorem mem_top {x : A} : x ∈ (⊤ : Subalgebra R A) := Set.mem_univ x

@[target, simp]
theorem top_toSubmodule : Subalgebra.toSubmodule (⊤ : Subalgebra R A) = ⊤ := sorry

@[simp]
theorem top_toSubsemiring : (⊤ : Subalgebra R A).toSubsemiring = ⊤ := rfl

@[simp]
theorem top_toSubring {R A : Type*} [CommRing R] [Ring A] [Algebra R A] :
    (⊤ : Subalgebra R A).toSubring = ⊤ := rfl

@[simp]
theorem toSubmodule_eq_top {S : Subalgebra R A} : Subalgebra.toSubmodule S = ⊤ ↔ S = ⊤ :=
  Subalgebra.toSubmodule.injective.eq_iff' top_toSubmodule

@[target, simp]
theorem toSubsemiring_eq_top {S : Subalgebra R A} : S.toSubsemiring = ⊤ ↔ S = ⊤ :=
  sorry

@[target, simp]
theorem toSubring_eq_top {R A : Type*} [CommRing R] [Ring A] [Algebra R A] {S : Subalgebra R A} :
    S.toSubring = ⊤ ↔ S = ⊤ :=
  sorry

@[target]
theorem mem_sup_left {S T : Subalgebra R A} : ∀ {x : A}, x ∈ S → x ∈ S ⊔ T :=
  sorry

@[target]
theorem mem_sup_right {S T : Subalgebra R A} : ∀ {x : A}, x ∈ T → x ∈ S ⊔ T :=
  sorry

@[target]
theorem mul_mem_sup {S T : Subalgebra R A} {x y : A} (hx : x ∈ S) (hy : y ∈ T) : x * y ∈ S ⊔ T :=
  sorry

theorem map_sup (f : A →ₐ[R] B) (S T : Subalgebra R A) : (S ⊔ T).map f = S.map f ⊔ T.map f :=
  (Subalgebra.gc_map_comap f).l_sup

theorem map_inf (f : A →ₐ[R] B) (hf : Function.Injective f) (S T : Subalgebra R A) :
    (S ⊓ T).map f = S.map f ⊓ T.map f := SetLike.coe_injective (Set.image_inter hf)

@[target, simp, norm_cast]
theorem coe_inf (S T : Subalgebra R A) : (↑(S ⊓ T) : Set A) = (S ∩ T : Set A) := sorry

@[simp]
theorem mem_inf {S T : Subalgebra R A} {x : A} : x ∈ S ⊓ T ↔ x ∈ S ∧ x ∈ T := Iff.rfl

open Subalgebra in
@[target, simp]
theorem inf_toSubmodule (S T : Subalgebra R A) :
    toSubmodule (S ⊓ T) = toSubmodule S ⊓ toSubmodule T := sorry

@[target, simp]
theorem inf_toSubsemiring (S T : Subalgebra R A) :
    (S ⊓ T).toSubsemiring = S.toSubsemiring ⊓ T.toSubsemiring :=
  sorry

@[target, simp]
theorem sup_toSubsemiring (S T : Subalgebra R A) :
    (S ⊔ T).toSubsemiring = S.toSubsemiring ⊔ T.toSubsemiring := by sorry

@[simp, norm_cast]
theorem coe_sInf (S : Set (Subalgebra R A)) : (↑(sInf S) : Set A) = ⋂ s ∈ S, ↑s :=
  sInf_image

theorem mem_sInf {S : Set (Subalgebra R A)} {x : A} : x ∈ sInf S ↔ ∀ p ∈ S, x ∈ p := by
  simp only [← SetLike.mem_coe, coe_sInf, Set.mem_iInter₂]

@[target, simp]
theorem sInf_toSubmodule (S : Set (Subalgebra R A)) :
    Subalgebra.toSubmodule (sInf S) = sInf (Subalgebra.toSubmodule '' S) :=
  sorry

@[target, simp]
theorem sInf_toSubsemiring (S : Set (Subalgebra R A)) :
    (sInf S).toSubsemiring = sInf (Subalgebra.toSubsemiring '' S) :=
  sorry

open Subalgebra in
@[target, simp]
theorem sSup_toSubsemiring (S : Set (Subalgebra R A)) (hS : S.Nonempty) :
    (sSup S).toSubsemiring = sSup (toSubsemiring '' S) := by sorry

@[simp, norm_cast]
theorem coe_iInf {ι : Sort*} {S : ι → Subalgebra R A} : (↑(⨅ i, S i) : Set A) = ⋂ i, S i := by
  simp [iInf]

@[target]
theorem mem_iInf {ι : Sort*} {S : ι → Subalgebra R A} {x : A} : (x ∈ ⨅ i, S i) ↔ ∀ i, x ∈ S i := by sorry

@[target]
theorem map_iInf {ι : Sort*} [Nonempty ι] (f : A →ₐ[R] B) (hf : Function.Injective f)
    (s : ι → Subalgebra R A) : (iInf s).map f = ⨅ (i : ι), (s i).map f := by sorry

open Subalgebra in
@[target, simp]
theorem iInf_toSubmodule {ι : Sort*} (S : ι → Subalgebra R A) :
    toSubmodule (⨅ i, S i) = ⨅ i, toSubmodule (S i) :=
  sorry

@[target, simp]
theorem iInf_toSubsemiring {ι : Sort*} (S : ι → Subalgebra R A) :
    (iInf S).toSubsemiring = ⨅ i, (S i).toSubsemiring := by sorry

@[simp]
theorem iSup_toSubsemiring {ι : Sort*} [Nonempty ι] (S : ι → Subalgebra R A) :
    (iSup S).toSubsemiring = ⨆ i, (S i).toSubsemiring := by
  simp only [iSup, Set.range_nonempty, sSup_toSubsemiring, ← Set.range_comp, Function.comp_def]

@[target]
lemma mem_iSup_of_mem {ι : Sort*} {S : ι → Subalgebra R A} (i : ι) {x : A} (hx : x ∈ S i) :
    x ∈ iSup S :=
  sorry

@[elab_as_elim]
lemma iSup_induction {ι : Sort*} (S : ι → Subalgebra R A) {motive : A → Prop}
    {x : A} (mem : x ∈ ⨆ i, S i)
    (basic : ∀ i, ∀ a ∈ S i, motive a)
    (zero : motive 0) (one : motive 1)
    (add : ∀ a b, motive a → motive b → motive (a + b))
    (mul : ∀ a b, motive a → motive b → motive (a * b))
    (algebraMap : ∀ r, motive (algebraMap R A r)) : motive x := by
  let T : Subalgebra R A :=
  { carrier := {x | motive x}
    mul_mem' {a b} := mul a b
    one_mem' := one
    add_mem' {a b} := add a b
    zero_mem' := zero
    algebraMap_mem' := algebraMap }
  suffices iSup S ≤ T from this mem
  rwa [iSup_le_iff]

/-- A dependent version of `Subalgebra.iSup_induction`. -/
@[target, elab_as_elim]
theorem iSup_induction' {ι : Sort*} (S : ι → Subalgebra R A) {motive : ∀ x, (x ∈ ⨆ i, S i) → Prop}
    {x : A} (mem : x ∈ ⨆ i, S i)
    (basic : ∀ (i) (x) (hx : x ∈ S i), motive x (mem_iSup_of_mem i hx))
    (zero : motive 0 (zero_mem _)) (one : motive 1 (one_mem _))
    (add : ∀ x y hx hy, motive x hx → motive y hy → motive (x + y) (add_mem ‹_› ‹_›))
    (mul : ∀ x y hx hy, motive x hx → motive y hy → motive (x * y) (mul_mem ‹_› ‹_›))
    (algebraMap : ∀ r, motive (algebraMap R A r) (Subalgebra.algebraMap_mem _ ‹_›)) :
    motive x mem := by sorry

instance : Inhabited (Subalgebra R A) := ⟨⊥⟩

@[target]
theorem mem_bot {x : A} : x ∈ (⊥ : Subalgebra R A) ↔ x ∈ Set.range (algebraMap R A) := sorry
@[target]
theorem toSubmodule_bot : Subalgebra.toSubmodule (⊥ : Subalgebra R A) = 1 :=
  sorry

@[target, simp]
theorem coe_bot : ((⊥ : Subalgebra R A) : Set A) = Set.range (algebraMap R A) := sorry

@[target]
theorem eq_top_iff {S : Subalgebra R A} : S = ⊤ ↔ ∀ x : A, x ∈ S :=
  sorry

theorem _root_.AlgHom.range_eq_top (f : A →ₐ[R] B) :
    f.range = (⊤ : Subalgebra R B) ↔ Function.Surjective f :=
  Algebra.eq_top_iff

@[deprecated (since := "2024-11-11")] alias range_top_iff_surjective := AlgHom.range_eq_top

@[simp]
theorem range_ofId : (Algebra.ofId R A).range = ⊥ := rfl

@[simp]
theorem range_id : (AlgHom.id R A).range = ⊤ :=
  SetLike.coe_injective Set.range_id

@[simp]
theorem map_top (f : A →ₐ[R] B) : (⊤ : Subalgebra R A).map f = f.range :=
  SetLike.coe_injective Set.image_univ

@[simp]
theorem map_bot (f : A →ₐ[R] B) : (⊥ : Subalgebra R A).map f = ⊥ :=
  Subalgebra.toSubmodule_injective <| by
    simpa only [Subalgebra.map_toSubmodule, toSubmodule_bot] using Submodule.map_one _

@[target, simp]
theorem comap_top (f : A →ₐ[R] B) : (⊤ : Subalgebra R B).comap f = ⊤ :=
  sorry
def toTop : A →ₐ[R] (⊤ : Subalgebra R A) :=
  (AlgHom.id R A).codRestrict ⊤ fun _ => mem_top

theorem surjective_algebraMap_iff :
    Function.Surjective (algebraMap R A) ↔ (⊤ : Subalgebra R A) = ⊥ :=
  ⟨fun h =>
    eq_bot_iff.2 fun y _ =>
      let ⟨_x, hx⟩ := h y
      hx ▸ Subalgebra.algebraMap_mem _ _,
    fun h y => Algebra.mem_bot.1 <| eq_bot_iff.1 h (Algebra.mem_top : y ∈ _)⟩

@[target]
theorem bijective_algebraMap_iff {R A : Type*} [Field R] [Semiring A] [Nontrivial A]
    [Algebra R A] : Function.Bijective (algebraMap R A) ↔ (⊤ : Subalgebra R A) = ⊥ :=
  sorry
@[simps! symm_apply]
noncomputable def botEquiv (F R : Type*) [Field F] [Semiring R] [Nontrivial R] [Algebra F R] :
    (⊥ : Subalgebra F R) ≃ₐ[F] F :=
  botEquivOfInjective (RingHom.injective _)

end Algebra

namespace Subalgebra

open Algebra

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
variable (S : Subalgebra R A)

/-- The top subalgebra is isomorphic to the algebra.

This is the algebra version of `Submodule.topEquiv`. -/
@[simps!]
def topEquiv : (⊤ : Subalgebra R A) ≃ₐ[R] A :=
  AlgEquiv.ofAlgHom (Subalgebra.val ⊤) toTop rfl rfl

instance subsingleton_of_subsingleton [Subsingleton A] : Subsingleton (Subalgebra R A) :=
  ⟨fun B C => ext fun x => by simp only [Subsingleton.elim x 0, zero_mem B, zero_mem C]⟩

instance _root_.AlgHom.subsingleton [Subsingleton (Subalgebra R A)] : Subsingleton (A →ₐ[R] B) :=
  ⟨fun f g =>
    AlgHom.ext fun a =>
      have : a ∈ (⊥ : Subalgebra R A) := Subsingleton.elim (⊤ : Subalgebra R A) ⊥ ▸ mem_top
      let ⟨_x, hx⟩ := Set.mem_range.mp (mem_bot.mp this)
      hx ▸ (f.commutes _).trans (g.commutes _).symm⟩

instance _root_.AlgEquiv.subsingleton_left [Subsingleton (Subalgebra R A)] :
    Subsingleton (A ≃ₐ[R] B) :=
  ⟨fun f g => AlgEquiv.ext fun x => AlgHom.ext_iff.mp (Subsingleton.elim f.toAlgHom g.toAlgHom) x⟩

instance _root_.AlgEquiv.subsingleton_right [Subsingleton (Subalgebra R B)] :
    Subsingleton (A ≃ₐ[R] B) :=
  ⟨fun f g => by rw [← f.symm_symm, Subsingleton.elim f.symm g.symm, g.symm_symm]⟩

@[target]
theorem range_val : S.val.range = S :=
  sorry

instance : Unique (Subalgebra R R) :=
  { inferInstanceAs (Inhabited (Subalgebra R R)) with
    uniq := by
      intro S
      refine le_antisymm ?_ bot_le
      intro _ _
      simp only [Set.mem_range, mem_bot, id.map_eq_self, exists_apply_eq_apply, default] }

/-- The map `S → T` when `S` is a subalgebra contained in the subalgebra `T`.

This is the subalgebra version of `Submodule.inclusion`, or `Subring.inclusion` -/
def inclusion {S T : Subalgebra R A} (h : S ≤ T) : S →ₐ[R] T where
  toFun := Set.inclusion h
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  commutes' _ := rfl

@[target]
theorem inclusion_injective {S T : Subalgebra R A} (h : S ≤ T) : Function.Injective (inclusion h) :=
  sorry

@[simp]
theorem inclusion_self {S : Subalgebra R A} : inclusion (le_refl S) = AlgHom.id R S :=
  AlgHom.ext fun _x => Subtype.ext rfl

@[simp]
theorem inclusion_mk {S T : Subalgebra R A} (h : S ≤ T) (x : A) (hx : x ∈ S) :
    inclusion h ⟨x, hx⟩ = ⟨x, h hx⟩ :=
  rfl

@[target]
theorem inclusion_right {S T : Subalgebra R A} (h : S ≤ T) (x : T) (m : (x : A) ∈ S) :
    inclusion h ⟨x, m⟩ = x :=
  sorry

@[simp]
theorem inclusion_inclusion {S T U : Subalgebra R A} (hst : S ≤ T) (htu : T ≤ U) (x : S) :
    inclusion htu (inclusion hst x) = inclusion (le_trans hst htu) x :=
  Subtype.ext rfl

@[simp]
theorem coe_inclusion {S T : Subalgebra R A} (h : S ≤ T) (s : S) : (inclusion h s : A) = s :=
  rfl

/-- Two subalgebras that are equal are also equivalent as algebras.

This is the `Subalgebra` version of `LinearEquiv.ofEq` and `Equiv.Set.ofEq`. -/
@[simps apply]
def equivOfEq (S T : Subalgebra R A) (h : S = T) : S ≃ₐ[R] T where
  __ := LinearEquiv.ofEq _ _ (congr_arg toSubmodule h)
  toFun x := ⟨x, h ▸ x.2⟩
  invFun x := ⟨x, h.symm ▸ x.2⟩
  map_mul' _ _ := rfl
  commutes' _ := rfl

@[target, simp]
theorem equivOfEq_symm (S T : Subalgebra R A) (h : S = T) :
    (equivOfEq S T h).symm = equivOfEq T S h.symm := sorry

@[simp]
theorem equivOfEq_rfl (S : Subalgebra R A) : equivOfEq S S rfl = AlgEquiv.refl := by ext; rfl

@[target, simp]
theorem equivOfEq_trans (S T U : Subalgebra R A) (hST : S = T) (hTU : T = U) :
    (equivOfEq S T hST).trans (equivOfEq T U hTU) = equivOfEq S U (hST.trans hTU) := sorry

section equivMapOfInjective

variable (f : A →ₐ[R] B)

@[target]
theorem range_comp_val : (f.comp S.val).range = S.map f := by sorry
def _root_.AlgHom.subalgebraMap : S →ₐ[R] S.map f :=
  (f.comp S.val).codRestrict _ fun x ↦ ⟨_, x.2, rfl⟩

variable {S} in
@[simp]
theorem _root_.AlgHom.subalgebraMap_coe_apply (x : S) : f.subalgebraMap S x = f x := rfl

theorem _root_.AlgHom.subalgebraMap_surjective : Function.Surjective (f.subalgebraMap S) :=
  f.toAddMonoidHom.addSubmonoidMap_surjective S.toAddSubmonoid

variable (hf : Function.Injective f)

/-- A subalgebra is isomorphic to its image under an injective `AlgHom` -/
noncomputable def equivMapOfInjective : S ≃ₐ[R] S.map f :=
  (AlgEquiv.ofInjective (f.comp S.val) (hf.comp Subtype.val_injective)).trans
    (equivOfEq _ _ (range_comp_val S f))

@[target, simp]
theorem coe_equivMapOfInjective_apply (x : S) : ↑(equivMapOfInjective S f hf x) = f x := sorry

end equivMapOfInjective

/-! ## Actions by `Subalgebra`s

These are just copies of the definitions about `Subsemiring` starting from
`Subring.mulAction`.
-/


section Actions

variable {α β : Type*}

/-- The action by a subalgebra is the action by the underlying algebra. -/
instance [SMul A α] (S : Subalgebra R A) : SMul S α :=
  inferInstanceAs (SMul S.toSubsemiring α)

@[target]
theorem smul_def [SMul A α] {S : Subalgebra R A} (g : S) (m : α) : g • m = (g : A) • m := sorry

instance smulCommClass_left [SMul A β] [SMul α β] [SMulCommClass A α β] (S : Subalgebra R A) :
    SMulCommClass S α β :=
  S.toSubsemiring.smulCommClass_left

instance smulCommClass_right [SMul α β] [SMul A β] [SMulCommClass α A β] (S : Subalgebra R A) :
    SMulCommClass α S β :=
  S.toSubsemiring.smulCommClass_right

/-- Note that this provides `IsScalarTower S R R` which is needed by `smul_mul_assoc`. -/
instance isScalarTower_left [SMul α β] [SMul A α] [SMul A β] [IsScalarTower A α β]
    (S : Subalgebra R A) : IsScalarTower S α β :=
  inferInstanceAs (IsScalarTower S.toSubsemiring α β)

instance isScalarTower_mid {R S T : Type*} [CommSemiring R] [Semiring S] [AddCommMonoid T]
    [Algebra R S] [Module R T] [Module S T] [IsScalarTower R S T] (S' : Subalgebra R S) :
    IsScalarTower R S' T :=
  ⟨fun _x y _z => smul_assoc _ (y : S) _⟩

instance [SMul A α] [FaithfulSMul A α] (S : Subalgebra R A) : FaithfulSMul S α :=
  inferInstanceAs (FaithfulSMul S.toSubsemiring α)

/-- The action by a subalgebra is the action by the underlying algebra. -/
instance [MulAction A α] (S : Subalgebra R A) : MulAction S α :=
  inferInstanceAs (MulAction S.toSubsemiring α)

/-- The action by a subalgebra is the action by the underlying algebra. -/
instance [AddMonoid α] [DistribMulAction A α] (S : Subalgebra R A) : DistribMulAction S α :=
  inferInstanceAs (DistribMulAction S.toSubsemiring α)

/-- The action by a subalgebra is the action by the underlying algebra. -/
instance [Zero α] [SMulWithZero A α] (S : Subalgebra R A) : SMulWithZero S α :=
  inferInstanceAs (SMulWithZero S.toSubsemiring α)

/-- The action by a subalgebra is the action by the underlying algebra. -/
instance [Zero α] [MulActionWithZero A α] (S : Subalgebra R A) : MulActionWithZero S α :=
  inferInstanceAs (MulActionWithZero S.toSubsemiring α)

/-- The action by a subalgebra is the action by the underlying algebra. -/
instance moduleLeft [AddCommMonoid α] [Module A α] (S : Subalgebra R A) : Module S α :=
  inferInstanceAs (Module S.toSubsemiring α)

/-- The action by a subalgebra is the action by the underlying algebra. -/
instance toAlgebra {R A : Type*} [CommSemiring R] [CommSemiring A] [Semiring α] [Algebra R A]
    [Algebra A α] (S : Subalgebra R A) : Algebra S α :=
  Algebra.ofSubsemiring S.toSubsemiring

@[target]
theorem algebraMap_eq {R A : Type*} [CommSemiring R] [CommSemiring A] [Semiring α] [Algebra R A]
    [Algebra A α] (S : Subalgebra R A) : algebraMap S α = (algebraMap A α).comp S.val :=
  sorry

@[simp]
theorem rangeS_algebraMap {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    (S : Subalgebra R A) : (algebraMap S A).rangeS = S.toSubsemiring := by
  rw [algebraMap_eq, Algebra.id.map_eq_id, RingHom.id_comp, ← toSubsemiring_subtype,
    Subsemiring.rangeS_subtype]

@[simp]
theorem range_algebraMap {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (S : Subalgebra R A) : (algebraMap S A).range = S.toSubring := by
  rw [algebraMap_eq, Algebra.id.map_eq_id, RingHom.id_comp, ← toSubring_subtype,
    Subring.range_subtype]

instance noZeroSMulDivisors_top [NoZeroDivisors A] (S : Subalgebra R A) : NoZeroSMulDivisors S A :=
  ⟨fun {c} x h =>
    have : (c : A) = 0 ∨ x = 0 := eq_zero_or_eq_zero_of_mul_eq_zero h
    this.imp_left (@Subtype.ext_iff _ _ c 0).mpr⟩

end Actions

section Center

theorem _root_.Set.algebraMap_mem_center (r : R) : algebraMap R A r ∈ Set.center A := by
  simp only [Semigroup.mem_center_iff, commutes, forall_const]

variable (R A)

/-- The center of an algebra is the set of elements which commute with every element. They form a
subalgebra. -/
@[simps! coe toSubsemiring]
def center : Subalgebra R A :=
  { Subsemiring.center A with algebraMap_mem' := Set.algebraMap_mem_center }

@[simp]
theorem center_toSubring (R A : Type*) [CommRing R] [Ring A] [Algebra R A] :
    (center R A).toSubring = Subring.center A :=
  rfl

@[simp]
theorem center_eq_top (A : Type*) [CommSemiring A] [Algebra R A] : center R A = ⊤ :=
  SetLike.coe_injective (Set.center_eq_univ A)

variable {R A}

instance : CommSemiring (center R A) :=
  inferInstanceAs (CommSemiring (Subsemiring.center A))

instance {A : Type*} [Ring A] [Algebra R A] : CommRing (center R A) :=
  inferInstanceAs (CommRing (Subring.center A))

@[target]
theorem mem_center_iff {a : A} : a ∈ center R A ↔ ∀ b : A, b * a = a * b :=
  sorry

end Center

section Centralizer

@[target, simp]
theorem _root_.Set.algebraMap_mem_centralizer {s : Set A} (r : R) :
    algebraMap R A r ∈ s.centralizer :=
  sorry

variable (R)

/-- The centralizer of a set as a subalgebra. -/
def centralizer (s : Set A) : Subalgebra R A :=
  { Subsemiring.centralizer s with algebraMap_mem' := Set.algebraMap_mem_centralizer }

@[simp, norm_cast]
theorem coe_centralizer (s : Set A) : (centralizer R s : Set A) = s.centralizer :=
  rfl

@[target]
theorem mem_centralizer_iff {s : Set A} {z : A} : z ∈ centralizer R s ↔ ∀ g ∈ s, g * z = z * g :=
  sorry

theorem center_le_centralizer (s) : center R A ≤ centralizer R s :=
  s.center_subset_centralizer

@[target]
theorem centralizer_le (s t : Set A) (h : s ⊆ t) : centralizer R t ≤ centralizer R s :=
  sorry

@[target, simp]
theorem centralizer_eq_top_iff_subset {s : Set A} : centralizer R s = ⊤ ↔ s ⊆ center R A :=
  sorry

@[target, simp]
theorem centralizer_univ : centralizer R Set.univ = center R A :=
  sorry

lemma le_centralizer_centralizer {s : Subalgebra R A} :
    s ≤ centralizer R (centralizer R (s : Set A)) :=
  Set.subset_centralizer_centralizer

@[simp]
lemma centralizer_centralizer_centralizer {s : Set A} :
    centralizer R s.centralizer.centralizer = centralizer R s := by
  apply SetLike.coe_injective
  simp only [coe_centralizer, Set.centralizer_centralizer_centralizer]

end Centralizer

end Subalgebra

section Nat

variable {R : Type*} [Semiring R]

/-- A subsemiring is an `ℕ`-subalgebra. -/
@[simps toSubsemiring]
def subalgebraOfSubsemiring (S : Subsemiring R) : Subalgebra ℕ R :=
  { S with algebraMap_mem' := fun i => natCast_mem S i }

@[simp]
theorem mem_subalgebraOfSubsemiring {x : R} {S : Subsemiring R} :
    x ∈ subalgebraOfSubsemiring S ↔ x ∈ S :=
  Iff.rfl

end Nat

section Int

variable {R : Type*} [Ring R]

/-- A subring is a `ℤ`-subalgebra. -/
@[simps toSubsemiring]
def subalgebraOfSubring (S : Subring R) : Subalgebra ℤ R :=
  { S with
    algebraMap_mem' := fun i =>
      Int.induction_on i (by simpa using S.zero_mem)
        (fun i ih => by simpa using S.add_mem ih S.one_mem) fun i ih =>
        show ((-i - 1 : ℤ) : R) ∈ S by
          rw [Int.cast_sub, Int.cast_one]
          exact S.sub_mem ih S.one_mem }

variable {S : Type*} [Semiring S]

@[simp]
theorem mem_subalgebraOfSubring {x : R} {S : Subring R} : x ∈ subalgebraOfSubring S ↔ x ∈ S :=
  Iff.rfl

end Int

section Equalizer

namespace AlgHom

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
variable {F : Type*}

/-- The equalizer of two R-algebra homomorphisms -/
@[simps coe toSubsemiring]
def equalizer (ϕ ψ : F) [FunLike F A B] [AlgHomClass F R A B] : Subalgebra R A where
  carrier := { a | ϕ a = ψ a }
  zero_mem' := by simp only [Set.mem_setOf_eq, map_zero]
  one_mem' := by simp only [Set.mem_setOf_eq, map_one]
  add_mem' {x y} (hx : ϕ x = ψ x) (hy : ϕ y = ψ y) := by
    rw [Set.mem_setOf_eq, map_add, map_add, hx, hy]
  mul_mem' {x y} (hx : ϕ x = ψ x) (hy : ϕ y = ψ y) := by
    rw [Set.mem_setOf_eq, map_mul, map_mul, hx, hy]
  algebraMap_mem' x := by
    simp only [Set.mem_setOf_eq, AlgHomClass.commutes]

variable [FunLike F A B] [AlgHomClass F R A B]

@[target, simp]
theorem mem_equalizer (φ ψ : F) (x : A) : x ∈ equalizer φ ψ ↔ φ x = ψ x :=
  sorry

@[target]
theorem equalizer_toSubmodule {φ ψ : F} :
    Subalgebra.toSubmodule (equalizer φ ψ) = LinearMap.eqLocus φ ψ := sorry

@[simp]
theorem equalizer_eq_top {φ ψ : F} : equalizer φ ψ = ⊤ ↔ φ = ψ := by
  simp [SetLike.ext_iff, DFunLike.ext_iff]

@[target, simp]
theorem equalizer_same (φ : F) : equalizer φ φ = ⊤ := sorry

theorem le_equalizer {φ ψ : F} {S : Subalgebra R A} : S ≤ equalizer φ ψ ↔ Set.EqOn φ ψ S := Iff.rfl

theorem eqOn_sup {φ ψ : F} {S T : Subalgebra R A} (hS : Set.EqOn φ ψ S) (hT : Set.EqOn φ ψ T) :
    Set.EqOn φ ψ ↑(S ⊔ T) := by
  rw [← le_equalizer] at hS hT ⊢
  exact sup_le hS hT

@[target]
theorem ext_on_codisjoint {φ ψ : F} {S T : Subalgebra R A} (hST : Codisjoint S T)
    (hS : Set.EqOn φ ψ S) (hT : Set.EqOn φ ψ T) : φ = ψ :=
  sorry

end AlgHom

end Equalizer

section MapComap

namespace Subalgebra

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

@[target]
theorem map_comap_eq (f : A →ₐ[R] B) (S : Subalgebra R B) : (S.comap f).map f = S ⊓ f.range :=
  sorry

theorem map_comap_eq_self
    {f : A →ₐ[R] B} {S : Subalgebra R B} (h : S ≤ f.range) : (S.comap f).map f = S := by
  simpa only [inf_of_le_left h] using map_comap_eq f S

theorem map_comap_eq_self_of_surjective
    {f : A →ₐ[R] B} (hf : Function.Surjective f) (S : Subalgebra R B) : (S.comap f).map f = S :=
  map_comap_eq_self <| by simp [(AlgHom.range_eq_top f).2 hf]

theorem comap_map_eq_self_of_injective
    {f : A →ₐ[R] B} (hf : Function.Injective f) (S : Subalgebra R A) : (S.map f).comap f = S :=
  SetLike.coe_injective (Set.preimage_image_eq _ hf)

end Subalgebra

end MapComap

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

/-- Turn a non-unital subalgebra containing `1` into a subalgebra. -/
def NonUnitalSubalgebra.toSubalgebra (S : NonUnitalSubalgebra R A) (h1 : (1 : A) ∈ S) :
    Subalgebra R A :=
  { S with
    one_mem' := h1
    algebraMap_mem' := fun r =>
      (Algebra.algebraMap_eq_smul_one (R := R) (A := A) r).symm ▸ SMulMemClass.smul_mem r h1 }

lemma Subalgebra.toNonUnitalSubalgebra_toSubalgebra (S : Subalgebra R A) :
    S.toNonUnitalSubalgebra.toSubalgebra S.one_mem = S := by cases S; rfl

@[target]
lemma NonUnitalSubalgebra.toSubalgebra_toNonUnitalSubalgebra (S : NonUnitalSubalgebra R A)
    (h1 : (1 : A) ∈ S) : (NonUnitalSubalgebra.toSubalgebra S h1).toNonUnitalSubalgebra = S := by sorry