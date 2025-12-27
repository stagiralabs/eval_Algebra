import VerifiedAgora.tagger
/-
Copyright (c) 2024 María Inés de Frutos Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos Fernández, Xavier Généreux
-/
import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
# Skew Monoid Algebras

Given a monoid `G` and a ring `k`, the skew monoid algebra of `G` over `k` is the set of finitely
supported functions `f : G → k` for which addition is defined pointwise and multiplication of two
elements `f` and `g` is given by the finitely supported function whose value at `a` is the sum of
`f x * (x • g y)` over all pairs `x, y` such that `x * y = a`, where `•` denotes the action of `G`
on `k`. When this action is trivial, this product is the usual convolution product.

In fact the construction of the skew monoid algebra makes sense when  `G` is not even a monoid, but
merely a magma, i.e., when `G` carries a multiplication which is not required to satisfy any
conditions at all, and `k` is a not-necessarily-associative semiring. In this case the construction
yields a not-necessarily-unital, not-necessarily-associative algebra.

## Main Definitions
- `SkewMonoidAlgebra k G`: the skew monoid algebra of `G` over `k` is the type of finite formal
`k`-linear combinations of terms of `G`, endowed with a skewed convolution product.

## TODO
- Define the skew convolution product.
- Provide algebraic instances.
-/


noncomputable section

/-- The skew monoid algebra of `G` over `k` is the type of finite formal `k`-linear
combinations of terms of `G`, endowed with a skewed convolution product. -/
structure SkewMonoidAlgebra (k : Type*) (G : Type*) [Zero k] where
  /-- The natural map from `G →₀ k` to `SkewMonoidAlgebra k G`. -/
  ofFinsupp ::
  /-- The natural map from `SkewMonoidAlgebra k G` to `G →₀ k`. -/
  toFinsupp : G →₀ k

open Function
namespace SkewMonoidAlgebra

variable {k G : Type*}

section AddCommMonoid

variable [AddCommMonoid k]

@[simp]
theorem eta (f : SkewMonoidAlgebra k G) : ofFinsupp f.toFinsupp = f := rfl

@[irreducible]
private def add :
    SkewMonoidAlgebra k G → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | ⟨a⟩, ⟨b⟩ => ⟨a + b⟩

private def smul {S : Type*} [SMulZeroClass S k] :
    S → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | s, ⟨b⟩ => ⟨s • b⟩

instance instZero : Zero (SkewMonoidAlgebra k G) := ⟨⟨0⟩⟩

instance instAdd : Add (SkewMonoidAlgebra k G) := ⟨add⟩

instance instSMulZeroClass {S : Type*} [SMulZeroClass S k] :
    SMulZeroClass S (SkewMonoidAlgebra k G) where
  smul s f := smul s f
  smul_zero a := by simp only [smul]; exact congr_arg ofFinsupp (smul_zero a)

@[simp]
theorem ofFinsupp_zero : (⟨0⟩ : SkewMonoidAlgebra k G) = 0 := rfl

@[target, simp]
theorem ofFinsupp_add {a b} : (⟨a + b⟩ : SkewMonoidAlgebra k G) = ⟨a⟩ + ⟨b⟩ :=
  sorry

@[target, simp]
theorem ofFinsupp_smul {S : Type*} [SMulZeroClass S k] (a : S) (b : G →₀ k) :
    (⟨a • b⟩ : SkewMonoidAlgebra k G) = (a • ⟨b⟩ : SkewMonoidAlgebra k G) :=
  sorry

@[target, simp]
theorem toFinsupp_zero : (0 : SkewMonoidAlgebra k G).toFinsupp = 0 := sorry

@[simp]
theorem toFinsupp_add (a b : SkewMonoidAlgebra k G) :
    (a + b).toFinsupp = a.toFinsupp + b.toFinsupp := by
  rw [← ofFinsupp_add]

@[target, simp]
theorem toFinsupp_smul {S : Type*} [SMulZeroClass S k] (a : S) (b : SkewMonoidAlgebra k G) :
    (a • b).toFinsupp = a • b.toFinsupp := by sorry

theorem _root_.IsSMulRegular.skewMonoidAlgebra {S : Type*} [Monoid S] [DistribMulAction S k] {a : S}
    (ha : IsSMulRegular k a) : IsSMulRegular (SkewMonoidAlgebra k G) a
  | ⟨_⟩, ⟨_⟩, h => by
    simp only [← ofFinsupp_smul] at h
    exact congr_arg _ <| ha.finsupp (ofFinsupp.inj h)

theorem toFinsupp_injective :
    Function.Injective (toFinsupp : SkewMonoidAlgebra k G → Finsupp _ _) :=
  fun ⟨_⟩ _ ↦ congr_arg _

@[simp]
theorem toFinsupp_inj {a b : SkewMonoidAlgebra k G} : a.toFinsupp = b.toFinsupp ↔ a = b :=
  toFinsupp_injective.eq_iff

theorem ofFinsupp_injective :
    Function.Injective (ofFinsupp : Finsupp _ _ → SkewMonoidAlgebra k G) :=
  fun _ _ ↦ congr_arg toFinsupp

/-- A more convenient spelling of `SkewMonoidAlgebra.ofFinsupp.injEq` in terms of `Iff`. -/
@[target]
theorem ofFinsupp_inj {a b} : (⟨a⟩ : SkewMonoidAlgebra k G) = ⟨b⟩ ↔ a = b :=
  sorry

@[target, simp]
theorem toFinsupp_eq_zero {a : SkewMonoidAlgebra k G} : a.toFinsupp = 0 ↔ a = 0 := by sorry

@[target, simp]
theorem ofFinsupp_eq_zero {a} : (⟨a⟩ : SkewMonoidAlgebra k G) = 0 ↔ a = 0 := by sorry

instance instInhabited : Inhabited (SkewMonoidAlgebra k G) := ⟨0⟩

instance instNontrivial [Nontrivial k] [Nonempty G] :
    Nontrivial (SkewMonoidAlgebra k G) := Function.Injective.nontrivial ofFinsupp_injective

instance instAddCommMonoid : AddCommMonoid (SkewMonoidAlgebra k G) where
  __ := toFinsupp_injective.addCommMonoid _ toFinsupp_zero toFinsupp_add
    (fun _ _ ↦ toFinsupp_smul _ _)
  toAdd  := SkewMonoidAlgebra.instAdd
  toZero := SkewMonoidAlgebra.instZero
  nsmul  := (· • ·)

section Support

/-- For `f : SkewMonoidAlgebra k G`, `f.support` is the set of all `a ∈ G` such that
`f a ≠ 0`. -/
def support : SkewMonoidAlgebra k G → Finset G
  | ⟨p⟩ => p.support

@[simp]
theorem support_ofFinsupp (p) : support (⟨p⟩ : SkewMonoidAlgebra k G) = p.support := by
  rw [support]

theorem support_toFinsupp (p : SkewMonoidAlgebra k G) : p.toFinsupp.support = p.support := by
  rw [support]

@[target, simp]
theorem support_zero : (0 : SkewMonoidAlgebra k G).support = ∅ := sorry

@[target, simp]
theorem support_eq_empty {p} : p.support = ∅ ↔ (p : SkewMonoidAlgebra k G) = 0 := by sorry

end Support

section Coeff

/-- `coeff f a` (often denoted `f.coeff a`) is the coefficient of `a` in `f`. -/
def coeff : SkewMonoidAlgebra k G → G → k
  | ⟨p⟩ => p

@[simp]
theorem coeff_ofFinsupp (p) : coeff (⟨p⟩ : SkewMonoidAlgebra k G) = p := rfl

@[target]
theorem coeff_injective : Injective (coeff : SkewMonoidAlgebra k G → G → k) := by sorry

@[simp]
theorem coeff_inj (p q : SkewMonoidAlgebra k G) : p.coeff = q.coeff ↔ p = q :=
  coeff_injective.eq_iff

@[target, simp]
theorem toFinsupp_apply (f : SkewMonoidAlgebra k G) (g) : f.toFinsupp g = f.coeff g := sorry

@[simp]
theorem coeff_zero (g : G) : coeff (0 : SkewMonoidAlgebra k G) g = 0 := rfl

@[simp]
theorem mem_support_iff {f : SkewMonoidAlgebra k G} {a : G} : a ∈ f.support ↔ f.coeff a ≠ 0 := by
  rcases f with ⟨⟩
  simp only [coeff, support_ofFinsupp, Finsupp.mem_support_iff, ne_eq, implies_true]

theorem not_mem_support_iff {f : SkewMonoidAlgebra k G} {a : G} :
    a ∉ f.support ↔ f.coeff a = 0 := by
  simp only [mem_support_iff, ne_eq, not_not]

@[target]
theorem ext_iff {p q : SkewMonoidAlgebra k G} : p = q ↔ ∀ n, coeff p n = coeff q n := by sorry

@[ext]
theorem ext {p q : SkewMonoidAlgebra k G} : (∀ a, coeff p a = coeff q a) → p = q := ext_iff.2

@[target, simp]
theorem coeff_add (p q : SkewMonoidAlgebra k G) (a : G) :
    coeff (p + q) a = coeff p a + coeff q a := by sorry

@[target, simp]
theorem coeff_smul {S} [SMulZeroClass S k] (r : S) (p : SkewMonoidAlgebra k G) (a : G) :
    coeff (r • p) a = r • coeff p a := by sorry

end Coeff

section Single

/-- `single a b` is the finitely supported function with value `b` at `a` and zero otherwise. -/
def single (a : G) (b : k) : SkewMonoidAlgebra k G := ⟨Finsupp.single a b⟩

@[target, simp]
theorem toFinsupp_single (a : G) (b : k) : (single a b).toFinsupp = Finsupp.single a b := sorry

@[target, simp]
theorem ofFinsupp_single (a : G) (b : k) : ⟨Finsupp.single a b⟩ = single a b := sorry

theorem coeff_single (a : G) (b : k) [DecidableEq G] :
    coeff (single a b) = Pi.single a b := by
  simp [coeff, Finsupp.single_eq_pi_single]

@[target]
theorem coeff_single_apply {a a' : G} {b : k} [Decidable (a = a')] :
    coeff (single a b) a' = if a = a' then b else 0 := by sorry

theorem single_zero_right (a : G) : single a (0 : k) = 0 := by
  ext a'; classical
  by_cases h : a = a' <;> (rw [coeff_single_apply]; simp only [h, ↓reduceIte, coeff_zero])

@[target, simp]
theorem single_add (a : G) (b₁ b₂ : k) : single a (b₁ + b₂) = single a b₁ + single a b₂ := by sorry

@[target]
theorem single_zero (a : G) : (single a 0 : SkewMonoidAlgebra k G) = 0 := by sorry

theorem single_eq_zero {a : G} {b : k} : single a b = 0 ↔ b = 0 := by
  rw [ofFinsupp_eq_zero, single, Finsupp.single_eq_zero]

/-- Group isomorphism between `SkewMonoidAlgebra k G` and `G →₀ k`. This is an
implementation detail, but it can be useful to transfer results from `Finsupp`
to `SkewMonoidAlgebra`. -/
@[simps apply symm_apply]
def toFinsuppAddEquiv : SkewMonoidAlgebra k G ≃+ (G →₀ k) where
  toFun        := toFinsupp
  invFun       := ofFinsupp
  left_inv     := fun ⟨_p⟩ ↦ rfl
  right_inv _p := rfl
  map_add'     := toFinsupp_add

theorem smul_single {S} [SMulZeroClass S k] (s : S) (a : G) (b : k) :
    s • single a b = single a (s • b) :=
  toFinsupp_injective <| by simp;

@[target]
theorem single_injective (a : G) : Function.Injective (single a : k → SkewMonoidAlgebra k G) :=
  sorry

@[target]
theorem _root_.IsSMulRegular.skewMonoidAlgebra_iff {S : Type*} [Monoid S] [DistribMulAction S k]
    {a : S} [Nonempty G] : IsSMulRegular k a ↔ IsSMulRegular (SkewMonoidAlgebra k G) a := by sorry

end Single

section One

variable [One G] [One k]

/-- The unit of the multiplication is `single 1 1`, i.e. the function that is `1` at `1` and
  zero elsewhere. -/
instance instOne : One (SkewMonoidAlgebra k G) := ⟨single 1 1⟩

@[target]
theorem ofFinsupp_one : (⟨Finsupp.single 1 1⟩ : SkewMonoidAlgebra k G) = 1 := sorry

@[simp]
theorem toFinsupp_one : (1 : SkewMonoidAlgebra k G).toFinsupp = Finsupp.single 1 1 := rfl

@[simp]
theorem toFinsupp_eq_single_one_one_iff {a : SkewMonoidAlgebra k G} :
    a.toFinsupp = Finsupp.single 1 1 ↔ a = 1 := by
  rw [← toFinsupp_one, toFinsupp_inj]

@[target, simp]
theorem ofFinsupp_eq_one {a} :
    (⟨a⟩ : SkewMonoidAlgebra k G) = 1 ↔ a = Finsupp.single 1 1 := by sorry

@[target]
theorem single_one_one  : single 1 (1 : k) = 1 := sorry

@[target]
theorem one_def : (1 : SkewMonoidAlgebra k G) = single 1 1 := sorry

@[target, simp]
theorem coeff_one_one : coeff (1 : SkewMonoidAlgebra k G) 1 = 1 := by sorry

theorem coeff_one {a : G} [Decidable (a = 1)] :
    (1 : SkewMonoidAlgebra k G).coeff a = if a = 1 then 1 else 0 := by
  classical
  simp_rw [eq_comm (a := a) (b := 1)]
  simpa using coeff_single_apply

end One

section sum

instance [DecidableEq G] [DecidableEq k] : DecidableEq (SkewMonoidAlgebra k G) :=
  Equiv.decidableEq toFinsuppAddEquiv.toEquiv

/-- `sum f g` is the sum of `g a (f.coeff a)` over the support of `f`. -/
def sum {N : Type*} [AddCommMonoid N] (f : SkewMonoidAlgebra k G) (g : G → k → N) : N :=
  f.toFinsupp.sum g

theorem sum_def {N : Type*} [AddCommMonoid N] (f : SkewMonoidAlgebra k G) (g : G → k → N) :
    sum f g = f.toFinsupp.sum g := rfl

/-- Unfolded version of `sum_def` in terms of `Finset.sum`. -/
@[target]
theorem sum_def' {N : Type*} [AddCommMonoid N] (f : SkewMonoidAlgebra k G) (g : G → k → N) :
    sum f g = ∑ a ∈ f.support, g a (f.coeff a) := sorry

@[target, simp]
theorem sum_single_index {N} [AddCommMonoid N] {a : G} {b : k} {h : G → k → N}
    (h_zero : h a 0 = 0) : (SkewMonoidAlgebra.single a b).sum h = h a b :=
  sorry

theorem map_sum {N P : Type*} [AddCommMonoid N] [AddCommMonoid P] {H : Type*} [FunLike H N P]
    [AddMonoidHomClass H N P] (h : H) (f : SkewMonoidAlgebra k G) (g : G → k → N) :
    h (sum f g) = sum f fun a b ↦ h (g a b) :=
  _root_.map_sum h _ _

/-- Variant where the image of `g` is a `SkewMonoidAlgebra`. -/
@[target]
theorem toFinsupp_sum' {k' G' : Type*} [AddCommMonoid k'] (f : SkewMonoidAlgebra k G)
    (g : G → k → SkewMonoidAlgebra k' G') :
    (sum f g).toFinsupp = Finsupp.sum f.toFinsupp (toFinsupp <| g · ·) :=
  sorry

@[target]
theorem ofFinsupp_sum {k' G' : Type*} [AddCommMonoid k'] (f : G →₀ k)
    (g : G → k → G' →₀ k'):
    (⟨Finsupp.sum f g⟩ : SkewMonoidAlgebra k' G') = sum ⟨f⟩ (⟨g · ·⟩) := by sorry

theorem sum_single (f : SkewMonoidAlgebra k G) : f.sum single = f := by
  apply toFinsupp_injective; simp only [toFinsupp_sum', toFinsupp_single, Finsupp.sum_single]

/-- Taking the `sum` under `h` is an additive homomorphism, if `h` is an additive homomorphism.
This is a more specific version of `SkewMonoidAlgebra.sum_add_index` with simpler hypotheses. -/
theorem sum_add_index' {S : Type*} [AddCommMonoid S] {f g : SkewMonoidAlgebra k G} {h : G → k → S}
    (hf : ∀ i, h i 0 = 0) (h_add : ∀ a b₁ b₂, h a (b₁ + b₂) = h a b₁ + h a b₂) :
    (f + g).sum h = f.sum h + g.sum h := by
  rw [show f + g = ⟨f.toFinsupp + g.toFinsupp⟩ by rw [ofFinsupp_add, eta]]
  exact Finsupp.sum_add_index' hf h_add

/-- Taking the `sum` under `h` is an additive homomorphism, if `h` is an additive homomorphism.
This is a more general version of `SkewMonoidAlgebra.sum_add_index'`;
the latter has simpler hypotheses. -/
@[target]
theorem sum_add_index {S : Type*} [DecidableEq G] [AddCommMonoid S]
    {f g : SkewMonoidAlgebra k G} {h : G → k → S} (h_zero : ∀ a ∈ f.support ∪ g.support, h a 0 = 0)
    (h_add : ∀ a ∈ f.support ∪ g.support, ∀ b₁ b₂, h a (b₁ + b₂) = h a b₁ + h a b₂) :
    (f + g).sum h = f.sum h + g.sum h := by sorry

@[target, simp]
theorem sum_add {S : Type*} [AddCommMonoid S] (p : SkewMonoidAlgebra k G) (f g : G → k → S) :
    (p.sum fun n x ↦ f n x + g n x) = p.sum f + p.sum g := sorry

@[target, simp]
theorem sum_zero_index {S : Type*} [AddCommMonoid S] {f : G → k → S} :
    (0 : SkewMonoidAlgebra k G).sum f = 0 := by sorry

@[target, simp]
theorem sum_zero {N : Type*} [AddCommMonoid N] {f : SkewMonoidAlgebra k G} :
    (f.sum fun _ _ ↦ (0 : N)) = 0 := sorry

@[target]
theorem sum_sum_index {α β M N P : Type*} [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
    {f : SkewMonoidAlgebra M α} {g : α → M → SkewMonoidAlgebra N β} {h : β → N → P}
    (h_zero : ∀ (a : β), h a 0 = 0)
    (h_add : ∀ (a : β) (b₁ b₂ : N), h a (b₁ + b₂) = h a b₁ + h a b₂) :
    sum (sum f g) h = sum f fun a b ↦ sum (g a b) h := by sorry

@[target, simp]
theorem coeff_sum {k' G' : Type*} [AddCommMonoid k'] {f : SkewMonoidAlgebra k G}
    {g : G → k → SkewMonoidAlgebra k' G'} {a₂ : G'} :
    (f.sum g).coeff a₂ = f.sum fun a₁ b ↦ (g a₁ b).coeff a₂ := by sorry

theorem sum_mul {S : Type*} [NonUnitalNonAssocSemiring S] (b : S) (s : SkewMonoidAlgebra k G)
    {f : G → k → S} : s.sum f * b = s.sum fun a c ↦ f a c * b := by
  simp only [sum, Finsupp.sum, Finset.sum_mul]

@[target]
theorem mul_sum {S : Type*} [NonUnitalNonAssocSemiring S] (b : S) (s : SkewMonoidAlgebra k G)
    {f : G → k → S} : b * s.sum f = s.sum fun a c ↦ b * f a c := by sorry
@[target, simp]
theorem sum_ite_eq' {N : Type*} [AddCommMonoid N] [DecidableEq G] (f : SkewMonoidAlgebra k G)
    (a : G) (b : G → k → N) : (f.sum fun (x : G) (v : k) ↦ if x = a then b x v else 0) =
      if a ∈ f.support then b a (f.coeff a) else 0 := by sorry

theorem smul_sum {M : Type*} {R : Type*} [AddCommMonoid M] [DistribSMul R M]
    {v : SkewMonoidAlgebra k G} {c : R} {h : G → k → M} :
    c • v.sum h = v.sum fun a b ↦ c • h a b := Finsupp.smul_sum

theorem sum_congr {f : SkewMonoidAlgebra k G} {M : Type*} [AddCommMonoid M] {g₁ g₂ : G → k → M}
    (h : ∀ x ∈ f.support, g₁ x (f.coeff x) = g₂ x (f.coeff x)) :
    f.sum g₁ = f.sum g₂ := Finset.sum_congr rfl h

end sum

end AddCommMonoid

end SkewMonoidAlgebra
