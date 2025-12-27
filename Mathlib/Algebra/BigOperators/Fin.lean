import VerifiedAgora.tagger
/-
Copyright (c) 2020 Yury Kudryashov, Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Anne Baanen
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Fin
import Mathlib.Logic.Equiv.Fin

/-!
# Big operators and `Fin`

Some results about products and sums over the type `Fin`.

The most important results are the induction formulas `Fin.prod_univ_castSucc`
and `Fin.prod_univ_succ`, and the formula `Fin.prod_const` for the product of a
constant function. These results have variants for sums instead of products.

## Main declarations

* `finFunctionFinEquiv`: An explicit equivalence between `Fin n → Fin m` and `Fin (m ^ n)`.
-/

assert_not_exists Field

open Finset

variable {α : Type*} {β : Type*}

namespace Finset

@[target] theorem prod_range [CommMonoid β] {n : ℕ} (f : ℕ → β) :
    ∏ i ∈ Finset.range n, f i = ∏ i : Fin n, f i := by sorry


end Finset

namespace Fin

@[target] theorem prod_ofFn [CommMonoid β] {n : ℕ} (f : Fin n → β) : (List.ofFn f).prod = ∏ i, f i := by
  sorry


@[target] theorem prod_univ_def [CommMonoid β] {n : ℕ} (f : Fin n → β) :
    ∏ i, f i = ((List.finRange n).map f).prod := by
  sorry


/-- A product of a function `f : Fin 0 → β` is `1` because `Fin 0` is empty -/
@[to_additive "A sum of a function `f : Fin 0 → β` is `0` because `Fin 0` is empty"]
theorem prod_univ_zero [CommMonoid β] (f : Fin 0 → β) : ∏ i, f i = 1 :=
  rfl

/-- A product of a function `f : Fin (n + 1) → β` over all `Fin (n + 1)`
is the product of `f x`, for some `x : Fin (n + 1)` times the remaining product -/
/-- A product of a function `f : Fin (n + 1) → β` over all `Fin (n + 1)`
is the product of `f x`, for some `x : Fin (n + 1)` times the remaining product -/
@[target] theorem prod_univ_succAbove [CommMonoid β] {n : ℕ} (f : Fin (n + 1) → β) (x : Fin (n + 1)) :
    ∏ i, f i = f x * ∏ i : Fin n, f (x.succAbove i) := by
  sorry


/-- A product of a function `f : Fin (n + 1) → β` over all `Fin (n + 1)`
is the product of `f 0` plus the remaining product -/
@[to_additive "A sum of a function `f : Fin (n + 1) → β` over all `Fin (n + 1)` is the sum of
`f 0` plus the remaining sum"]
theorem prod_univ_succ [CommMonoid β] {n : ℕ} (f : Fin (n + 1) → β) :
    ∏ i, f i = f 0 * ∏ i : Fin n, f i.succ :=
  prod_univ_succAbove f 0

/-- A product of a function `f : Fin (n + 1) → β` over all `Fin (n + 1)`
is the product of `f (Fin.last n)` plus the remaining product -/
/-- A product of a function `f : Fin (n + 1) → β` over all `Fin (n + 1)`
is the product of `f (Fin.last n)` plus the remaining product -/
@[target] theorem prod_univ_castSucc [CommMonoid β] {n : ℕ} (f : Fin (n + 1) → β) :
    ∏ i, f i = (∏ i : Fin n, f (Fin.castSucc i)) * f (last n) := by
  sorry


@[target] theorem prod_univ_get [CommMonoid α] (l : List α) : ∏ i : Fin l.length, l[i.1] = l.prod := by
  sorry


@[to_additive (attr := simp)]
theorem prod_univ_get' [CommMonoid β] (l : List α) (f : α → β) :
    ∏ i : Fin l.length, f l[i.1] = (l.map f).prod := by
  simp [Finset.prod_eq_multiset_prod]

@[target] theorem prod_cons [CommMonoid β] {n : ℕ} (x : β) (f : Fin n → β) :
    (∏ i : Fin n.succ, (cons x f : Fin n.succ → β) i) = x * ∏ i : Fin n, f i := by
  sorry


@[target] theorem prod_snoc [CommMonoid β] {n : ℕ} (x : β) (f : Fin n → β) :
    (∏ i : Fin n.succ, (snoc f x : Fin n.succ → β) i) = (∏ i : Fin n, f i) * x := by
  sorry


@[target] theorem prod_univ_one [CommMonoid β] (f : Fin 1 → β) : ∏ i, f i = f 0 := by sorry


@[target] theorem prod_univ_two [CommMonoid β] (f : Fin 2 → β) : ∏ i, f i = f 0 * f 1 := by
  sorry


@[to_additive]
theorem prod_univ_two' [CommMonoid β] (f : α → β) (a b : α) :
    ∏ i, f (![a, b] i) = f a * f b :=
  prod_univ_two _

@[target] theorem prod_univ_three [CommMonoid β] (f : Fin 3 → β) : ∏ i, f i = f 0 * f 1 * f 2 := by
  sorry


@[target] theorem prod_univ_four [CommMonoid β] (f : Fin 4 → β) : ∏ i, f i = f 0 * f 1 * f 2 * f 3 := by
  sorry


@[target] theorem prod_univ_five [CommMonoid β] (f : Fin 5 → β) :
    ∏ i, f i = f 0 * f 1 * f 2 * f 3 * f 4 := by
  sorry


@[to_additive]
theorem prod_univ_six [CommMonoid β] (f : Fin 6 → β) :
    ∏ i, f i = f 0 * f 1 * f 2 * f 3 * f 4 * f 5 := by
  rw [prod_univ_castSucc, prod_univ_five]
  rfl

@[target] theorem prod_univ_seven [CommMonoid β] (f : Fin 7 → β) :
    ∏ i, f i = f 0 * f 1 * f 2 * f 3 * f 4 * f 5 * f 6 := by
  sorry


@[target] theorem prod_univ_eight [CommMonoid β] (f : Fin 8 → β) :
    ∏ i, f i = f 0 * f 1 * f 2 * f 3 * f 4 * f 5 * f 6 * f 7 := by
  sorry


theorem sum_pow_mul_eq_add_pow {n : ℕ} {R : Type*} [CommSemiring R] (a b : R) :
    (∑ s : Finset (Fin n), a ^ s.card * b ^ (n - s.card)) = (a + b) ^ n := by
  simpa using Fintype.sum_pow_mul_eq_add_pow (Fin n) a b

@[target] theorem prod_const [CommMonoid α] (n : ℕ) (x : α) : ∏ _i : Fin n, x = x ^ n := by sorry


theorem sum_const [AddCommMonoid α] (n : ℕ) (x : α) : ∑ _i : Fin n, x = n • x := by simp

@[target] theorem prod_Ioi_zero {M : Type*} [CommMonoid M] {n : ℕ} {v : Fin n.succ → M} :
    ∏ i ∈ Ioi 0, v i = ∏ j : Fin n, v j.succ := by
  sorry


@[target] theorem prod_Ioi_succ {M : Type*} [CommMonoid M] {n : ℕ} (i : Fin n) (v : Fin n.succ → M) :
    ∏ j ∈ Ioi i.succ, v j = ∏ j ∈ Ioi i, v j.succ := by
  sorry


@[to_additive]
theorem prod_congr' {M : Type*} [CommMonoid M] {a b : ℕ} (f : Fin b → M) (h : a = b) :
    (∏ i : Fin a, f (i.cast h)) = ∏ i : Fin b, f i := by
  subst h
  congr

@[target] theorem prod_univ_add {M : Type*} [CommMonoid M] {a b : ℕ} (f : Fin (a + b) → M) :
    (∏ i : Fin (a + b), f i) = (∏ i : Fin a, f (castAdd b i)) * ∏ i : Fin b, f (natAdd a i) := by
  sorry


@[target] theorem prod_trunc {M : Type*} [CommMonoid M] {a b : ℕ} (f : Fin (a + b) → M)
    (hf : ∀ j : Fin b, f (natAdd a j) = 1) :
    (∏ i : Fin (a + b), f i) = ∏ i : Fin a, f (castLE (Nat.le.intro rfl) i) := by
  sorry


@[target] lemma sum_neg_one_pow (R : Type*) [Ring R] (m : ℕ) :
    (∑ n : Fin m, (-1) ^ n.1 : R) = if Even m then 0 else 1 := by
  sorry


section PartialProd

variable [Monoid α] {n : ℕ}

/-- For `f = (a₁, ..., aₙ)` in `αⁿ`, `partialProd f` is `(1, a₁, a₁a₂, ..., a₁...aₙ)` in `αⁿ⁺¹`. -/
@[to_additive "For `f = (a₁, ..., aₙ)` in `αⁿ`, `partialSum f` is\n
`(0, a₁, a₁ + a₂, ..., a₁ + ... + aₙ)` in `αⁿ⁺¹`."]
def partialProd (f : Fin n → α) (i : Fin (n + 1)) : α :=
  ((List.ofFn f).take i).prod

@[target] theorem partialProd_zero (f : Fin n → α) : partialProd f 0 = 1 := by sorry


@[target] theorem partialProd_succ (f : Fin n → α) (j : Fin n) :
    partialProd f j.succ = partialProd f (Fin.castSucc j) * f j := by
  sorry


@[to_additive]
theorem partialProd_succ' (f : Fin (n + 1) → α) (j : Fin (n + 1)) :
    partialProd f j.succ = f 0 * partialProd (Fin.tail f) j := by
  simp [partialProd]
  rfl

@[target] theorem partialProd_left_inv {G : Type*} [Group G] (f : Fin (n + 1) → G) :
    (f 0 • partialProd fun i : Fin n => (f i)⁻¹ * f i.succ) = f :=
  funext fun x => Fin.inductionOn x (by sorry


@[target] theorem partialProd_right_inv {G : Type*} [Group G] (f : Fin n → G) (i : Fin n) :
    (partialProd f (Fin.castSucc i))⁻¹ * partialProd f i.succ = f i := by
  sorry


/-- Let `(g₀, g₁, ..., gₙ)` be a tuple of elements in `Gⁿ⁺¹`.
Then if `k < j`, this says `(g₀g₁...gₖ₋₁)⁻¹ * g₀g₁...gₖ = gₖ`.
If `k = j`, it says `(g₀g₁...gₖ₋₁)⁻¹ * g₀g₁...gₖ₊₁ = gₖgₖ₊₁`.
If `k > j`, it says `(g₀g₁...gₖ)⁻¹ * g₀g₁...gₖ₊₁ = gₖ₊₁.`
Useful for defining group cohomology. -/
/-- Let `(g₀, g₁, ..., gₙ)` be a tuple of elements in `Gⁿ⁺¹`.
Then if `k < j`, this says `(g₀g₁...gₖ₋₁)⁻¹ * g₀g₁...gₖ = gₖ`.
If `k = j`, it says `(g₀g₁...gₖ₋₁)⁻¹ * g₀g₁...gₖ₊₁ = gₖgₖ₊₁`.
If `k > j`, it says `(g₀g₁...gₖ)⁻¹ * g₀g₁...gₖ₊₁ = gₖ₊₁.`
Useful for defining group cohomology. -/
@[target] theorem inv_partialProd_mul_eq_contractNth {G : Type*} [Group G] (g : Fin (n + 1) → G)
    (j : Fin (n + 1)) (k : Fin n) :
    (partialProd g (j.succ.succAbove (Fin.castSucc k)))⁻¹ * partialProd g (j.succAbove k).succ =
      j.contractNth (· * ·) g k := by
  sorry


end PartialProd

end Fin

/-- Equivalence between `Fin n → Fin m` and `Fin (m ^ n)`. -/
@[simps!]
def finFunctionFinEquiv {m n : ℕ} : (Fin n → Fin m) ≃ Fin (m ^ n) :=
  Equiv.ofRightInverseOfCardLE (le_of_eq <| by simp_rw [Fintype.card_fun, Fintype.card_fin])
    (fun f => ⟨∑ i, f i * m ^ (i : ℕ), by
      induction n with
      | zero => simp
      | succ n ih =>
        cases m
        · exact isEmptyElim (f <| Fin.last _)
        simp_rw [Fin.sum_univ_castSucc, Fin.coe_castSucc, Fin.val_last]
        refine (Nat.add_lt_add_of_lt_of_le (ih _) <| Nat.mul_le_mul_right _
          (Fin.is_le _)).trans_eq ?_
        rw [← one_add_mul (_ : ℕ), add_comm, pow_succ']⟩)
    (fun a b => ⟨a / m ^ (b : ℕ) % m, by
      rcases n with - | n
      · exact b.elim0
      rcases m with - | m
      · rw [zero_pow n.succ_ne_zero] at a
        exact a.elim0
      · exact Nat.mod_lt _ m.succ_pos⟩)
    fun a => by
      dsimp
      induction n with
      | zero => subsingleton [(finCongr <| pow_zero _).subsingleton]
      | succ n ih =>
        simp_rw [Fin.forall_iff, Fin.ext_iff] at ih
        ext
        simp_rw [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, pow_zero, Nat.div_one,
          mul_one, pow_succ', ← Nat.div_div_eq_div_mul, mul_left_comm _ m, ← mul_sum]
        rw [ih _ (Nat.div_lt_of_lt_mul (a.is_lt.trans_eq (pow_succ' _ _))), Nat.mod_add_div]

@[target] theorem finFunctionFinEquiv_apply {m n : ℕ} (f : Fin n → Fin m) :
    (finFunctionFinEquiv f : ℕ) = ∑ i : Fin n, ↑(f i) * m ^ (i : ℕ) := by sorry


@[target] theorem finFunctionFinEquiv_single {m n : ℕ} [NeZero m] (i : Fin n) (j : Fin m) :
    (finFunctionFinEquiv (Pi.single i j) : ℕ) = j * m ^ (i : ℕ) := by
  sorry


/-- Equivalence between `∀ i : Fin m, Fin (n i)` and `Fin (∏ i : Fin m, n i)`. -/
/-- Equivalence between `∀ i : Fin m, Fin (n i)` and `Fin (∏ i : Fin m, n i)`. -/
def finPiFinEquiv {m : ℕ} {n : Fin m → ℕ} : (∀ i : Fin m, Fin (n i)) ≃ Fin (∏ i : Fin m, n i) :=
  Equiv.ofRightInverseOfCardLE (le_of_eq <| by sorry


@[target] theorem finPiFinEquiv_apply {m : ℕ} {n : Fin m → ℕ} (f : ∀ i : Fin m, Fin (n i)) :
    (finPiFinEquiv f : ℕ) = ∑ i, f i * ∏ j, n (Fin.castLE i.is_lt.le j) := by sorry


@[target] theorem finPiFinEquiv_single {m : ℕ} {n : Fin m → ℕ} [∀ i, NeZero (n i)] (i : Fin m)
    (j : Fin (n i)) :
    (finPiFinEquiv (Pi.single i j : ∀ i : Fin m, Fin (n i)) : ℕ) =
      j * ∏ j, n (Fin.castLE i.is_lt.le j) := by
  sorry


/-- Equivalence between the Sigma type `(i : Fin m) × Fin (n i)` and `Fin (∑ i : Fin m, n i)`. -/
def finSigmaFinEquiv {m : ℕ} {n : Fin m → ℕ} : (i : Fin m) × Fin (n i) ≃ Fin (∑ i : Fin m, n i) :=
  match m with
  | 0 => @Equiv.equivOfIsEmpty _ _ _ (by simp; exact Fin.isEmpty')
  | Nat.succ m =>
    calc _ ≃ _ := (@finSumFinEquiv m 1).sigmaCongrLeft.symm
      _ ≃ _ := Equiv.sumSigmaDistrib _
      _ ≃ _ := finSigmaFinEquiv.sumCongr (Equiv.uniqueSigma _)
      _ ≃ _ := finSumFinEquiv
      _ ≃ _ := finCongr (Fin.sum_univ_castSucc n).symm

@[target] theorem finSigmaFinEquiv_apply {m : ℕ} {n : Fin m → ℕ} (k : (i : Fin m) × Fin (n i)) :
    (finSigmaFinEquiv k : ℕ) = ∑ i : Fin k.1, n (Fin.castLE k.1.2.le i) + k.2 := by
  sorry


/-- `finSigmaFinEquiv` on `Fin 1 × f` is just `f` -/
theorem finSigmaFinEquiv_one {n : Fin 1 → ℕ} (ij : (i : Fin 1) × Fin (n i)) :
    (finSigmaFinEquiv ij : ℕ) = ij.2 := by
  rw [finSigmaFinEquiv_apply, add_left_eq_self]
  apply @Finset.sum_of_isEmpty _ _ _ _ (by simpa using Fin.isEmpty')

namespace List

section CommMonoid

variable [CommMonoid α]

@[target] theorem prod_take_ofFn {n : ℕ} (f : Fin n → α) (i : ℕ) :
    ((ofFn f).take i).prod = ∏ j ∈ Finset.univ.filter fun j : Fin n => j.val < i, f j := by
  sorry


@[to_additive]
theorem prod_ofFn {n : ℕ} {f : Fin n → α} : (ofFn f).prod = ∏ i, f i :=
  Fin.prod_ofFn f

end CommMonoid

@[target] theorem alternatingProd_eq_finset_prod {G : Type*} [CommGroup G] :
    ∀ (L : List G), alternatingProd L = ∏ i : Fin L.length, L[i] ^ (-1 : ℤ) ^ (i : ℕ)
  | [] => by
    sorry


end List
