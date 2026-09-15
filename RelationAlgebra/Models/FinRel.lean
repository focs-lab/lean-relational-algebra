import Mathlib.Data.Fintype.Order
import Mathlib.Data.Fintype.Pi
import RelationAlgebra.Converse
import RelationAlgebra.Kleene.Complete

/-!
# The model of finite, decidable relations

This is the Lean counterpart of `theories/fhrel.v` in Damien Pous' Rocq library
[relation-algebra](https://github.com/damien-pous/relation-algebra), to whom this model is due
(upstream it is a development by Christian Doczkal, using MathComp's `finType` and `connect`).

A `FinRel α β` is a Boolean-valued matrix `α → β → Bool`.  Over finite types every operation of
relation algebra becomes *decidable* and *computable*: unlike `SetRel α β`, whose Kleene star is
an inductively defined `Prop`, the star of a `FinRel` is a Boolean matrix one can evaluate.

## Design

* `0`, `1`, `+`, `*`, converse and complement are computable Boolean matrix operations.
* The Kleene star is `FinRel.tc`, which computes `(1 + R) ^ (card α * card α + 1)`
  (`FinRel.tc_def`).  The chain `(1 + R) ^ n` is increasing in a lattice of `card α * card α`
  "cells", so it is stationary from that exponent on (`FinRel.pow_succ_self_eq`); this is what
  makes `tc` the closure.  The iteration itself is carried out on *sets of pairs*
  (`FinRel.powFinset`) so that it runs in polynomial time.  Warshall's algorithm would be
  asymptotically better, but this version is short to justify and reduces in the kernel.
* The lattice structure is the pointwise one coming from `Bool`; since `FinRel α β` is finite it
  is a *complete* lattice (`Fintype.toCompleteLattice`), hence a `CompleteKleeneAlgebra`.  Only
  the infinitary operations `sSup`/`sInf` are noncomputable; everything else evaluates.
* `FinRel.toSetRel` maps the model into the reference model `SetRel α β` and is an isomorphism
  of complete Kleene algebras onto it (`FinRel.orderIsoSetRel` and the `toSetRel_*` lemmas),
  which validates the definitions above — in particular `toSetRel_kstar`.

## Evaluating

```lean
-- the successor relation on `Fin 4`
#eval FinRel.succExample 0 1                              -- true
#eval (FinRel.succExample∗) 0 3                           -- true  (0 → 1 → 2 → 3)
#eval (FinRel.succExample∗) 3 0                           -- false
#eval decide (FinRel.succExample ≤ FinRel.succExample∗)   -- true
```

## References

* [D. Pous, *Relation Algebra and KAT in Coq*, file `theories/fhrel.v`,
  <https://github.com/damien-pous/relation-algebra>]
-/

open scoped Computability

/-- A decidable relation between finite types, as a Boolean-valued function. -/
def FinRel (α β : Type*) : Type _ := α → β → Bool

namespace FinRel

variable {α β γ : Type*}

@[ext]
theorem ext {R S : FinRel α β} (h : ∀ a b, R a b = S a b) : R = S :=
  funext fun a ↦ funext fun b ↦ h a b

theorem ext_iff' {R S : FinRel α β} (h : ∀ a b, R a b ↔ S a b) : R = S :=
  ext fun a b ↦ Bool.eq_iff_iff.2 (h a b)

/-! ### The Boolean algebra structure

All of it is the pointwise structure of `Bool`, and all of it computes. -/

/-- Finite relations inherit the pointwise Boolean algebra of `Bool`. -/
instance instBooleanAlgebra : BooleanAlgebra (FinRel α β) :=
  inferInstanceAs (BooleanAlgebra (α → β → Bool))

/-- Equality of finite relations is decidable. -/
instance instDecidableEq [Fintype α] [Fintype β] : DecidableEq (FinRel α β) :=
  inferInstanceAs (DecidableEq (α → β → Bool))

/-- Finite relations between finite types form a finite type. -/
instance instFintype [DecidableEq α] [Fintype α] [DecidableEq β] [Fintype β] :
    Fintype (FinRel α β) :=
  inferInstanceAs (Fintype (α → β → Bool))

theorem le_def {R S : FinRel α β} : R ≤ S ↔ ∀ a b, R a b → S a b :=
  ⟨fun h a b hab ↦ Bool.le_iff_imp.1 (h a b) hab, fun h a b ↦ Bool.le_iff_imp.2 (h a b)⟩

/-- Inclusion of finite relations is decidable, so it can be checked by `decide`. -/
instance decidableLE [Fintype α] [Fintype β] (R S : FinRel α β) : Decidable (R ≤ S) :=
  decidable_of_iff _ le_def.symm

@[simp] theorem sup_apply (R S : FinRel α β) (a : α) (b : β) :
    (R ⊔ S) a b = (R a b || S a b) := rfl

@[simp] theorem inf_apply (R S : FinRel α β) (a : α) (b : β) :
    (R ⊓ S) a b = (R a b && S a b) := rfl

@[simp] theorem compl_apply (R : FinRel α β) (a : α) (b : β) : Rᶜ a b = !R a b := rfl

@[simp] theorem bot_apply (a : α) (b : β) : (⊥ : FinRel α β) a b = false := rfl

@[simp] theorem top_apply (a : α) (b : β) : (⊤ : FinRel α β) a b = true := rfl

/-! ### The Kleene algebra operations -/

/-- The empty relation. -/
instance instZero : Zero (FinRel α β) := ⟨fun _ _ ↦ false⟩

/-- Union of finite relations. -/
instance instAdd : Add (FinRel α β) := ⟨fun R S a b ↦ R a b || S a b⟩

/-- The identity relation, i.e. the identity matrix. -/
instance instOne [DecidableEq α] : One (FinRel α α) := ⟨fun a b ↦ decide (a = b)⟩

/-- Composition of finite relations: a Boolean matrix product. -/
def comp [Fintype β] (R : FinRel α β) (S : FinRel β γ) : FinRel α γ :=
  fun a c ↦ decide (∃ b, R a b ∧ S b c)

/-- Composition of finite relations on a fixed finite type. -/
instance instMul [Fintype α] : Mul (FinRel α α) := ⟨comp⟩

/-- Converse of a finite relation: the transpose of the matrix. -/
instance instStar : Star (FinRel α α) := ⟨fun R a b ↦ R b a⟩

@[simp] theorem zero_apply (a : α) (b : β) : (0 : FinRel α β) a b = false := rfl

@[simp] theorem add_apply (R S : FinRel α β) (a : α) (b : β) :
    (R + S) a b = (R a b || S a b) := rfl

@[simp] theorem one_apply [DecidableEq α] (a b : α) :
    (1 : FinRel α α) a b = decide (a = b) := rfl

@[simp] theorem comp_apply [Fintype β] (R : FinRel α β) (S : FinRel β γ) (a : α) (c : γ) :
    comp R S a c = decide (∃ b, R a b ∧ S b c) := rfl

@[simp] theorem mul_apply [Fintype α] (R S : FinRel α α) (a c : α) :
    (R * S) a c = decide (∃ b, R a b ∧ S b c) := rfl

@[simp] theorem star_apply (R : FinRel α α) (a b : α) : star R a b = R b a := rfl

theorem one_iff [DecidableEq α] {a b : α} : (1 : FinRel α α) a b ↔ a = b := by simp

theorem mul_iff [Fintype α] {R S : FinRel α α} {a c : α} :
    (R * S) a c ↔ ∃ b, R a b ∧ S b c := by simp

/-- Finite relations on a finite type form a monoid under composition. -/
instance instMonoid [Fintype α] [DecidableEq α] : Monoid (FinRel α α) where
  mul_assoc R S T := ext_iff' fun a d ↦ by
    simp only [mul_iff]
    exact ⟨fun ⟨c, ⟨b, hab, hbc⟩, hcd⟩ ↦ ⟨b, hab, c, hbc, hcd⟩,
      fun ⟨b, hab, c, hbc, hcd⟩ ↦ ⟨c, ⟨b, hab, hbc⟩, hcd⟩⟩
  one_mul R := ext_iff' fun a b ↦ by
    simp only [mul_iff, one_iff]
    exact ⟨fun ⟨c, hac, hcb⟩ ↦ hac ▸ hcb, fun h ↦ ⟨a, rfl, h⟩⟩
  mul_one R := ext_iff' fun a b ↦ by
    simp only [mul_iff, one_iff]
    exact ⟨fun ⟨c, hac, hcb⟩ ↦ hcb ▸ hac, fun h ↦ ⟨b, h, rfl⟩⟩
  npow := npowRec

/-- Finite relations on a finite type form an idempotent semiring. -/
instance instIdemSemiring [Fintype α] [DecidableEq α] : IdemSemiring (FinRel α α) where
  __ : Monoid (FinRel α α) := instMonoid
  __ : SemilatticeSup (FinRel α α) := inferInstance
  __ : OrderBot (FinRel α α) := inferInstance
  add_assoc R S T := ext fun a b ↦ Bool.or_assoc _ _ _
  zero_add R := ext fun a b ↦ Bool.false_or _
  add_zero R := ext fun a b ↦ Bool.or_false _
  add_comm R S := ext fun a b ↦ Bool.or_comm _ _
  nsmul := nsmulRec
  left_distrib R S T := ext_iff' fun a c ↦ by
    simp only [add_apply, mul_apply, Bool.or_eq_true, decide_eq_true_eq]
    exact ⟨fun ⟨b, hab, hbc⟩ ↦ hbc.imp (fun h ↦ ⟨b, hab, h⟩) fun h ↦ ⟨b, hab, h⟩,
      fun h ↦ h.elim (fun ⟨b, hab, hbc⟩ ↦ ⟨b, hab, Or.inl hbc⟩)
        fun ⟨b, hab, hbc⟩ ↦ ⟨b, hab, Or.inr hbc⟩⟩
  right_distrib R S T := ext_iff' fun a c ↦ by
    simp only [add_apply, mul_apply, Bool.or_eq_true, decide_eq_true_eq]
    exact ⟨fun ⟨b, hab, hbc⟩ ↦ hab.imp (fun h ↦ ⟨b, h, hbc⟩) fun h ↦ ⟨b, h, hbc⟩,
      fun h ↦ h.elim (fun ⟨b, hab, hbc⟩ ↦ ⟨b, Or.inl hab, hbc⟩)
        fun ⟨b, hab, hbc⟩ ↦ ⟨b, Or.inr hab, hbc⟩⟩
  zero_mul R := ext_iff' fun a c ↦ by simp
  mul_zero R := ext_iff' fun a c ↦ by simp
  add_eq_sup R S := rfl

/-! ### The Kleene star, computably

The powers of a reflexive relation form an increasing chain in the finite lattice of relations,
so the chain is stationary; counting the related pairs bounds the time it takes. -/

/-- The number of pairs related by a finite relation. -/
def card [Fintype α] [Fintype β] (R : FinRel α β) : ℕ :=
  (Finset.univ.filter fun p : α × β ↦ R p.1 p.2).card

theorem card_le [Fintype α] [Fintype β] (R : FinRel α β) :
    card R ≤ Fintype.card α * Fintype.card β := by
  refine (Finset.card_filter_le _ _).trans ?_
  rw [Finset.card_univ, Fintype.card_prod]

theorem card_lt_card [Fintype α] {R S : FinRel α α} (h : R ≤ S) (hne : R ≠ S) :
    card R < card S := by
  obtain ⟨a, b, hS, hR⟩ : ∃ a b, S a b ∧ ¬ R a b := by
    by_contra hcon
    refine hne (le_antisymm h (le_def.2 fun a b hb ↦ ?_))
    by_contra hR
    exact hcon ⟨a, b, hb, hR⟩
  have hsub : (Finset.univ.filter fun p : α × α ↦ R p.1 p.2) ⊆
      Finset.univ.filter fun p : α × α ↦ S p.1 p.2 := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact le_def.1 h _ _ hp
  refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).2 ⟨(a, b), ?_, ?_⟩) <;>
    simp [Finset.mem_filter, hS, hR]

/-- The number of iteration steps after which the powers of a reflexive relation are stationary. -/
def closureSteps (α : Type*) [Fintype α] : ℕ := Fintype.card α * Fintype.card α + 1

section Star

variable [Fintype α] [DecidableEq α]

theorem le_pow_succ {S : FinRel α α} (hS : 1 ≤ S) (n : ℕ) : S ^ n ≤ S ^ (n + 1) := by
  rw [pow_succ]
  calc S ^ n = S ^ n * 1 := (mul_one _).symm
    _ ≤ S ^ n * S := mul_le_mul_right hS _

theorem one_le_pow {S : FinRel α α} (hS : 1 ≤ S) : ∀ n : ℕ, (1 : FinRel α α) ≤ S ^ n
  | 0 => (pow_zero S).ge
  | n + 1 => (one_le_pow hS n).trans (le_pow_succ hS n)

theorem pow_eq_of_pow_eq {S : FinRel α α} {n : ℕ} (h : S ^ n = S ^ (n + 1)) :
    S ^ (n + 1) = S ^ (n + 2) :=
  calc S ^ (n + 1) = S ^ n * S := pow_succ S n
    _ = S ^ (n + 1) * S := by rw [h]
    _ = S ^ (n + 2) := (pow_succ S (n + 1)).symm

theorem le_card_pow {S : FinRel α α} (hS : 1 ≤ S) :
    ∀ n : ℕ, S ^ n ≠ S ^ (n + 1) → n ≤ card (S ^ n)
  | 0, _ => Nat.zero_le _
  | n + 1, hne => by
    have hne' : S ^ n ≠ S ^ (n + 1) := fun h ↦ hne (pow_eq_of_pow_eq h)
    exact Nat.succ_le_of_lt
      (lt_of_le_of_lt (le_card_pow hS n hne') (card_lt_card (le_pow_succ hS n) hne'))

/-- The powers of a reflexive finite relation are stationary from `closureSteps α` on: there are
only `card α * card α` pairs to add, and each non-stationary step adds one. -/
theorem pow_succ_self_eq {S : FinRel α α} (hS : 1 ≤ S) :
    S ^ (closureSteps α + 1) = S ^ closureSteps α := by
  by_contra hne
  have hne' : S ^ closureSteps α ≠ S ^ (closureSteps α + 1) := fun h ↦ hne h.symm
  have h₁ := le_card_pow hS _ hne'
  have h₂ := card_le (S ^ closureSteps α)
  have h₃ : closureSteps α = Fintype.card α * Fintype.card α + 1 := rfl
  omega

/-- The set of pairs related by `S ^ n`, computed by iterated Boolean matrix multiplication.
Iterating on *sets of pairs* rather than on Boolean-matrix functions is what makes this run in
polynomial time: composing functions repeatedly would re-evaluate the factors exponentially
often, whereas the `let` below forces each intermediate matrix exactly once. -/
def powFinset (S : FinRel α α) : ℕ → Finset (α × α)
  | 0 => Finset.univ.filter fun p ↦ p.1 = p.2
  | n + 1 =>
    let m := powFinset S n
    Finset.univ.filter fun p ↦ ∃ b, (p.1, b) ∈ m ∧ S b p.2

theorem mem_powFinset (S : FinRel α α) :
    ∀ (n : ℕ) (a b : α), (a, b) ∈ powFinset S n ↔ (S ^ n) a b
  | 0, a, b => by simp [powFinset, pow_zero]
  | n + 1, a, b => by
    simp only [powFinset, Finset.mem_filter, Finset.mem_univ, true_and, pow_succ, mul_iff]
    exact exists_congr fun c ↦ and_congr_left' (mem_powFinset S n a c)

/-- The reflexive-transitive closure of a finite relation, computed as `(1 + R) ^ n` for `n`
large enough that the powers are stationary.  This is a computable Boolean matrix. -/
def tc (R : FinRel α α) : FinRel α α :=
  let m := powFinset (1 + R) (closureSteps α)
  fun a b ↦ decide ((a, b) ∈ m)

theorem tc_def (R : FinRel α α) : tc R = (1 + R) ^ closureSteps α :=
  ext_iff' fun a b ↦ by simp [tc, mem_powFinset]

-- `Fintype α` is not visible in the statement but is needed for the `IdemSemiring`
-- instance used in the proof.
set_option linter.unusedFintypeInType false in
theorem one_le_one_add (R : FinRel α α) : (1 : FinRel α α) ≤ 1 + R := le_self_add

theorem one_add_mul_tc (R : FinRel α α) : (1 + R) * tc R = tc R := by
  rw [tc_def, ← pow_succ' (1 + R), pow_succ_self_eq (one_le_one_add R)]

theorem tc_mul_one_add (R : FinRel α α) : tc R * (1 + R) = tc R := by
  rw [tc_def, ← pow_succ (1 + R), pow_succ_self_eq (one_le_one_add R)]

theorem one_le_tc (R : FinRel α α) : 1 ≤ tc R :=
  (tc_def R).ge.trans' (one_le_pow (one_le_one_add R) _)

/-- Finite relations on a finite type form a Kleene algebra, with the *computable* star `tc`. -/
instance instKleeneAlgebra : KleeneAlgebra (FinRel α α) where
  __ := instIdemSemiring
  kstar := tc
  one_le_kstar := one_le_tc
  mul_kstar_le_kstar R := by
    calc R * tc R ≤ (1 + R) * tc R := mul_le_mul_left le_add_self _
      _ = tc R := one_add_mul_tc R
  kstar_mul_le_kstar R := by
    calc tc R * R ≤ tc R * (1 + R) := mul_le_mul_right le_add_self _
      _ = tc R := tc_mul_one_add R
  mul_kstar_le_self R S h := by
    have hS : S * (1 + R) ≤ S := by rw [mul_add, mul_one]; exact add_le le_rfl h
    have key : ∀ n : ℕ, S * (1 + R) ^ n ≤ S := by
      intro n
      induction n with
      | zero => rw [pow_zero, mul_one]
      | succ n ih =>
        calc S * (1 + R) ^ (n + 1) = S * (1 + R) ^ n * (1 + R) := by rw [pow_succ, mul_assoc]
          _ ≤ S * (1 + R) := mul_le_mul_left ih _
          _ ≤ S := hS
    rw [tc_def]
    exact key _
  kstar_mul_le_self R S h := by
    have hS : (1 + R) * S ≤ S := by rw [add_mul, one_mul]; exact add_le le_rfl h
    have key : ∀ n : ℕ, (1 + R) ^ n * S ≤ S := by
      intro n
      induction n with
      | zero => rw [pow_zero, one_mul]
      | succ n ih =>
        calc (1 + R) ^ (n + 1) * S = (1 + R) * ((1 + R) ^ n * S) := by
              rw [pow_succ', mul_assoc]
          _ ≤ (1 + R) * S := mul_le_mul_right ih _
          _ ≤ S := hS
    rw [tc_def]
    exact key _

theorem kstar_eq_tc (R : FinRel α α) : R∗ = tc R := rfl

end Star

/-! ### Completeness of the lattice, and the relation algebra structure -/

/-- A finite bounded lattice is complete, so finite relations form a complete lattice.  Only
`sSup`/`sInf` are noncomputable here; the lattice operations are the computable pointwise ones. -/
noncomputable instance instCompleteLattice [DecidableEq α] [Fintype α] [DecidableEq β]
    [Fintype β] : CompleteLattice (FinRel α β) :=
  Fintype.toCompleteLattice _

section Complete

variable [DecidableEq α] [Fintype α] [DecidableEq β] [Fintype β]

theorem sSup_apply_iff {𝒮 : Set (FinRel α β)} {a : α} {b : β} :
    sSup 𝒮 a b ↔ ∃ R ∈ 𝒮, R a b := by
  classical
  refine ⟨fun h ↦ ?_, fun ⟨R, hR, hab⟩ ↦ le_def.1 (le_sSup hR) _ _ hab⟩
  have hle : sSup 𝒮 ≤ (fun x y ↦ decide (∃ R ∈ 𝒮, R x y) : FinRel α β) :=
    sSup_le fun R hR ↦ le_def.2 fun x y hxy ↦ by simpa using ⟨R, hR, hxy⟩
  simpa using le_def.1 hle _ _ h

theorem iSup_apply_iff {ι : Sort*} {f : ι → FinRel α β} {a : α} {b : β} :
    (⨆ i, f i) a b ↔ ∃ i, (f i) a b := by
  simp only [iSup, sSup_apply_iff, Set.mem_range, exists_exists_eq_and]

end Complete

section CompleteHom

variable [DecidableEq α] [Fintype α]

/-- Composition distributes over arbitrary unions. -/
instance instIsQuantale : IsQuantale (FinRel α α) where
  mul_sSup_distrib R 𝒮 := ext_iff' fun a c ↦ by
    simp only [mul_iff, sSup_apply_iff, iSup_apply_iff, exists_prop]
    exact ⟨fun ⟨b, hab, S, hS, hbc⟩ ↦ ⟨S, hS, b, hab, hbc⟩,
      fun ⟨S, hS, b, hab, hbc⟩ ↦ ⟨b, hab, S, hS, hbc⟩⟩
  sSup_mul_distrib 𝒮 S := ext_iff' fun a c ↦ by
    simp only [mul_iff, sSup_apply_iff, iSup_apply_iff, exists_prop]
    exact ⟨fun ⟨b, ⟨R, hR, hab⟩, hbc⟩ ↦ ⟨R, hR, b, hab, hbc⟩,
      fun ⟨R, hR, b, hab, hbc⟩ ↦ ⟨b, ⟨R, hR, hab⟩, hbc⟩⟩

/-- Finite relations form a complete Kleene algebra. -/
noncomputable instance instCompleteKleeneAlgebra : CompleteKleeneAlgebra (FinRel α α) where
  __ := instKleeneAlgebra
  __ := instCompleteLattice
  mul_sSup_distrib := IsQuantale.mul_sSup_distrib
  sSup_mul_distrib := IsQuantale.sSup_mul_distrib

/-- Finite relations on a finite type form a relation algebra, with converse the transpose. -/
instance instRelationAlgebra : RelationAlgebra (FinRel α α) where
  __ := instKleeneAlgebra
  __ := instBooleanAlgebra
  star := star
  star_involutive _ := rfl
  star_mul R S := ext_iff' fun a c ↦ by
    simp only [star_apply, mul_iff]
    exact ⟨fun ⟨b, h₁, h₂⟩ ↦ ⟨b, h₂, h₁⟩, fun ⟨b, h₁, h₂⟩ ↦ ⟨b, h₂, h₁⟩⟩
  star_add R S := rfl
  dedekind R S T := le_def.2 fun a c h ↦ by
    simp only [inf_apply, Bool.and_eq_true, mul_iff, star_apply] at h ⊢
    obtain ⟨⟨b, hab, hbc⟩, hac⟩ := h
    exact ⟨b, ⟨hab, c, hac, hbc⟩, hbc, a, hab, hac⟩

end CompleteHom

/-! ### Tests -/

/-- The sub-identity relation determined by a decidable predicate. -/
def ofPred [DecidableEq α] (p : α → Bool) : FinRel α α := fun a b ↦ decide (a = b) && p a

@[simp] theorem ofPred_apply [DecidableEq α] (p : α → Bool) (a b : α) :
    ofPred p a b = (decide (a = b) && p a) := rfl

/-- Finite relations form a Kleene algebra with tests, the tests being the decidable predicates
on `α`. -/
instance instKAT [DecidableEq α] [Fintype α] :
    KleeneAlgebraWithTests (α → Bool) (FinRel α α) where
  test := ofPred
  test_bot := ext fun a b ↦ by simp [Bot.bot]
  test_top := ext fun a b ↦ by simp [Top.top]
  test_sup p q := ext_iff' fun a b ↦ by
    simp only [ofPred_apply, add_apply, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
    change (a = b ∧ (p a || q a) = true) ↔ _
    simp only [Bool.or_eq_true]
    tauto
  test_inf p q := ext_iff' fun a b ↦ by
    simp only [ofPred_apply, mul_apply, Bool.and_eq_true, decide_eq_true_eq]
    change (a = b ∧ (p a && q a) = true) ↔ _
    simp only [Bool.and_eq_true]
    constructor
    · rintro ⟨rfl, hp, hq⟩
      exact ⟨a, ⟨rfl, hp⟩, rfl, hq⟩
    · rintro ⟨c, ⟨rfl, hp⟩, rfl, hq⟩
      exact ⟨rfl, hp, hq⟩

/-! ### Comparison with the reference model `SetRel`

`toSetRel` is an isomorphism of complete Kleene algebras onto `SetRel α α`, which validates the
computable definitions above against the reference model of `RelationAlgebra.Models.Rel`. -/

open scoped SetRel

/-- The relation on `α` denoted by a finite relation. -/
def toSetRel (R : FinRel α β) : SetRel α β := {p | R p.1 p.2}

@[simp] theorem mem_toSetRel {R : FinRel α β} {p : α × β} : p ∈ toSetRel R ↔ R p.1 p.2 := Iff.rfl

theorem toSetRel_injective : Function.Injective (toSetRel : FinRel α β → SetRel α β) := by
  intro R S h
  exact ext_iff' fun a b ↦ Iff.of_eq (congrArg (fun U : SetRel α β ↦ (a, b) ∈ U) h)

@[simp] theorem toSetRel_le_iff {R S : FinRel α β} : toSetRel R ≤ toSetRel S ↔ R ≤ S :=
  ⟨fun h ↦ le_def.2 fun a b hab ↦ @h (a, b) hab, fun h _ hp ↦ le_def.1 h _ _ hp⟩

@[simp] theorem toSetRel_zero : toSetRel (0 : FinRel α α) = 0 := by
  ext ⟨a, b⟩; simp

@[simp] theorem toSetRel_add (R S : FinRel α α) :
    toSetRel (R + S) = toSetRel R + toSetRel S := by
  ext ⟨a, b⟩; simp

@[simp] theorem toSetRel_one [DecidableEq α] : toSetRel (1 : FinRel α α) = 1 := by
  ext ⟨a, b⟩; simp [SetRel.one_def, SetRel.id]

@[simp] theorem toSetRel_mul [Fintype α] (R S : FinRel α α) :
    toSetRel (R * S) = toSetRel R * toSetRel S := by
  ext ⟨a, b⟩; simp [SetRel.mul_def]

theorem toSetRel_pow [DecidableEq α] [Fintype α] (R : FinRel α α) :
    ∀ n : ℕ, toSetRel (R ^ n) = toSetRel R ^ n
  | 0 => by rw [pow_zero, pow_zero, toSetRel_one]
  | n + 1 => by rw [pow_succ, pow_succ, toSetRel_mul, toSetRel_pow R n]

open scoped Classical in
/-- `toSetRel` is an order isomorphism onto the reference model. -/
noncomputable def orderIsoSetRel [DecidableEq α] [Fintype α] : FinRel α α ≃o SetRel α α where
  toFun := toSetRel
  invFun U := fun a b ↦ decide ((a, b) ∈ U)
  left_inv R := ext_iff' fun a b ↦ by simp
  right_inv U := Set.ext fun p ↦ by simp
  map_rel_iff' := toSetRel_le_iff

@[simp] theorem orderIsoSetRel_apply [DecidableEq α] [Fintype α] (R : FinRel α α) :
    orderIsoSetRel R = toSetRel R := rfl

/-- The computable star of `FinRel` really is the reflexive-transitive closure. -/
@[simp] theorem toSetRel_kstar [DecidableEq α] [Fintype α] (R : FinRel α α) :
    toSetRel (R∗) = (toSetRel R)∗ := by
  rw [CompleteKleeneAlgebra.kstar_eq_iSup_pow, SetRel.kstar_eq_iSup_pow]
  ext p
  simp only [mem_toSetRel, iSup_apply_iff, Set.iSup_eq_iUnion, Set.mem_iUnion]
  exact exists_congr fun n ↦ by rw [← toSetRel_pow R n]; exact Iff.rfl

/-- `R∗` relates `a` and `b` exactly when `b` is reachable from `a` by `R`-steps. -/
theorem kstar_iff [DecidableEq α] [Fintype α] (R : FinRel α α) (a b : α) :
    (R∗) a b ↔ Relation.ReflTransGen (fun x y ↦ R x y) a b := by
  have h : ((a, b) ∈ toSetRel (R∗)) = ((a, b) ∈ (toSetRel R)∗) := by rw [toSetRel_kstar]
  exact Iff.of_eq h

/-! ### A computable example

`succExample` is the successor relation on `Fin 4`.  Its transitive closure and inclusions
between finite relations are decided by `decide`, and evaluated by `#eval`. -/

set_option maxRecDepth 100000

/-- The successor relation on `Fin 4`, as a Boolean matrix. -/
def succExample : FinRel (Fin 4) (Fin 4) := fun a b ↦ decide (b.val = a.val + 1)

example : succExample 0 1 := by decide

example : ¬ succExample 0 2 := by decide

example : (succExample∗) 0 3 := by decide

example : ¬ (succExample∗) 3 0 := by decide

example : succExample ≤ succExample∗ := by decide

example : succExample∗ * succExample∗ = succExample∗ := by decide

end FinRel
