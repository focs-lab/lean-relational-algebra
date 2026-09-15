import Mathlib.Data.Setoid.Basic
import RelationAlgebra.Converse
import RelationAlgebra.Kleene.Complete
import RelationAlgebra.Kleene.Quantale
import RelationAlgebra.Models.Rel

/-!
# The model of relations on a setoid

This is the Lean counterpart of `theories/srel.v` in Damien Pous' Rocq library
[relation-algebra](https://github.com/damien-pous/relation-algebra), to whom this model is due.

A `SetoidRel α`, for `[Setoid α]`, is a binary relation on `α` that is *invariant* under the
setoid equivalence `≈`.  We package it as a structure bundling the relation together with its
invariance proof, rather than as a subtype of `SetRel α α`: the structure gives `R.rel a b`
directly as a `Prop` (no `(a, b) ∈ ↑R` coercions) while the invariance proof stays available
under the name `SetoidRel.respects`, which is exactly how `srel.v` presents the model.

The essential point, as upstream, is that **the identity is the setoid equivalence** `≈`, not
`Eq`, and that the Kleene star is computed accordingly: `R∗` is the reflexive-transitive closure
of `R ⊔ (· ≈ ·)` (`SetoidRel.rel_kstar`).  So this is *not* a sub-Kleene-algebra of `SetRel α α`,
even though it is a sublattice of it.

## Main results

* `SetoidRel.instCompleteLattice`, `SetoidRel.instBooleanAlgebra`: invariant relations are closed
  under arbitrary unions and intersections and under complement, so they form a complete Boolean
  algebra.  (In particular the complement of an invariant relation *is* invariant, so nothing
  forces us to weaken the Boolean structure.)
* `SetoidRel.instMonoid`, `SetoidRel.instIsQuantale`: composition with unit `≈`; hence
  `SetoidRel.instKleeneAlgebra`, obtained from `KleeneAlgebra.ofQuantale` (which builds its
  `IdemSemiring` part with `IdemSemiring.ofQuantale`), and `SetoidRel.instCompleteKleeneAlgebra`.
* `SetoidRel.instRelationAlgebra`: converse (Mathlib's `star`) and the Dedekind law.
* `SetoidRel.instKAT`: tests are the `≈`-invariant subsets of `α`, presented as
  `Set (Quotient s)` (`SetoidRel.invariant_iff_exists_preimage`).
* `SetoidRel.rel_kstar`: the characterisation of the star.
* `SetoidRel.discreteOrderIso`: for the discrete setoid, this model is isomorphic — as an ordered
  Kleene algebra — to the plain relational model `SetRel α α`.

## References

* [D. Pous, *Relation Algebra and KAT in Coq*, file `theories/srel.v`,
  <https://github.com/damien-pous/relation-algebra>]
-/

open scoped Computability

/-- A relation on a setoid, required to be invariant under the setoid equivalence. -/
structure SetoidRel (α : Type*) [Setoid α] where
  /-- The underlying binary relation. -/
  rel : α → α → Prop
  /-- Invariance under the setoid equivalence. -/
  respects : ∀ {a a' b b' : α}, a ≈ a' → b ≈ b' → rel a b → rel a' b'

namespace SetoidRel

variable {α : Type*} [s : Setoid α] {R S T : SetoidRel α} {a b c : α}

@[ext]
theorem ext (h : ∀ a b, R.rel a b ↔ S.rel a b) : R = S := by
  have hrel : R.rel = S.rel := funext fun a ↦ funext fun b ↦ propext (h a b)
  cases R
  cases S
  subst hrel
  rfl

/-! ### The complete Boolean algebra structure

Invariant relations are closed under all the Boolean and infinitary operations, so they form a
complete sublattice of `SetRel α α`. -/

/-- Invariant relations on a setoid form a complete lattice, with the pointwise order. -/
instance instCompleteLattice : CompleteLattice (SetoidRel α) where
  le R S := ∀ a b, R.rel a b → S.rel a b
  le_refl _ _ _ h := h
  le_trans _ _ _ hRS hST a b h := hST a b (hRS a b h)
  le_antisymm _ _ hRS hSR := ext fun a b ↦ ⟨hRS a b, hSR a b⟩
  sup R S := ⟨fun a b ↦ R.rel a b ∨ S.rel a b,
    fun h₁ h₂ h ↦ h.imp (R.respects h₁ h₂) (S.respects h₁ h₂)⟩
  le_sup_left _ _ _ _ h := Or.inl h
  le_sup_right _ _ _ _ h := Or.inr h
  sup_le _ _ _ hRT hST a b h := h.elim (hRT a b) (hST a b)
  inf R S := ⟨fun a b ↦ R.rel a b ∧ S.rel a b,
    fun h₁ h₂ h ↦ ⟨R.respects h₁ h₂ h.1, S.respects h₁ h₂ h.2⟩⟩
  inf_le_left _ _ _ _ h := h.1
  inf_le_right _ _ _ _ h := h.2
  le_inf _ _ _ hRS hRT a b h := ⟨hRS a b h, hRT a b h⟩
  sSup 𝒮 := ⟨fun a b ↦ ∃ R ∈ 𝒮, R.rel a b,
    fun h₁ h₂ h ↦ h.imp fun R hR ↦ ⟨hR.1, R.respects h₁ h₂ hR.2⟩⟩
  isLUB_sSup _ := ⟨fun R hR a b h ↦ ⟨R, hR, h⟩,
    fun _ hR a b h ↦ hR h.choose_spec.1 a b h.choose_spec.2⟩
  sInf 𝒮 := ⟨fun a b ↦ ∀ R ∈ 𝒮, R.rel a b,
    fun h₁ h₂ h R hR ↦ R.respects h₁ h₂ (h R hR)⟩
  isGLB_sInf _ := ⟨fun R hR a b h ↦ h R hR, fun _ hR a b h R hR' ↦ hR hR' a b h⟩
  top := ⟨fun _ _ ↦ True, fun _ _ _ ↦ trivial⟩
  bot := ⟨fun _ _ ↦ False, fun _ _ h ↦ h⟩
  le_top _ _ _ _ := trivial
  bot_le _ _ _ h := h.elim

theorem le_def : R ≤ S ↔ ∀ a b, R.rel a b → S.rel a b := Iff.rfl

@[simp] theorem rel_sup : (R ⊔ S).rel a b ↔ R.rel a b ∨ S.rel a b := Iff.rfl
@[simp] theorem rel_inf : (R ⊓ S).rel a b ↔ R.rel a b ∧ S.rel a b := Iff.rfl
@[simp] theorem rel_top : (⊤ : SetoidRel α).rel a b := trivial
@[simp] theorem rel_bot : ¬ (⊥ : SetoidRel α).rel a b := id

@[simp] theorem rel_sSup {𝒮 : Set (SetoidRel α)} : (sSup 𝒮).rel a b ↔ ∃ R ∈ 𝒮, R.rel a b :=
  Iff.rfl

@[simp] theorem rel_sInf {𝒮 : Set (SetoidRel α)} : (sInf 𝒮).rel a b ↔ ∀ R ∈ 𝒮, R.rel a b :=
  Iff.rfl

@[simp] theorem rel_iSup {ι : Sort*} {f : ι → SetoidRel α} :
    (⨆ i, f i).rel a b ↔ ∃ i, (f i).rel a b := by
  simp only [iSup, rel_sSup, Set.mem_range, exists_exists_eq_and]

/-- Invariant relations on a setoid form a Boolean algebra: the complement of an invariant
relation is invariant. -/
instance instBooleanAlgebra : BooleanAlgebra (SetoidRel α) where
  __ := instCompleteLattice
  compl R := ⟨fun a b ↦ ¬ R.rel a b,
    fun h₁ h₂ h hr ↦ h (R.respects (Setoid.symm h₁) (Setoid.symm h₂) hr)⟩
  le_sup_inf _ _ _ _ _ h := by simp only [rel_inf, rel_sup] at h ⊢; tauto
  inf_compl_le_bot _ _ _ h := h.2 h.1
  top_le_sup_compl R a b _ := Classical.em (R.rel a b)

@[simp] theorem rel_compl : (Rᶜ).rel a b ↔ ¬ R.rel a b := Iff.rfl

/-! ### The monoid structure: composition, with the setoid equivalence as unit -/

/-- The identity of this model is the setoid equivalence, not `Eq`. -/
instance instOne : One (SetoidRel α) :=
  ⟨⟨(· ≈ ·), fun h₁ h₂ h ↦ Setoid.trans (Setoid.symm h₁) (Setoid.trans h h₂)⟩⟩

/-- Composition of invariant relations. -/
instance instMul : Mul (SetoidRel α) :=
  ⟨fun R S ↦ ⟨fun a c ↦ ∃ b, R.rel a b ∧ S.rel b c, fun h₁ h₂ h ↦
    h.imp fun b hb ↦ ⟨R.respects h₁ (Setoid.refl b) hb.1, S.respects (Setoid.refl b) h₂ hb.2⟩⟩⟩

@[simp] theorem rel_one : (1 : SetoidRel α).rel a b ↔ a ≈ b := Iff.rfl
@[simp] theorem rel_mul : (R * S).rel a c ↔ ∃ b, R.rel a b ∧ S.rel b c := Iff.rfl

/-- Composition is associative and has the setoid equivalence as unit. -/
instance instMonoid : Monoid (SetoidRel α) where
  mul_assoc R S T := by
    ext a d
    simp only [rel_mul]
    constructor
    · rintro ⟨c, ⟨b, hab, hbc⟩, hcd⟩
      exact ⟨b, hab, c, hbc, hcd⟩
    · rintro ⟨b, hab, c, hbc, hcd⟩
      exact ⟨c, ⟨b, hab, hbc⟩, hcd⟩
  one_mul R := by
    ext a b
    simp only [rel_mul, rel_one]
    exact ⟨fun ⟨c, hac, hcb⟩ ↦ R.respects (Setoid.symm hac) (Setoid.refl b) hcb,
      fun h ↦ ⟨a, Setoid.refl a, h⟩⟩
  mul_one R := by
    ext a b
    simp only [rel_mul, rel_one]
    exact ⟨fun ⟨c, hac, hcb⟩ ↦ R.respects (Setoid.refl a) hcb hac,
      fun h ↦ ⟨b, h, Setoid.refl b⟩⟩
  npow := npowRec

/-- Composition distributes over arbitrary unions. -/
instance instIsQuantale : IsQuantale (SetoidRel α) where
  mul_sSup_distrib R 𝒮 := by
    ext a c
    simp only [rel_mul, rel_sSup, rel_iSup, exists_prop]
    constructor
    · rintro ⟨b, hab, S, hS, hbc⟩
      exact ⟨S, hS, b, hab, hbc⟩
    · rintro ⟨S, hS, b, hab, hbc⟩
      exact ⟨b, hab, S, hS, hbc⟩
  sSup_mul_distrib 𝒮 S := by
    ext a c
    simp only [rel_mul, rel_sSup, rel_iSup, exists_prop]
    constructor
    · rintro ⟨b, ⟨R, hR, hab⟩, hbc⟩
      exact ⟨R, hR, b, hab, hbc⟩
    · rintro ⟨R, hR, b, hab, hbc⟩
      exact ⟨b, ⟨R, hR, hab⟩, hbc⟩

/-- Invariant relations form a Kleene algebra, via the generic quantale construction. -/
instance instKleeneAlgebra : KleeneAlgebra (SetoidRel α) := KleeneAlgebra.ofQuantale _

/-- Invariant relations form a complete Kleene algebra. -/
instance instCompleteKleeneAlgebra : CompleteKleeneAlgebra (SetoidRel α) where
  __ := instKleeneAlgebra
  __ := instCompleteLattice
  mul_sSup_distrib := IsQuantale.mul_sSup_distrib
  sSup_mul_distrib := IsQuantale.sSup_mul_distrib

@[simp] theorem rel_add : (R + S).rel a b ↔ R.rel a b ∨ S.rel a b := Iff.rfl
@[simp] theorem rel_zero : ¬ (0 : SetoidRel α).rel a b := id

/-! ### The Kleene star -/

@[simp] theorem rel_pow_zero : (R ^ 0).rel a b ↔ a ≈ b := by rw [pow_zero]; exact Iff.rfl

theorem rel_pow_succ {n : ℕ} : (R ^ (n + 1)).rel a b ↔ ∃ c, (R ^ n).rel a c ∧ R.rel c b := by
  rw [pow_succ]; exact Iff.rfl

theorem rel_kstar_iff_exists_pow : (R∗).rel a b ↔ ∃ n : ℕ, (R ^ n).rel a b := by
  rw [CompleteKleeneAlgebra.kstar_eq_iSup_pow, rel_iSup]

/-- The star of `R` is the reflexive-transitive closure of `R` joined with the setoid
equivalence.  This is the point at which the model differs from `SetRel α α`. -/
theorem rel_kstar :
    (R∗).rel a b ↔ Relation.ReflTransGen (fun x y ↦ x ≈ y ∨ R.rel x y) a b := by
  rw [rel_kstar_iff_exists_pow]
  constructor
  · rintro ⟨n, hn⟩
    induction n generalizing b with
    | zero => exact Relation.ReflTransGen.single (Or.inl (rel_pow_zero.1 hn))
    | succ n ih =>
      obtain ⟨c, hac, hcb⟩ := rel_pow_succ.1 hn
      exact (ih hac).tail (Or.inr hcb)
  · intro h
    induction h with
    | refl => exact ⟨0, rel_pow_zero.2 (Setoid.refl a)⟩
    | tail _ hstep ih =>
      obtain ⟨n, hn⟩ := ih
      rcases hstep with hstep | hstep
      · exact ⟨n, (R ^ n).respects (Setoid.refl a) hstep hn⟩
      · exact ⟨n + 1, rel_pow_succ.2 ⟨_, hn, hstep⟩⟩

/-! ### Converse and the relation algebra structure -/

/-- Converse of an invariant relation. -/
instance instStar : Star (SetoidRel α) :=
  ⟨fun R ↦ ⟨fun a b ↦ R.rel b a, fun h₁ h₂ h ↦ R.respects h₂ h₁ h⟩⟩

@[simp] theorem rel_star : (star R).rel a b ↔ R.rel b a := Iff.rfl

/-- Invariant relations on a setoid form a relation algebra. -/
instance instRelationAlgebra : RelationAlgebra (SetoidRel α) where
  __ := instKleeneAlgebra
  __ := instBooleanAlgebra
  star := star
  star_involutive _ := by ext a b; simp only [rel_star]
  star_mul R S := by
    ext a c
    simp only [rel_star, rel_mul]
    exact ⟨fun ⟨b, hb₁, hb₂⟩ ↦ ⟨b, hb₂, hb₁⟩, fun ⟨b, hb₁, hb₂⟩ ↦ ⟨b, hb₂, hb₁⟩⟩
  star_add R S := by ext a b; simp only [rel_star, rel_add]
  dedekind R S T := by
    intro a c h
    obtain ⟨⟨b, hab, hbc⟩, hac⟩ := h
    exact ⟨b, ⟨hab, c, hac, hbc⟩, hbc, a, hab, hac⟩

/-! ### Tests

The tests of this KAT are the `≈`-invariant subsets of `α`.  We present them as subsets of the
quotient, `Set (Quotient s)`, which is literally the same thing
(`SetoidRel.invariant_iff_exists_preimage`) and is already a Boolean algebra in Mathlib. -/

/-- A subset of `α` is invariant under `≈` exactly when it is the preimage of a subset of the
quotient; this is why we may take `Set (Quotient s)` as the Boolean algebra of tests. -/
theorem invariant_iff_exists_preimage (t : Set α) :
    (∀ ⦃x y : α⦄, x ≈ y → x ∈ t → y ∈ t) ↔ ∃ P : Set (Quotient s), t = Quotient.mk s ⁻¹' P := by
  constructor
  · intro h
    refine ⟨Quotient.mk s '' t, Set.ext fun x ↦ ⟨fun hx ↦ ⟨x, hx, rfl⟩, ?_⟩⟩
    rintro ⟨y, hy, hxy⟩
    exact h (Quotient.exact hxy) hy
  · rintro ⟨P, rfl⟩ x y hxy hx
    simpa only [Set.mem_preimage, Quotient.sound hxy] using hx

/-- The sub-identity relation determined by an invariant subset of `α`, given as a subset of the
quotient. -/
def ofSet (P : Set (Quotient s)) : SetoidRel α :=
  ⟨fun a b ↦ a ≈ b ∧ ⟦a⟧ ∈ P, fun h₁ h₂ h ↦
    ⟨Setoid.trans (Setoid.symm h₁) (Setoid.trans h.1 h₂),
      by simpa only [Quotient.sound h₁] using h.2⟩⟩

@[simp] theorem rel_ofSet {P : Set (Quotient s)} : (ofSet P).rel a b ↔ a ≈ b ∧ ⟦a⟧ ∈ P := Iff.rfl

theorem ofSet_le_one (P : Set (Quotient s)) : ofSet P ≤ 1 := fun _ _ h ↦ h.1

/-- Invariant relations form a Kleene algebra with tests, the tests being the invariant subsets
of `α`, i.e. the subsets of the quotient. -/
instance instKAT : KleeneAlgebraWithTests (Set (Quotient s)) (SetoidRel α) where
  test := ofSet
  test_bot := by
    ext a b
    simp only [rel_ofSet, Set.bot_eq_empty, Set.mem_empty_iff_false, and_false, false_iff]
    exact rel_zero
  test_top := by ext a b; simp only [rel_ofSet, rel_one, Set.top_eq_univ, Set.mem_univ, and_true]
  test_sup P Q := by
    ext a b
    simp only [rel_ofSet, rel_add, Set.sup_eq_union, Set.mem_union]
    tauto
  test_inf P Q := by
    ext a b
    simp only [rel_ofSet, rel_mul, Set.inf_eq_inter, Set.mem_inter_iff]
    constructor
    · rintro ⟨hab, hP, hQ⟩
      exact ⟨a, ⟨Setoid.refl a, hP⟩, hab, hQ⟩
    · rintro ⟨c, ⟨hac, hP⟩, hcb, hQ⟩
      exact ⟨Setoid.trans hac hcb, hP, by simpa only [Quotient.sound hac] using hQ⟩

/-! ### Sanity checks -/

example (R : SetoidRel α) : (R∗)∗ = R∗ := kstar_idem R

example (R S : SetoidRel α) : star (R * S) = star S * star R := RelationAlgebra.star_mul R S

/-- The unit of this model is the setoid equivalence: it relates distinct equivalent points. -/
example (h : a ≈ b) : (1 : SetoidRel α).rel a b := h

/-! ### Comparison with the plain relational model

Forgetting invariance gives a map to `SetRel α α`.  It preserves the lattice structure and
composition, but *not* the unit or the star — unless the setoid is discrete, in which case it is
an isomorphism of complete Kleene algebras. -/

open scoped SetRel

/-- The underlying plain relation of an invariant relation. -/
def toSetRel (R : SetoidRel α) : SetRel α α := {p | R.rel p.1 p.2}

@[simp] theorem mem_toSetRel {p : α × α} : p ∈ toSetRel R ↔ R.rel p.1 p.2 := Iff.rfl

theorem toSetRel_injective : Function.Injective (toSetRel : SetoidRel α → SetRel α α) :=
  fun _ _ h ↦ ext fun a b ↦ by
    exact Iff.of_eq (congrArg (fun U : SetRel α α ↦ (a, b) ∈ U) h)

@[simp] theorem toSetRel_le_iff : toSetRel R ≤ toSetRel S ↔ R ≤ S :=
  ⟨fun h a b hab ↦ @h (a, b) hab, fun h _ hp ↦ h _ _ hp⟩

@[simp] theorem toSetRel_zero : toSetRel (0 : SetoidRel α) = 0 := rfl

@[simp] theorem toSetRel_add (R S : SetoidRel α) :
    toSetRel (R + S) = toSetRel R + toSetRel S := rfl

@[simp] theorem toSetRel_mul (R S : SetoidRel α) :
    toSetRel (R * S) = toSetRel R * toSetRel S := rfl

theorem toSetRel_one : toSetRel (1 : SetoidRel α) = {p : α × α | p.1 ≈ p.2} := rfl

end SetoidRel

/-! ### Recovering the plain relational model

For the *discrete* setoid, whose equivalence is `Eq`, `toSetRel` is an isomorphism of complete
Kleene algebras onto `SetRel α α`. -/

section Discrete

open scoped SetRel

variable (β : Type*)

/-- The discrete setoid on `β`: its equivalence is equality. -/
@[reducible] def discreteSetoid : Setoid β := ⟨Eq, eq_equivalence⟩

attribute [local instance] discreteSetoid

namespace SetoidRel

/-- For the discrete setoid, invariant relations are exactly the relations on `β`: `toSetRel` is
an order isomorphism onto `SetRel β β`. -/
def discreteOrderIso : SetoidRel β ≃o SetRel β β where
  toFun := toSetRel
  invFun U := ⟨fun a b ↦ (a, b) ∈ U, by
    intro a a' b b' h₁ h₂ h
    have e₁ : a = a' := h₁
    have e₂ : b = b' := h₂
    exact e₁ ▸ e₂ ▸ h⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := toSetRel_le_iff

variable {β}

@[simp] theorem discreteOrderIso_apply (R : SetoidRel β) :
    discreteOrderIso β R = toSetRel R := rfl

/-- For the discrete setoid the unit is the identity relation, as in `SetRel β β`. -/
@[simp] theorem toSetRel_discrete_one : toSetRel (1 : SetoidRel β) = 1 := rfl

theorem toSetRel_pow (R : SetoidRel β) : ∀ n : ℕ, toSetRel (R ^ n) = toSetRel R ^ n
  | 0 => by rw [pow_zero, pow_zero, toSetRel_discrete_one]
  | n + 1 => by rw [pow_succ, pow_succ, toSetRel_mul, toSetRel_pow R n]

/-- For the discrete setoid the star agrees with the star of `SetRel β β`. -/
@[simp] theorem toSetRel_discrete_kstar (R : SetoidRel β) : toSetRel (R∗) = (toSetRel R)∗ := by
  rw [CompleteKleeneAlgebra.kstar_eq_iSup_pow, CompleteKleeneAlgebra.kstar_eq_iSup_pow]
  ext p
  simp only [mem_toSetRel, rel_iSup, Set.iSup_eq_iUnion, Set.mem_iUnion]
  exact exists_congr fun n ↦ by rw [← toSetRel_pow R n]; exact Iff.rfl

end SetoidRel

end Discrete
