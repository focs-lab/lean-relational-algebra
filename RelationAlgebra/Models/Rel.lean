import Mathlib.Data.Rel
import Mathlib.Data.Set.Lattice
import Mathlib.Logic.Relation
import Mathlib.Algebra.Order.Quantale
import RelationAlgebra.KAT.Defs

/-!
# The relational model

Binary relations on a type `α`, i.e. `SetRel α α = Set (α × α)`, form a Kleene algebra with
tests:

* `R + S = R ∪ S`, `0 = ∅`, `R ≤ S ↔ R ⊆ S` (the lattice structure of `Set`),
* `R * S = R ○ S` (relational composition, `SetRel.comp`), `1 = SetRel.id`,
* `R∗` is the reflexive-transitive closure `Relation.ReflTransGen`,
* tests are subsets `s : Set α`, embedded as the sub-identity relations
  `SetRel.ofSet s = {(a, a) | a ∈ s}`.

Since `SetRel α α` is reducibly `Set (α × α)`, and `Set` already carries (scoped, pointwise)
`+` and `*` instances in Mathlib, the ring-like instances here are **scoped**: write
`open scoped SetRel` to activate them.  All of Mathlib's `Set` and `SetRel` API remains
available, and `SetRel.mul_def`, `SetRel.add_def`, `SetRel.mem_kstar`, ... translate between
the two vocabularies.
-/

open scoped Computability

namespace SetRel

variable {α : Type*} {R S : SetRel α α} {a b : α}

/-- Binary relations compose: `R * S = R ○ S`. -/
scoped instance instMul : Mul (SetRel α α) := ⟨comp⟩
/-- The identity relation is the unit: `1 = SetRel.id`. -/
scoped instance instOne : One (SetRel α α) := ⟨SetRel.id⟩
/-- Addition of relations is union: `R + S = R ∪ S`. -/
scoped instance instAdd : Add (SetRel α α) := ⟨(· ∪ ·)⟩
/-- The empty relation is zero: `0 = ∅`. -/
scoped instance instZero : Zero (SetRel α α) := ⟨∅⟩
/-- The Kleene star of a relation is its reflexive-transitive closure. -/
scoped instance instKStar : KStar (SetRel α α) :=
  ⟨fun R ↦ {p | Relation.ReflTransGen (· ~[R] ·) p.1 p.2}⟩

theorem mul_def (R S : SetRel α α) : R * S = R ○ S := rfl
theorem add_def (R S : SetRel α α) : R + S = R ∪ S := rfl
theorem one_def : (1 : SetRel α α) = SetRel.id := rfl
theorem zero_def : (0 : SetRel α α) = ∅ := rfl
theorem kstar_def (R : SetRel α α) : R∗ = {p | Relation.ReflTransGen (· ~[R] ·) p.1 p.2} := rfl

@[simp] theorem mem_mul : a ~[R * S] b ↔ ∃ c, a ~[R] c ∧ c ~[S] b := Iff.rfl
@[simp] theorem mem_add : a ~[R + S] b ↔ a ~[R] b ∨ a ~[S] b := Iff.rfl
@[simp] theorem mem_one : a ~[(1 : SetRel α α)] b ↔ a = b := Iff.rfl
@[simp] theorem mem_zero : ¬ a ~[(0 : SetRel α α)] b := id
@[simp] theorem mem_kstar : a ~[R∗] b ↔ Relation.ReflTransGen (· ~[R] ·) a b := Iff.rfl

theorem comp_union (R S T : SetRel α α) : R ○ (S ∪ T) = (R ○ S) ∪ (R ○ T) := by
  ext ⟨a, c⟩
  simp only [mem_comp, Set.mem_union]
  constructor
  · rintro ⟨b, hab, hbc | hbc⟩
    · exact Or.inl ⟨b, hab, hbc⟩
    · exact Or.inr ⟨b, hab, hbc⟩
  · rintro (⟨b, hab, hbc⟩ | ⟨b, hab, hbc⟩)
    · exact ⟨b, hab, Or.inl hbc⟩
    · exact ⟨b, hab, Or.inr hbc⟩

theorem union_comp (R S T : SetRel α α) : (R ∪ S) ○ T = (R ○ T) ∪ (S ○ T) := by
  ext ⟨a, c⟩
  simp only [mem_comp, Set.mem_union]
  constructor
  · rintro ⟨b, hab | hab, hbc⟩
    · exact Or.inl ⟨b, hab, hbc⟩
    · exact Or.inr ⟨b, hab, hbc⟩
  · rintro (⟨b, hab, hbc⟩ | ⟨b, hab, hbc⟩)
    · exact ⟨b, Or.inl hab, hbc⟩
    · exact ⟨b, Or.inr hab, hbc⟩

/-- Relations on `α` form an idempotent semiring under union and composition. -/
scoped instance instIdemSemiring : IdemSemiring (SetRel α α) where
  add_assoc := Set.union_assoc
  zero_add := Set.empty_union
  add_zero := Set.union_empty
  add_comm := Set.union_comm
  nsmul := nsmulRec
  mul_assoc := comp_assoc
  one_mul := id_comp
  mul_one := comp_id
  npow := npowRec
  left_distrib := comp_union
  right_distrib := union_comp
  zero_mul := empty_comp
  mul_zero := comp_empty
  add_eq_sup _ _ := rfl

theorem le_def : R ≤ S ↔ R ⊆ S := Iff.rfl

/-- Relations on `α` form a quantale: composition distributes over arbitrary unions. -/
scoped instance instIsQuantale : IsQuantale (SetRel α α) where
  mul_sSup_distrib R 𝒮 := by
    simp only [mul_def, Set.sSup_eq_sUnion, Set.iSup_eq_iUnion]
    exact comp_sUnion R 𝒮
  sSup_mul_distrib 𝒮 S := by
    simp only [mul_def, Set.sSup_eq_sUnion, Set.iSup_eq_iUnion]
    exact sUnion_comp 𝒮 S

/-- Relations on `α` form a Kleene algebra, with `R∗` the reflexive-transitive closure. -/
scoped instance instKleeneAlgebra : KleeneAlgebra (SetRel α α) where
  one_le_kstar _ := by
    rintro ⟨a, b⟩ (h : a = b)
    subst h
    exact Relation.ReflTransGen.refl
  mul_kstar_le_kstar _ := by
    rintro ⟨a, c⟩ ⟨b, hab, hbc⟩
    exact Relation.ReflTransGen.head hab hbc
  kstar_mul_le_kstar _ := by
    rintro ⟨a, c⟩ ⟨b, hab, hbc⟩
    exact Relation.ReflTransGen.tail hab hbc
  mul_kstar_le_self R S h := by
    rintro ⟨a, c⟩ ⟨b, hab, hbc⟩
    replace hbc : Relation.ReflTransGen (· ~[R] ·) b c := hbc
    induction hbc with
    | refl => exact hab
    | tail _ hcd ih => exact h ⟨_, ih, hcd⟩
  kstar_mul_le_self R S h := by
    rintro ⟨a, c⟩ ⟨b, hab, hbc⟩
    replace hab : Relation.ReflTransGen (· ~[R] ·) a b := hab
    induction hab using Relation.ReflTransGen.head_induction_on with
    | refl => exact hbc
    | head hab' _ ih => exact h ⟨_, hab', ih⟩

@[simp] theorem mem_pow_zero : a ~[R ^ 0] b ↔ a = b := by rw [pow_zero, mem_one]

theorem mem_pow_succ {n : ℕ} : a ~[R ^ (n + 1)] b ↔ ∃ c, a ~[R] c ∧ c ~[R ^ n] b := by
  rw [pow_succ', mem_mul]

theorem mem_pow_succ' {n : ℕ} : a ~[R ^ (n + 1)] b ↔ ∃ c, a ~[R ^ n] c ∧ c ~[R] b := by
  rw [pow_succ, mem_mul]

/-- `R∗ = ⋃ n, R ^ n`: the relational model is star-continuous. -/
theorem kstar_eq_iUnion_pow (R : SetRel α α) : R∗ = ⋃ n : ℕ, R ^ n := by
  ext ⟨a, b⟩
  simp only [mem_kstar, Set.mem_iUnion]
  constructor
  · intro h
    induction h with
    | refl => exact ⟨0, rfl⟩
    | tail _ hcd ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, mem_pow_succ'.2 ⟨_, hn, hcd⟩⟩
  · rintro ⟨n, hn⟩
    induction n generalizing b with
    | zero => exact mem_pow_zero.1 hn ▸ Relation.ReflTransGen.refl
    | succ n ih =>
      obtain ⟨c, hac, hcb⟩ := mem_pow_succ'.1 hn
      exact (ih _ hac).tail hcb

theorem kstar_eq_iSup_pow (R : SetRel α α) : R∗ = ⨆ n : ℕ, R ^ n := kstar_eq_iUnion_pow R

/-! ### Tests: sub-identity relations -/

/-- The sub-identity relation `{(a, a) | a ∈ s}` associated with a set `s`. -/
def ofSet (s : Set α) : SetRel α α := {p | p.1 = p.2 ∧ p.1 ∈ s}

@[simp] theorem mem_ofSet {s : Set α} : a ~[ofSet s] b ↔ a = b ∧ a ∈ s := Iff.rfl

@[simp] theorem ofSet_empty : ofSet (∅ : Set α) = 0 := by ext ⟨a, b⟩; simp
@[simp] theorem ofSet_univ : ofSet (Set.univ : Set α) = 1 := by ext ⟨a, b⟩; simp
theorem ofSet_union (s t : Set α) : ofSet (s ∪ t) = ofSet s + ofSet t := by
  ext ⟨a, b⟩; simp; tauto
theorem ofSet_inter (s t : Set α) : ofSet (s ∩ t) = ofSet s * ofSet t := by
  ext ⟨a, b⟩; aesop

theorem ofSet_le_one (s : Set α) : ofSet s ≤ 1 := fun _ h ↦ h.1

theorem ofSet_injective : Function.Injective (ofSet : Set α → SetRel α α) := by
  intro s t h
  ext a
  have := congrArg (fun R : SetRel α α ↦ a ~[R] a) h
  simpa using this

/-- Relations on `α` form a Kleene algebra with tests, with tests the subsets of `α`. -/
scoped instance instKAT : KleeneAlgebraWithTests (Set α) (SetRel α α) where
  test := ofSet
  test_bot := ofSet_empty
  test_top := ofSet_univ
  test_sup := ofSet_union
  test_inf := ofSet_inter

theorem test_def (s : Set α) : (KAT.test s : SetRel α α) = ofSet s := rfl

end SetRel
