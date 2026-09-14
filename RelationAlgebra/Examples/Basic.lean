import RelationAlgebra.Kleene.Basic
import RelationAlgebra.KAT.Hoare
import RelationAlgebra.Models.Rel
import RelationAlgebra.Models.Bool
import Mathlib.Computability.Language

/-!
# Examples

A few sanity checks showing the library in use.
-/

open scoped Computability KAT

section Abstract

variable {T K : Type*} [BooleanAlgebra T] [KleeneAlgebra K] [KAT T K]

/-- Sliding, in any Kleene algebra. -/
example (a b : K) : a * (b * a)∗ = (a * b)∗ * a := KleeneAlgebra.mul_kstar_eq_kstar_mul a b

/-- Denesting, specialised to Mathlib's languages. -/
example {σ : Type*} (l m : Language σ) : (l + m)∗ = l∗ * (m * l∗)∗ := KleeneAlgebra.kstar_add l m

/-- `if b then p else q` is `if ¬b then q else p`. -/
example (b : T) (p q : K) : KAT.ifThenElse bᶜ p q = KAT.ifThenElse b q p :=
  KAT.ifThenElse_compl b p q

/-- The loop guard is false after a `while` loop. -/
example (b : T) (p : K) : KAT.HoareTriple ⊤ (KAT.whileDo b p) bᶜ :=
  KAT.HoareTriple.whileDo_exit b p

/-- A test placed before a loop whose body preserves it is still true afterwards. -/
example (b c : T) (p : K) (h : KAT.HoareTriple (b ⊓ c) p c) :
    KAT.HoareTriple c (KAT.whileDo b p) c :=
  (KAT.HoareTriple.whileDo h).weaken_post inf_le_right

end Abstract

section Relational

open scoped SetRel

/-- The successor relation on `ℕ`. -/
def succRel : SetRel ℕ ℕ := {p | p.2 = p.1 + 1}

/-- Its reflexive-transitive closure is `≤`. -/
example : succRel∗ = {p | p.1 ≤ p.2} := by
  ext ⟨a, b⟩
  simp only [SetRel.mem_kstar, Set.mem_setOf_eq]
  constructor
  · intro h
    induction h with
    | refl => exact le_rfl
    | tail _ hcd ih => exact ih.trans (by simp only [succRel, Set.mem_setOf_eq] at hcd; omega)
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | step _ ih => exact ih.tail rfl

/-- In the relational model, a Hoare triple says exactly what it should. -/
example {α : Type*} (s t : Set α) (R : SetRel α α) :
    KAT.HoareTriple s R t ↔ ∀ a b, a ∈ s → a ~[R] b → b ∈ t := by
  rw [KAT.hoareTriple_iff_le, SetRel.le_def, SetRel.test_def, SetRel.test_def, Set.subset_def]
  constructor
  · intro h a b ha hab
    obtain ⟨c, -, hcb, hc⟩ := h (a, b) ⟨a, ⟨rfl, ha⟩, hab⟩
    have hcb' : c = b := hcb
    have hc' : c ∈ t := hc
    exact hcb' ▸ hc'
  · rintro h ⟨a, b⟩ ⟨c, ⟨hac, ha⟩, hab⟩
    obtain rfl : a = c := hac
    exact ⟨b, hab, rfl, h _ _ ha hab⟩

end Relational
