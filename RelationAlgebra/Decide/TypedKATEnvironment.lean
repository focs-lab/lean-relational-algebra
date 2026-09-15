import RelationAlgebra.TypedKAT
import RelationAlgebra.Models.Bool

/-!
# Environments for typed KAT reflection

The reifier names objects by natural numbers. Actions carry their endpoints and values;
test environments are built one object at a time. All lookups at concrete indices reduce
definitionally, so reflection reconstructs proofs without casts between hom-sets.
-/

open CategoryTheory

universe u v w

/-- A Kleene category has the two trivial tests at every object. -/
instance Bool.instTypedKAT (C : Type u) [Category.{v} C] [KleeneCategory C] :
    TypedKAT C (fun _ ↦ Bool) where
  test b := cond b (𝟙 _) ⊥
  test_bot := rfl
  test_top := rfl
  test_sup a b := by cases a <;> cases b <;> simp
  test_inf a b := by cases a <;> cases b <;> simp

namespace TypedKAT.Reflection

variable {C : Type u} [Category.{v} C]

/-- One action in the reifier's environment, including its syntactic endpoints. -/
structure Action (obj : ℕ → C) where
  /-- Source object index. -/
  source : ℕ
  /-- Target object index. -/
  target : ℕ
  /-- The original morphism. -/
  value : obj source ⟶ obj target

variable (T : C → Type w) [∀ X, BooleanAlgebra (T X)] (d : C)

/-- The empty object environment uses true as the default test. -/
def nilTests : ∀ i : ℕ, ℕ → T (([] : List C).getD i d) := fun _ _ ↦ ⊤

/-- Extend a dependent test environment at the head of the object list. -/
def consTests (X : C) (xs : List C) (head : ℕ → T X)
    (tail : ∀ i, ℕ → T (xs.getD i d)) : ∀ i, ℕ → T ((X :: xs).getD i d)
  | 0 => head
  | i + 1 => tail i

end TypedKAT.Reflection
