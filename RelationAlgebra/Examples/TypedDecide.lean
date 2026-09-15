import RelationAlgebra.Decide.KATTactic

/-!
# Using `kat` on typed goals

These regressions exercise categorical reification directly, including heterogeneous
composition, tests at different objects, proof reconstruction, and failure behaviour.
The minimal tactic import also checks that test-free goals get the trivial Boolean model.
-/

open CategoryTheory
open scoped Computability TypedKAT

universe u v w

namespace TypedKAT.TacticExamples

section KleeneCategory

variable {C : Type u} [Category.{v} C] [KleeneCategory C] {X Y Z : C}

/-- Sliding with different source and target objects, without a test-family assumption. -/
theorem sliding (p : X ⟶ Y) (q : Y ⟶ X) : p ≫ (q ≫ p)∗ = (p ≫ q)∗ ≫ p := by
  kat

example (p q : X ⟶ Y) (r : Y ⟶ Z) : (p ⊔ q) ≫ r = p ≫ r ⊔ q ≫ r := by kat

example (p : X ⟶ Y) : 𝟙 X ≫ p ≫ 𝟙 Y ⊔ ⊥ = p := by kat

example (p q : X ⟶ X) : (p ⊔ q)∗ = p∗ ≫ (q ≫ p∗)∗ := by kat 100

example (p : X ⟶ X) : 𝟙 X ⊔ p ≫ p∗ = p∗ := by kat

example : (⊥ : X ⟶ X)∗ = 𝟙 X := by kat

/-- Local definitions of objects are identified by definitional equality. -/
example (p : X ⟶ Y) (q : Y ⟶ X) :
    let X' := X
    let p' : X' ⟶ Y := p
    p' ≫ (q ≫ p')∗ = (p' ≫ q)∗ ≫ p' := by
  dsimp only
  kat

/-- Preprocessing can introduce binders before categorical reification. -/
example : ∀ (p : X ⟶ Y) (q : Y ⟶ X), p ≫ (q ≫ p)∗ = (p ≫ q)∗ ≫ p := by kat

set_option linter.style.multiGoal false in
/-- Closing the first goal during preprocessing must leave the second goal intact. -/
example (p : X ⟶ Y) : p = p ∧ True := by
  constructor
  kat
  trivial

set_option linter.style.multiGoal false in
/-- Closing the first goal by reflection must also leave the second goal intact. -/
example (p : X ⟶ Y) (q : Y ⟶ X) :
    p ≫ (q ≫ p)∗ = (p ≫ q)∗ ≫ p ∧ True := by
  constructor
  kat
  trivial

/-- Failure with insufficient fuel leaves the goal available for another attempt. -/
example (p : X ⟶ Y) (q : Y ⟶ X) : p ≫ (q ≫ p)∗ = (p ≫ q)∗ ≫ p := by
  fail_if_success kat 0
  kat 100

/-- Distinct actions and noncommuting compositions must remain distinct. -/
example (p q : X ⟶ X) : p = p ∧ q = q := by
  fail_if_success have : p = q := by kat
  fail_if_success have : p ≫ q = q ≫ p := by kat
  fail_if_success have : p∗ = p := by kat
  exact ⟨rfl, rfl⟩

end KleeneCategory

section Tests

variable {C : Type u} [Category.{v} C] [KleeneCategory C]
  {T : C → Type w} [∀ A, BooleanAlgebra (T A)] [TypedKAT C T] {X Y Z : C}

/-- Guards at different objects refine a heterogeneous action. -/
theorem guarded_le (p : X ⟶ Y) (b : T X) (c : T Y) : ⌞b⌟ ≫ p ≫ ⌞c⌟ ≤ p := by kat

/-- Source and target Boolean environments are independent. -/
theorem split_source_target (p : X ⟶ Y) (b : T X) (c : T Y) :
    ⌞b⌟ ≫ p ⊔ ⌞bᶜ⌟ ≫ p = p ≫ ⌞c⌟ ⊔ p ≫ ⌞cᶜ⌟ := by kat

example (p : X ⟶ Y) (q : Y ⟶ Z) (b : T Y) :
    p ≫ ⌞b⌟ ≫ q ⊔ p ≫ ⌞bᶜ⌟ ≫ q = p ≫ q := by kat

/-- Multiple primitive tests at one object need distinct indices. -/
example (b c : T X) : (⌞b ⊔ c⌟ : X ⟶ X) ≫ ⌞bᶜ⌟ = ⌞bᶜ ⊓ c⌟ := by kat

/-- With no actions, the default action environment still reconstructs the proof. -/
example (b : T X) : (⌞b⌟ : X ⟶ X) ≫ ⌞bᶜ⌟ = ⊥ := by kat

example (b c : T X) : (⌞b \ c⌟ : X ⟶ X) = ⌞b⌟ ≫ ⌞cᶜ⌟ := by kat

example (b c : T X) : (⌞b ⇨ c⌟ : X ⟶ X) ≫ ⌞b⌟ = ⌞b ⊓ c⌟ := by kat

example (b : T X) : (⌞b⌟ : X ⟶ X)∗ = 𝟙 X := by kat

example (p : X ⟶ Y) (b : T X) : TypedKAT.ifThenElse b p p = p := by kat

example (p : X ⟶ X) (b : T X) :
    TypedKAT.HoareTriple ⊤ (TypedKAT.whileDo b p) bᶜ := by kat

example (p : X ⟶ Y) (b : T X) : TypedKAT.HoareTriple b p ⊤ := by kat

example (p : X ⟶ Y) (q : Y ⟶ X) (b : T X) :
    TypedKAT.whileDo b (p ≫ q) =
      TypedKAT.ifThenElse b (p ≫ q ≫ TypedKAT.whileDo b (p ≫ q)) (𝟙 X) := by kat

/-- Identifying the objects must not identify distinct tests at that object. -/
example (p : X ⟶ X) (b c : T X) :
    ⌞b⌟ ≫ p ⊔ ⌞bᶜ⌟ ≫ p = p ≫ ⌞c⌟ ⊔ p ≫ ⌞cᶜ⌟ := by kat

/-- The reifier must not infer any relationship between independent tests. -/
example (p : X ⟶ Y) (b : T X) (c : T Y) (d : T X) :
    p = p ∧ b = b ∧ c = c ∧ d = d := by
  fail_if_success have : ⌞b⌟ ≫ p = p ≫ ⌞c⌟ := by kat
  fail_if_success have : (⌞b⌟ : X ⟶ X) = ⌞d⌟ := by kat
  exact ⟨rfl, rfl, rfl, rfl⟩

end Tests

/-- The category and all its instances can be introduced by the tactic itself. -/
example : ∀ (C : Type u) (_ : Category.{v} C) (_ : KleeneCategory C)
    (T : C → Type w) (_ : ∀ A, BooleanAlgebra (T A)) (_ : TypedKAT C T)
    (X : C) (b : T X), (⌞b⌟ : X ⟶ X) ≫ ⌞bᶜ⌟ = ⊥ := by kat

/-! Concrete hom-set implementations must retain their categorical interpretation. -/

private def numbers : RelCat := ℕ
private def booleans : RelCat := Bool

example (p : numbers ⟶ booleans) (q : booleans ⟶ numbers) :
    p ≫ (q ≫ p)∗ = (p ≫ q)∗ ≫ p := by kat

example (p : numbers ⟶ booleans) (b : Set numbers) (c : Set booleans) :
    (⌞b⌟ : numbers ⟶ numbers) ≫ p ≫ ⌞c⌟ ≤ p := by kat

/-- An atom can be a concrete relation constructor rather than a variable of hom type. -/
example (r : SetRel numbers booleans) (b : Set numbers) :
    (⌞b⌟ : numbers ⟶ numbers) ≫ RelCat.Hom.ofRel r ⊔
      ⌞bᶜ⌟ ≫ RelCat.Hom.ofRel r = RelCat.Hom.ofRel r := by kat

/-! Existing untyped uses on `End` retain their reversed multiplication convention. -/

example {C : Type u} [Category.{v} C] [KleeneCategory C] {X : C} (p q : End X) :
    (p + q)∗ = p∗ * (q * p∗)∗ := by kat

end TypedKAT.TacticExamples
