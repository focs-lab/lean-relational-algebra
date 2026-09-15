import RelationAlgebra.Decide.HKATTactic

/-!
# Using `hkat` with heterogeneous hypotheses

These examples test the public tactic with a minimal import. They cover hypotheses at
several objects, iteration, Boolean conversions, rewriting, and failed proof attempts.
-/

open CategoryTheory
open scoped Computability TypedKAT

universe u v w

namespace TypedKAT.HypothesisExamples

section WithoutTests

variable {C : Type u} [Category.{v} C] [KleeneCategory C] {W X Y Z : C}

/-- Zero morphisms can be used inside contexts with different endpoints. -/
theorem zero_context (p : W ⟶ X) (q : X ⟶ Y) (r : Y ⟶ Z) (h : q = ⊥) :
    p ≫ q ≫ r = ⊥ := by hkat

example (p : X ⟶ Y) (q : Y ⟶ Z) (h : p ≤ ⊥) : p ≫ q ≤ ⊥ := by hkat

/-- A zero cycle has identity star, including when its edges change objects. -/
theorem zero_cycle (p : X ⟶ Y) (q : Y ⟶ X) (h : p ≫ q = ⊥) :
    (p ≫ q)∗ = 𝟙 X := by hkat

/-- Paths may go around several cycles before reaching the zero hypothesis. -/
example (p : X ⟶ Y) (q : Y ⟶ X) (r : Y ⟶ Z) (s : Z ⟶ Y)
    (h : q ≫ p = ⊥) : p ≫ (r ≫ s ⊔ q ≫ p)∗ ≫ r = p ≫ (r ≫ s)∗ ≫ r := by
  hkat

/-- Several hypotheses in distinct hom-sets contribute to one proof. -/
example (p : X ⟶ Y) (q : Y ⟶ Z) (r : X ⟶ Z) (hp : p ≤ ⊥) (hq : q ≤ ⊥) :
    p ≫ q ⊔ r = r := by hkat

/-- A disconnected hypothesis is irrelevant, even if it has the same syntactic shape. -/
example (p : X ⟶ Y) (q : W ⟶ Z) (_h : q = ⊥) : p = p := by
  fail_if_success have : p = ⊥ := by hkat
  rfl

/-- Arbitrary equations between actions are outside the supported conversion rules. -/
example (p q : X ⟶ Y) (_h : p = q) : p = p := by
  fail_if_success have : p ≫ 𝟙 Y = q := by hkat
  rfl

/-- Insufficient fuel must fail without changing the goal. -/
example (p : X ⟶ Y) (q : Y ⟶ X) (h : p ≫ q = ⊥) : (p ≫ q)∗ = 𝟙 X := by
  fail_if_success hkat 0
  hkat 10000

/-- Unsupported hypotheses do not prevent use of a supported one. -/
example (p : X ⟶ Y) (q : Y ⟶ Z) (h : p = ⊥) (n : ℕ) (_hn : n ≤ n + 1) :
    p ≫ q = ⊥ := by hkat

set_option linter.style.multiGoal false in
/-- Preprocessing closes only the original goal. -/
example (p : X ⟶ Y) : p = p ∧ True := by
  constructor
  hkat
  trivial

set_option linter.style.multiGoal false in
/-- Hypothesis elimination also leaves unrelated goals available. -/
example (p : X ⟶ Y) (q : Y ⟶ Z) (h : p = ⊥) : p ≫ q = ⊥ ∧ True := by
  constructor
  hkat
  trivial

/-- The minimal import supplies the trivial Boolean family for typed test-free goals. -/
example : ∀ (p : X ⟶ Y) (q : Y ⟶ Z), p = ⊥ → p ≫ q = ⊥ := by hkat

end WithoutTests

section WithTests

variable {C : Type u} [Category.{v} C] [KleeneCategory C]
  {T : C → Type w} [∀ A, BooleanAlgebra (T A)] [TypedKAT C T] {X Y Z : C}

/-- Hoare sequencing genuinely uses hypotheses at different objects. -/
theorem sequence (p : X ⟶ Y) (q : Y ⟶ Z) (b : T X) (c : T Y) (d : T Z)
    (hp : TypedKAT.HoareTriple b p c) (hq : TypedKAT.HoareTriple c q d) :
    TypedKAT.HoareTriple b (p ≫ q) d := by
  fail_if_success kat
  hkat

/-- A round trip between different objects preserves the source invariant. -/
theorem iterate_round_trip (p : X ⟶ Y) (q : Y ⟶ X) (b : T X) (c : T Y)
    (hp : TypedKAT.HoareTriple b p c) (hq : TypedKAT.HoareTriple c q b) :
    TypedKAT.HoareTriple b (p ≫ q)∗ b := by hkat 10000

example (p : X ⟶ X) (b : T X) (h : TypedKAT.HoareTriple b p b) :
    TypedKAT.HoareTriple b p∗ b := by hkat

/-- Guarded inequalities and equalities have the same conversions as untyped `hkat`. -/
example (p : X ⟶ Y) (b : T X) (c : T Y) (h : ⌞b⌟ ≫ p ≤ p ≫ ⌞c⌟) :
    TypedKAT.HoareTriple b p c := by hkat

example (p : X ⟶ Y) (b : T X) (c : T Y) (h : ⌞b⌟ ≫ p = p ≫ ⌞c⌟) :
    TypedKAT.HoareTriple b p c := by hkat

example (p q : X ⟶ Y) (b : T Y) (c : T X) (h : p ≫ ⌞b⌟ ≤ ⌞c⌟ ≫ q) :
    ⌞cᶜ⌟ ≫ p ≫ ⌞b⌟ = ⊥ := by hkat

example (p q : X ⟶ Y) (c : T Y) (h : q ≤ p ≫ ⌞c⌟) : q ≫ ⌞cᶜ⌟ = ⊥ := by hkat

example (p q : X ⟶ Y) (b : T X) (h : q ≤ ⌞b⌟ ≫ p) : ⌞bᶜ⌟ ≫ q = ⊥ := by hkat

example (p : X ⟶ Y) (b c : T X) (h : b ≤ c) : ⌞b⌟ ≫ p ≤ ⌞c⌟ ≫ p := by hkat

example (p : X ⟶ Y) (b c : T Y) (h : b = c) : p ≫ ⌞b⌟ = p ≫ ⌞c⌟ := by hkat

/-- Boolean hypotheses at an intermediate object must be discovered too. -/
example (p : X ⟶ Y) (q : Y ⟶ Z) (b c : T Y) (h : b ≤ c) :
    p ≫ ⌞b⌟ ≫ q ≤ p ≫ ⌞c⌟ ≫ q := by hkat

/-- Normalize Boolean difference and implication in hypotheses as well as the goal. -/
example (p : X ⟶ Y) (b c : T X) (d : T Y)
    (h : TypedKAT.HoareTriple (b \ c) p d) :
    TypedKAT.HoareTriple (b ⊓ cᶜ) p d := by hkat

example (p : X ⟶ Y) (b c : T X) (h : b ⇨ c = ⊤) :
    ⌞b⌟ ≫ p ≤ ⌞c⌟ ≫ p := by hkat

/-- Conditionals in hypotheses are unfolded before collecting their action graph. -/
example (p : X ⟶ Y) (q : Y ⟶ Z) (b : T X) (c : T Y) (d : T Z)
    (hp : TypedKAT.HoareTriple b (TypedKAT.ifThenElse b p p) c)
    (hq : TypedKAT.HoareTriple c q d) : TypedKAT.HoareTriple b (p ≫ q) d := by hkat

/-- Loop invariants can be supplied as ordinary hypotheses. -/
example (p : X ⟶ X) (b i : T X) (h : TypedKAT.HoareTriple (i ⊓ b) p i) :
    TypedKAT.HoareTriple i (TypedKAT.whileDo b p) (i ⊓ bᶜ) := by hkat

/-- Both special endomorphism rewrites remain usable inside heterogeneous contexts. -/
example (p : X ⟶ X) (q : X ⟶ Y) (b : T X) (h : ⌞b⌟ ≫ p = ⌞b⌟) :
    ⌞b⌟ ≫ p ≫ q = ⌞b⌟ ≫ q := by hkat

example (p : Y ⟶ Y) (q : X ⟶ Y) (b : T Y) (h : p ≫ ⌞b⌟ = ⌞b⌟) :
    q ≫ ⌞bᶜ⌟ ≫ p ≫ ⌞b⌟ = ⊥ := by hkat

/-- Tests at distinct objects must not become interchangeable. -/
example (p : X ⟶ Y) (b : T X) (c : T Y) (_h : b = ⊥) : p = p ∧ c = c := by
  fail_if_success have : p ≫ ⌞c⌟ = ⊥ := by hkat
  exact ⟨rfl, rfl⟩

/-- Even a usable Hoare hypothesis does not justify reversing a program. -/
example (p : X ⟶ Y) (q : Y ⟶ X) (b : T X) (c : T Y)
    (_h : TypedKAT.HoareTriple b p c) : q = q := by
  fail_if_success have : TypedKAT.HoareTriple c q b := by hkat
  rfl

/-- With no usable hypothesis, a nontrivial identity still belongs to `kat`. -/
example (p : X ⟶ Y) (b : T X) : ⌞b⌟ ≫ p ⊔ ⌞bᶜ⌟ ≫ p = p := by
  fail_if_success hkat
  kat

end WithTests

/-- A Boolean assumption may be needed at either end when the test family is constant. -/
example {C : Type u} [Category.{v} C] [KleeneCategory C] {B : Type w}
    [BooleanAlgebra B] [TypedKAT C (fun _ ↦ B)] {X Y : C}
    (p : X ⟶ Y) (b c : B) (h : b ≤ c) :
    p ≫ TypedKAT.test (T := fun _ : C ↦ B) b ≤
      p ≫ TypedKAT.test (T := fun _ : C ↦ B) c := by hkat

/-- The tactic itself may introduce the category, all instances, and the hypotheses. -/
example : ∀ (C : Type u) (_ : Category.{v} C) (_ : KleeneCategory C)
    (T : C → Type w) (_ : ∀ A, BooleanAlgebra (T A)) (_ : TypedKAT C T)
    (X Y Z : C) (p : X ⟶ Y) (q : Y ⟶ Z) (b : T X) (c : T Y) (d : T Z),
    TypedKAT.HoareTriple b p c → TypedKAT.HoareTriple c q d →
    TypedKAT.HoareTriple b (p ≫ q) d := by hkat

private def numbers : RelCat := ℕ
private def booleans : RelCat := Bool

/-- Concrete heterogeneous relations keep their categorical composition direction. -/
theorem relation_sequence (p : numbers ⟶ booleans) (q : booleans ⟶ numbers)
    (b d : Set numbers) (c : Set booleans)
    (hp : TypedKAT.HoareTriple b p c) (hq : TypedKAT.HoareTriple c q d) :
    TypedKAT.HoareTriple b (p ≫ q) d := by hkat 10000

example (r : SetRel numbers booleans) (q : booleans ⟶ numbers)
    (h : RelCat.Hom.ofRel r = (⊥ : numbers ⟶ booleans)) :
    RelCat.Hom.ofRel r ≫ q = ⊥ := by hkat

/-- Concrete action atoms also work under star and join in the path construction. -/
example (r : SetRel numbers numbers)
    (h : RelCat.Hom.ofRel r = (⊥ : numbers ⟶ numbers)) :
    KStar.kstar (α := numbers ⟶ numbers) (RelCat.Hom.ofRel r) = 𝟙 numbers := by hkat

example (r s : SetRel numbers booleans) (q : booleans ⟶ numbers) :
    let p : numbers ⟶ booleans := RelCat.Hom.ofRel r
    let p' : numbers ⟶ booleans := RelCat.Hom.ofRel s
    p ⊔ p' = ⊥ → (p ⊔ p') ≫ q = ⊥ := by
  dsimp only
  hkat

/-- Rectangular matrices use the same typed tactic and independent diagonal tests. -/
theorem matrix_sequence {K B : Type*} [KleeneAlgebra K] [BooleanAlgebra B] [KAT B K]
    {X Y Z : Matrix.Mat K} (p : X ⟶ Y) (q : Y ⟶ Z)
    (b : Fin X.dim → B) (c : Fin Y.dim → B) (d : Fin Z.dim → B)
    (hp : TypedKAT.HoareTriple (T := fun A : Matrix.Mat K ↦ Fin A.dim → B) b p c)
    (hq : TypedKAT.HoareTriple (T := fun A : Matrix.Mat K ↦ Fin A.dim → B) c q d) :
    TypedKAT.HoareTriple (T := fun A : Matrix.Mat K ↦ Fin A.dim → B) b (p ≫ q) d := by
  hkat

/-- `End` remains on the untyped branch, with Mathlib's reversed multiplication. -/
example {C : Type u} [Category.{v} C] [KleeneCategory C] {X : C}
    (p q : End X) (h : p ≤ 0) : p * q = 0 := by hkat

end TypedKAT.HypothesisExamples
