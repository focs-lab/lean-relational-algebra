import RelationAlgebra.Decide.RaTactic

/-!
# Typed `ra` regressions

The same commands handle abstract categories, heterogeneous relations, and rectangular
matrices. Failed normalization is not evidence that an equation is invalid.
-/

open CategoryTheory KleeneCategoryWithConverse
open scoped Computability KleeneCategoryWithConverse

universe u v

namespace TypedRaExamples

section Abstract
variable {C : Type u} [Category.{v} C] [KleeneCategory C] [KleeneCategoryWithConverse C]
  {X Y Z : C} (f h : X ⟶ Y) (g : Y ⟶ Z) (r : X ⟶ X)

theorem reverse_distribute : ((f ⊔ h) ≫ g)ᵒ = gᵒ ≫ fᵒ ⊔ gᵒ ≫ hᵒ := by ra
theorem reverse_iterate : ((r ⊔ r)∗)ᵒ = (rᵒ)∗ := by ra
theorem inclusion : fᵒ ≤ (f ⊔ h)ᵒ := by ra
example : (fᵒ)ᵒ ≫ 𝟙 Y = f := by ra
example : (⊥ : X ⟶ Y)ᵒ = ⊥ := by ra
example : (⊥ : X ⟶ X)∗ = 𝟙 X := by ra
example : (r∗)∗ = r∗ := by ra
example : (⊥ : X ⟶ Z) = f ≫ (⊥ : Y ⟶ Z) := by ra
example : ((𝟙 X)ᵒ ≫ f)ᵒ = fᵒ := by ra
example : ∀ (k : Y ⟶ X), (f ≫ k)ᵒ = kᵒ ≫ fᵒ := by ra

/-- Each normalizer visibly leaves the simplified categorical goal. -/
theorem normalise_remaining (hf : f = h) :
    (𝟙 X ≫ f ⊔ ⊥)ᵒ = hᵒ := by
  ra_normalise
  guard_target =ₛ fᵒ = hᵒ
  exact congrArg converse hf

theorem simplify_remaining (hf : f = h) :
    ((𝟙 X ≫ f)ᵒ ⊔ ⊥) = hᵒ := by
  ra_simpl
  guard_target =ₛ fᵒ = hᵒ
  exact congrArg converse hf

example (hf : f ≤ h) : (𝟙 X ≫ f ⊔ ⊥)ᵒ ≤ hᵒ := by
  ra_normalise
  guard_target =ₛ fᵒ ≤ hᵒ
  exact converse_mono hf

example : ((f ⊔ h) ≫ g)ᵒ = gᵒ ≫ fᵒ ⊔ gᵒ ≫ hᵒ := by ra_normalise
example : ((𝟙 X ≫ f)ᵒ)ᵒ = f := by ra_simpl
example : ((⊥ : X ⟶ Y) ≫ (⊥ : Y ⟶ X))∗ = 𝟙 X := by ra_normalise

set_option linter.style.multiGoal false in
example : (f ≫ g)ᵒ = gᵒ ≫ fᵒ ∧ True := by
  constructor
  ra
  trivial

set_option linter.style.multiGoal false in
example : (𝟙 X ≫ f)ᵒ = fᵒ ∧ True := by
  constructor
  ra_normalise
  trivial

set_option linter.style.multiGoal false in
example : (𝟙 X ≫ f)ᵒ = fᵒ ∧ True := by
  constructor
  ra_simpl
  trivial

/-- Invalid identities must not be accepted. -/
example : True := by
  fail_if_success have : f = h := by ra
  fail_if_success have : r ≫ (f ≫ fᵒ) = (f ≫ fᵒ) ≫ r := by ra
  fail_if_success have : fᵒ = (⊥ : Y ⟶ X) := by ra
  trivial

/-- A valid induction law lies outside structural normalization. -/
example : r ≫ r∗ = r∗ ≫ r := by
  fail_if_success ra
  exact (KleeneCategory.kstar_comp_comm r).symm

/-- Star readback has to preserve the loop endpoint. -/
example : ((f ≫ fᵒ ⊔ ⊥)∗)ᵒ = (f ≫ fᵒ)∗ := by ra_normalise
example : (((⊥ : Y ⟶ X)ᵒ) ≫ (⊥ : Y ⟶ X))∗ = 𝟙 X := by ra_simpl

/-- An operation outside the syntax is an opaque morphism. -/
example (opaqueMorphism : (X ⟶ Y) → (X ⟶ Y)) :
    (𝟙 X ≫ opaqueMorphism f)ᵒ = (opaqueMorphism f)ᵒ := by ra

/-- Existing untyped notation on `End` retains its multiplication order. -/
example (a b : End X) : Star.star (R := End X) (a * b) =
    Star.star (R := End X) b * Star.star (R := End X) a := by ra

end Abstract

private def numbers : RelCat := ℕ
private def booleans : RelCat := Bool
private def units : RelCat := Unit

/-- Genuine heterogeneous relations, with three distinct endpoint types. -/
theorem relations (f : numbers ⟶ booleans) (g : booleans ⟶ units) :
    (f ≫ g)ᵒ = gᵒ ≫ fᵒ := by ra

/-- Rectangular dimensions cannot be interchanged accidentally. -/
theorem matrices {K : Type u} [KleeneAlgebra K] [StarRing K]
    (f : (⟨2⟩ : Matrix.Mat K) ⟶ ⟨3⟩) (g : (⟨3⟩ : Matrix.Mat K) ⟶ ⟨4⟩) :
    (f ≫ g)ᵒ = gᵒ ≫ fᵒ := by ra

example {K : Type u} [KleeneAlgebra K] [StarRing K]
    (f : (⟨0⟩ : Matrix.Mat K) ⟶ ⟨3⟩) : (f ≫ fᵒ)ᵒ = f ≫ fᵒ := by ra

example (f h : numbers ⟶ booleans) (hf : f = h) : (𝟙 numbers ≫ f)ᵒ = hᵒ := by
  ra_normalise
  guard_target =ₛ fᵒ = hᵒ
  exact congrArg converse hf

example {K : Type u} [KleeneAlgebra K] [StarRing K]
    (f h : (⟨2⟩ : Matrix.Mat K) ⟶ ⟨3⟩) (hf : f = h) :
    (fᵒ ≫ 𝟙 (⟨2⟩ : Matrix.Mat K)) = hᵒ := by
  ra_simpl
  guard_target =ₛ fᵒ = hᵒ
  exact congrArg converse hf

end TypedRaExamples
