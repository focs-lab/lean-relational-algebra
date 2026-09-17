import RelationAlgebra.Decide.RaTactic
import RelationAlgebra.Models.MatrixResidual

/-!
# Boolean and residual automation regressions

The examples cover normalization inside the new operations, partial inclusion reasoning,
proof reconstruction in abstract and concrete models, and rejection of invalid laws.
-/

open CategoryTheory KleeneCategoryWithConverse
open scoped Computability

universe u v
namespace FullRaExamples

section Untyped
open scoped RelationAlgebra
variable {K : Type u} [RelationAlgebra K] (a b c d : K)

theorem boolean_demorgan : (a ⊓ b)ᶜ = aᶜ ⊔ bᶜ := by ra
example : a ⊔ b = b ⊔ a := by ra
example : (a ⊔ b) * c = a * c ⊔ b * c := by ra
example : (⊥ : K) * a = ⊥ := by ra
example : 1 * (a ⊔ ⊥) = a := by ra_simpl
theorem scalar_cancel : a * (a ⇘ b) ≤ b := by ra
theorem scalar_nested : (a * (b + c))ᶜ = (a*b + a*c)ᶜ := by ra
example : (⊤ : K)∗ = ⊤ := by ra
example : star ((a ⊓ b)ᶜ) = (star a ⊓ star b)ᶜ := by ra
example : (a ⊔ b) ⇘ c = (a ⇘ c) ⊓ (b ⇘ c) := by ra
example : a ⇘ (b ⊓ c) = (a ⇘ b) ⊓ (a ⇘ c) := by ra
example : (a ⇙ b) * b ≤ a := by ra
example : (a ⊓ b) ⇘ c ≥ a ⇘ c := by ra
example : star (a ⇘ b) = star b ⇙ star a := by ra
example : (a*b) ⇘ c = b ⇘ (a ⇘ c) := by ra
example : (a \ b) = a ⊓ bᶜ := by ra
example : (a ⇨ b) = b ⊔ aᶜ := by ra
example : (a ⊓ (b ⊔ c)) = (a ⊓ b) ⊔ (a ⊓ c) := by ra
example : a ⊓ (b ⊔ a) = a := by ra
example : (a ⊔ aᶜ) ⇘ b = (⊤ : K) ⇘ b := by ra
example : (a ⇘ a)∗ = a ⇘ a := by ra
example : a ≤ b ⇘ (b * (a ⊔ c)) := by ra
example : ((a+b)*c) ⊓ d ≤ (a*c+b*c) := by ra

-- Applied local functions remain valid atoms, without classifier diagnostics.
#guard_msgs in
example (F : K → K) : 1 * F a = F a := by ra

#guard_msgs in
example (F : K → K) : F (a ⊓ a) = F a := by ra

/-- The commands leave a readable residual goal when hypotheses are needed. -/
theorem scalar_remaining (h : a ⇘ c = b ⇘ c) : (1*a) ⇘ c = b ⇘ c := by
  ra_normalise
  guard_target =ₛ a ⇘ c = b ⇘ c
  exact h

example (h : a = b) : (aᶜ)ᶜ = b := by
  ra_simpl
  guard_target =ₛ a = b
  exact h

example (h : a = b) : a = a := by
  fail_if_success have : a ⇘ c = b ⇘ c := by ra
  fail_if_success have : aᶜ = bᶜ := by ra
  have _ := h
  rfl

/-- No commutativity, complement/composition homomorphism, or reversed variance is assumed. -/
example : True := by
  fail_if_success have : (a*b)ᶜ = aᶜ*bᶜ := by ra
  fail_if_success have : (a ⇘ b)ᶜ ≤ ((a ⊓ c) ⇘ b)ᶜ := by ra
  fail_if_success have : (a⊓b)*c = (a*c)⊓(b*c) := by ra
  trivial
end Untyped

section Typed
open scoped KleeneCategoryWithConverse ResiduatedKleeneCategory
variable {C : Type u} [Category.{v} C] [KleeneCategory C]
  [BooleanKleeneCategory C] [KleeneCategoryWithConverse C] [RelationCategory C]
  {W X Y Z : C} (f f' : X ⟶ Y) (g g' : Y ⟶ Z) (h : X ⟶ Z)

theorem typed_cancel : f ≫ (f ⇘ h) ≤ h := by ra
theorem typed_right_cancel : (h ⇙ g) ≫ g ≤ h := by ra
omit [KleeneCategoryWithConverse C] [RelationCategory C] in
theorem typed_nested : ((f ⊔ f') ≫ g)ᶜ = (f ≫ g)ᶜ ⊓ (f' ≫ g)ᶜ := by ra
theorem typed_residual_converse : (f ⇘ h)ᵒ = hᵒ ⇙ fᵒ := by ra
example : (⊤ : X ⟶ X)∗ = ⊤ := by ra
example : (f ⊔ f') ⇘ h = (f ⇘ h) ⊓ (f' ⇘ h) := by ra
example : ((f ⊓ f')ᶜ)ᵒ = (fᵒ)ᶜ ⊔ (f'ᵒ)ᶜ := by ra
example : (⊥ : X ⟶ Y) ⇘ h = ⊤ := by ra
example : (𝟙 X) ⇘ f = f := by ra
example : f ⇘ f ≤ (f ⊓ f') ⇘ f := by ra
example : (f ⇘ f)∗ = f ⇘ f := by ra
example : (f ≫ g) ⊓ h ≤ (f ⊓ h ≫ gᵒ) ≫ (g ⊓ fᵒ ≫ h) := by ra
example : (f ⊓ f') ≫ (g ⊓ g') ≤ f ≫ g := by ra
example : g ≤ f ⇘ (f ≫ (g ⊔ g')) := by ra
example (k : W ⟶ X) : (k ≫ f) ⇘ (k ≫ h) = f ⇘ (k ⇘ (k ≫ h)) := by ra
example : ∀ (k : X ⟶ Y), ((𝟙 X ≫ k)ᶜ)ᵒ = (kᵒ)ᶜ := by ra

theorem typed_remaining (hh : f ⇘ h = f' ⇘ h) : (𝟙 X ≫ f) ⇘ h = f' ⇘ h := by
  ra_normalise
  guard_target =ₛ f ⇘ h = f' ⇘ h
  exact hh

set_option linter.style.multiGoal false in
example : ((f ⊔ f')ᶜ)ᵒ = (fᵒ)ᶜ ⊓ (f'ᵒ)ᶜ ∧ True := by
  constructor
  ra
  trivial

set_option linter.style.multiGoal false in
example : (𝟙 X) ⇘ f = f ∧ True := by
  constructor
  ra_simpl
  trivial

set_option linter.style.multiGoal false in
example : (f ⊓ f')ᶜ = fᶜ ⊔ f'ᶜ ∧ True := by
  constructor
  ra_normalise
  trivial

example : f = f := by
  fail_if_success have : (f ≫ g)ᶜ = fᶜ ≫ gᶜ := by ra
  fail_if_success have : (f ⊓ f') ≫ g = (f ≫ g) ⊓ (f' ≫ g) := by ra
  fail_if_success have := (ResiduatedKleeneCategory.ldiv f g : Y ⟶ Z)
  rfl
end Typed

section ResidualOnly
open scoped ResiduatedKleeneCategory
variable {C : Type u} [Category.{v} C] [KleeneCategory C] [ResiduatedKleeneCategory C]
  {X Y Z : C}
example (f : X ⟶ Y) (h : X ⟶ Z) : f ≫ (f ⇘ h) ≤ h := by ra
example (f : X ⟶ Y) : (f ⇘ f)∗ = f ⇘ f := by ra
end ResidualOnly

section Models
open scoped KleeneCategoryWithConverse ResiduatedKleeneCategory
private def numbers : RelCat := ℕ
private def booleans : RelCat := Bool
private def units : RelCat := Unit

theorem relation_cancel (f : numbers ⟶ booleans) (h : numbers ⟶ units) :
    f ≫ (f ⇘ h) ≤ h := by ra

theorem matrix_cancel {K : Type u} [ResiduatedKleeneLattice K]
    (f : (⟨2⟩ : Matrix.Mat K) ⟶ ⟨3⟩) (h : (⟨2⟩ : Matrix.Mat K) ⟶ ⟨4⟩) :
    f ≫ (f ⇘ h) ≤ h := by ra

example {K : Type u} [RelationAlgebra K]
    (f : (⟨2⟩ : Matrix.Mat K) ⟶ ⟨3⟩) (h : (⟨2⟩ : Matrix.Mat K) ⟶ ⟨4⟩) :
    (f ⇘ h)ᵒ = hᵒ ⇙ fᵒ := by ra

example {K : Type u} [RelationAlgebra K] (A B : Matrix (Fin 2) (Fin 2) K) :
    star (A ⊓ B) = star A ⊓ star B := by ra

example {K : Type u} [RelationAlgebra K] (A : Matrix (Fin 2) (Fin 2) K) :
    star Aᶜ = (star A)ᶜ := by ra
end Models
end FullRaExamples
