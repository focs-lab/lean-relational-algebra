import RelationAlgebra.TypedResiduated

/-! # Typed Boolean relation algebra and residuals: interface and model checks -/

open CategoryTheory KleeneCategoryWithConverse ResiduatedKleeneCategory
open scoped Computability KleeneCategoryWithConverse ResiduatedKleeneCategory

universe u v
namespace TypedResidualExamples

section Abstract
variable {C : Type u} [Category.{v} C] [KleeneCategory C]
  [BooleanKleeneCategory C] [KleeneCategoryWithConverse C] [RelationCategory C]
  {W X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)

theorem adjunction : g ≤ f ⇘ h ↔ f ≫ g ≤ h := ldiv_spec _ _ _
theorem right_adjunction : f ≤ h ⇙ g ↔ f ≫ g ≤ h := rdiv_spec _ _ _
theorem schroeder : f ≫ g ≤ h ↔ fᵒ ≫ hᶜ ≤ gᶜ := RelationCategory.schroeder_left
theorem dedekind : (f ≫ g) ⊓ h ≤ (f ⊓ h ≫ gᵒ) ≫ (g ⊓ fᵒ ≫ h) :=
  RelationCategory.dedekind _ _ _
example : (f ⊓ fᶜ : X ⟶ Y) = ⊥ := inf_compl_eq_bot
example : (f ⊔ fᶜ : X ⟶ Y) = ⊤ := sup_compl_eq_top
example : (fᶜ)ᵒ = (fᵒ)ᶜ := converse_compl _
example : (f ⇘ h)ᵒ = hᵒ ⇙ fᵒ := converse_ldiv _ _
example : (h ⇙ g)ᵒ = gᵒ ⇘ hᵒ := converse_rdiv _ _
example : (f ⇘ f)∗ = f ⇘ f := kstar_ldiv_self _
example : (f ⇙ f)∗ = f ⇙ f := kstar_rdiv_self _
end Abstract

section ResidualOnly
variable {C : Type u} [Category.{v} C] [KleeneCategory C] [ResiduatedKleeneCategory C]
  {W X Y Z : C}

/-- These laws require neither Boolean structure nor converse. -/
example (f : W ⟶ X) (g : X ⟶ Y) (h : W ⟶ Z) :
    (f ≫ g) ⇘ h = g ⇘ (f ⇘ h) := comp_ldiv _ _ _
example (f : X ⟶ Y) (h : X ⟶ Z) : f ≫ (f ⇘ h) ≤ h := comp_ldiv_le _ _
example (f : X ⟶ Y) : (f ⇘ f)∗ = f ⇘ f := kstar_ldiv_self _
example (a b : End X) : ResiduatedIdemSemiring.ldiv a b =
    ResiduatedKleeneCategory.rdiv (C := C) b a := rfl
end ResidualOnly

private def numbers : RelCat := ℕ
private def booleans : RelCat := Bool
private def units : RelCat := Unit

/-- Universal quantification over the common source is the actual relational semantics. -/
theorem relation_left (f : numbers ⟶ booleans) (h : numbers ⟶ units) (b : Bool) :
    (b, ()) ∈ (f ⇘ h).rel ↔ ∀ n, (n, b) ∈ f.rel → (n, ()) ∈ h.rel :=
  RelCat.Hom.mem_ldiv _ _ _ _

theorem relation_right (h : numbers ⟶ units) (g : booleans ⟶ units) (n : ℕ) (b : Bool) :
    (n, b) ∈ (h ⇙ g).rel ↔ ∀ z, (b, z) ∈ g.rel → (n, z) ∈ h.rel :=
  RelCat.Hom.mem_rdiv _ _ _ _

example : (⊥ : numbers ⟶ booleans) ⇘ (⊥ : numbers ⟶ units) = ⊤ := bot_ldiv _
example : (⊥ : numbers ⟶ units) ⇙ (⊥ : booleans ⟶ units) = ⊤ := rdiv_bot _

/-- End recovers Boolean relation algebra without changing its composition convention. -/
example {C : Type u} [Category.{v} C] [KleeneCategory C]
    [BooleanKleeneCategory C] [KleeneCategoryWithConverse C] [RelationCategory C]
    (X : C) : RelationAlgebra (End X) := inferInstance

end TypedResidualExamples
