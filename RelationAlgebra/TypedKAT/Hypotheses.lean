import RelationAlgebra.TypedKAT

/-!
# Typed Hoare hypotheses

These are the heterogeneous counterparts of `KAT/Hypotheses.lean`. A zero hypothesis
`z : A ⟶ B` can contribute to a goal in `X ⟶ Y` after composition with paths
`u : X ⟶ A` and `v : B ⟶ Y`. The resulting zero morphisms can then be joined.

Only soundness is needed: every added term vanishes by a supplied hypothesis.
Completeness of Hardin–Kozen hypothesis elimination is not claimed here. The conversion
rules follow `theories/kat_tac.v` in Damien Pous' `relation-algebra` library.
-/

open CategoryTheory
open scoped TypedKAT

universe u v w

namespace TypedKAT

section Eliminate

variable {C : Type u} [Category.{v} C] [KleeneCategory C] {X Y A B : C}

/-- Transport a zero hypothesis into another hom-set using well-typed contexts. -/
theorem context_le_bot (u : X ⟶ A) (v : B ⟶ Y) {z : A ⟶ B} (hz : z ≤ ⊥) :
    u ≫ z ≫ v ≤ ⊥ := by
  rw [le_antisymm hz bot_le, KleeneCategory.bot_comp, KleeneCategory.comp_bot]

/-- Remove an added zero morphism from an equality. -/
theorem hoare_elim_eq (z x y : X ⟶ Y) (hz : z ≤ ⊥) (h : x ⊔ z = y ⊔ z) : x = y := by
  simpa only [le_antisymm hz bot_le, sup_bot_eq] using h

/-- Remove an added zero morphism from an inequality. -/
theorem hoare_elim_le (z x y : X ⟶ Y) (hz : z ≤ ⊥) (h : x ≤ y ⊔ z) : x ≤ y := by
  simpa only [le_antisymm hz bot_le, sup_bot_eq] using h

theorem le_bot_to_hoare {z : X ⟶ Y} (h : z ≤ ⊥) : z ≤ ⊥ := h

theorem eq_bot_to_hoare {z : X ⟶ Y} (h : z = ⊥) : z ≤ ⊥ := h.le

end Eliminate

section Convert

variable {C : Type u} [Category.{v} C] [KleeneCategory C]
  {T : C → Type w} [∀ X, BooleanAlgebra (T X)] [TypedKAT C T] {X Y : C}

theorem test_eq_to_hoare (b c : T X) (h : b = c) :
    (⌞b ⊓ cᶜ⌟ ⊔ ⌞bᶜ ⊓ c⌟ : X ⟶ X) ≤ ⊥ := by
  subst c
  simp only [inf_compl_eq_bot, compl_inf_eq_bot, test_bot, sup_idem, le_refl]

theorem test_le_to_hoare (b c : T X) (h : b ≤ c) : (⌞b ⊓ cᶜ⌟ : X ⟶ X) ≤ ⊥ := by
  have hbc : b ⊓ cᶜ = ⊥ := by rw [← sdiff_eq, sdiff_eq_bot_iff]; exact h
  simp only [hbc, test_bot, le_refl]

theorem test_comp_le_to_hoare (b : T X) (c : T Y) (p q : X ⟶ Y)
    (h : ⌞b⌟ ≫ p ≤ q ≫ ⌞c⌟) : ⌞b⌟ ≫ p ≫ ⌞cᶜ⌟ ≤ ⊥ := by
  calc ⌞b⌟ ≫ p ≫ ⌞cᶜ⌟ = (⌞b⌟ ≫ p) ≫ ⌞cᶜ⌟ := (Category.assoc _ _ _).symm
    _ ≤ (q ≫ ⌞c⌟) ≫ ⌞cᶜ⌟ := KleeneCategory.comp_le_comp_left h _
    _ = ⊥ := by rw [Category.assoc, test_comp_compl, KleeneCategory.comp_bot]

theorem comp_test_le_to_hoare (b : T Y) (c : T X) (p q : X ⟶ Y)
    (h : p ≫ ⌞b⌟ ≤ ⌞c⌟ ≫ q) : ⌞cᶜ⌟ ≫ p ≫ ⌞b⌟ ≤ ⊥ := by
  calc ⌞cᶜ⌟ ≫ p ≫ ⌞b⌟ ≤ ⌞cᶜ⌟ ≫ (⌞c⌟ ≫ q) := KleeneCategory.comp_le_comp_right h _
    _ = ⊥ := by rw [← Category.assoc, test_compl_comp, KleeneCategory.bot_comp]

theorem le_comp_test_to_hoare (c : T Y) (p q : X ⟶ Y) (h : q ≤ p ≫ ⌞c⌟) :
    q ≫ ⌞cᶜ⌟ ≤ ⊥ := by
  calc q ≫ ⌞cᶜ⌟ ≤ (p ≫ ⌞c⌟) ≫ ⌞cᶜ⌟ := KleeneCategory.comp_le_comp_left h _
    _ = ⊥ := by rw [Category.assoc, test_comp_compl, KleeneCategory.comp_bot]

theorem le_test_comp_to_hoare (c : T X) (p q : X ⟶ Y) (h : q ≤ ⌞c⌟ ≫ p) :
    ⌞cᶜ⌟ ≫ q ≤ ⊥ := by
  calc ⌞cᶜ⌟ ≫ q ≤ ⌞cᶜ⌟ ≫ (⌞c⌟ ≫ p) := KleeneCategory.comp_le_comp_right h _
    _ = ⊥ := by rw [← Category.assoc, test_compl_comp, KleeneCategory.bot_comp]

theorem hoareTriple_to_hoare {b : T X} {p : X ⟶ Y} {c : T Y}
    (h : HoareTriple b p c) : ⌞b⌟ ≫ p ≫ ⌞cᶜ⌟ ≤ ⊥ := h.le

/-- Rewrite an endomorphism whose restriction to a test is the identity on that test. -/
theorem test_comp_eq_to_hoare (c : T X) (p : X ⟶ X) (h : ⌞c⌟ ≫ p = ⌞c⌟) :
    p = ⌞cᶜ⌟ ≫ p ⊔ ⌞c⌟ := by
  rw [← h, ← KleeneCategory.sup_comp, test_compl_sup, Category.id_comp]

/-- The corresponding rewrite for restriction at the target. -/
theorem comp_test_eq_to_hoare (c : T X) (p : X ⟶ X) (h : p ≫ ⌞c⌟ = ⌞c⌟) :
    p = p ≫ ⌞cᶜ⌟ ⊔ ⌞c⌟ := by
  rw [← h, ← KleeneCategory.comp_sup, test_compl_sup, Category.comp_id]

end Convert

end TypedKAT
