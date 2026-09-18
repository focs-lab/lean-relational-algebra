/- SPDX-License-Identifier: LGPL-3.0-or-later
Lean translation and extensions, 2026-09-18. See LICENSE and NOTICE.md. -/
import RelationAlgebra.TypedPoints
import RelationAlgebra.TypedIteration

/-!
# Boolean and iteration laws for typed relational predicates

The remaining Boolean and Kleene laws for predicates from Pous's `relalg.v`.
These use the canonical allegory of a `RelationCategory`, ensuring its order and
converse agree with the Boolean and Kleene operations. The points/atoms theory
itself remains in `TypedPoints`, under weaker hypotheses.
-/

open CategoryTheory
open scoped Computability
universe u v

namespace AllegoryCategory

variable {C : Type u} [Category.{v} C] [KleeneCategory C]
  [BooleanKleeneCategory C] [KleeneCategoryWithConverse C] [RelationCategory C]
  {X Y Z : C}

/-- Every pair is related in at least one direction. -/
def IsLinear (f : X ⟶ X) : Prop := f ⊔ fᵒ = ⊤

theorem IsLinear.converse {f : X ⟶ X} (h : IsLinear f) : IsLinear fᵒ := by
  simpa [IsLinear, sup_comm] using h

theorem isSymmetric_compl_id : IsSymmetric ((𝟙 X)ᶜ) := by
  change KleeneCategoryWithConverse.converse ((𝟙 X)ᶜ) = _
  simp

theorem IsIrreflexive.le_compl_id {f : X ⟶ X} (h : IsIrreflexive f) : f ≤ (𝟙 X)ᶜ :=
  le_compl_iff_disjoint_right.mpr (disjoint_iff.mpr h)

theorem IsVector.sup {f g : X ⟶ Y} (hf : IsVector f) (hg : IsVector g) :
    IsVector (f ⊔ g) := by
  change (f ⊔ g) ≫ (⊤ : Y ⟶ Y) = f ⊔ g
  rw [KleeneCategory.sup_comp, hf, hg]

theorem isVector_bot : IsVector (⊥ : X ⟶ Y) := KleeneCategory.bot_comp _

theorem isVector_top : IsVector (⊤ : X ⟶ Y) := top_comp_top_right

/-- Disjoint relations cannot return to the identity through converse composition. -/
theorem inf_id_comp_converse_eq_bot {f g : X ⟶ Y} (h : f ⊓ g = ⊥) :
    (𝟙 X) ⊓ (f ≫ gᵒ) = ⊥ := by
  apply le_antisymm _ bot_le
  calc (𝟙 X) ⊓ (f ≫ gᵒ) = (f ≫ gᵒ) ⊓ 𝟙 X := inf_comm _ _
    _ ≤ (f ⊓ (𝟙 X) ≫ (gᵒ)ᵒ) ≫ gᵒ := modular _ _ _
    _ = ⊥ := by simp [h]

theorem IsVector.disjoint_iff {f g : X ⟶ Y} (hg : IsVector g) :
    f ⊓ g = ⊥ ↔ gᵒ ≫ f = ⊥ := by
  rw [← le_bot_iff (a := gᵒ ≫ f), RelationCategory.schroeder_left]
  change f ⊓ g = ⊥ ↔ (gᵒ)ᵒ ≫ (⊥ : Y ⟶ Y)ᶜ ≤ fᶜ
  rw [converse_converse, compl_bot, hg]
  exact ⟨fun h ↦ le_compl_iff_disjoint_left.mpr (_root_.disjoint_iff.mpr h),
    fun h ↦ _root_.disjoint_iff.mp (le_compl_iff_disjoint_left.mp h)⟩

theorem Injective.compl_comp_le {g : Y ⟶ Z} (hg : Injective g) (f : X ⟶ Y) :
    fᶜ ≫ g ≤ (f ≫ g)ᶜ := by
  rw [RelationCategory.schroeder_right, compl_compl]
  change (f ≫ g) ≫ gᵒ ≤ (fᶜ)ᶜ
  rw [compl_compl, Category.assoc]
  simpa using comp_mono_right hg f

theorem Surjective.compl_comp_le {g : Y ⟶ Z} (hg : Surjective g) (f : X ⟶ Y) :
    (f ≫ g)ᶜ ≤ fᶜ ≫ g := by
  have hu : (f ≫ g) ⊔ (fᶜ ≫ g) = ⊤ := by
    rw [← KleeneCategory.sup_comp, sup_compl_eq_top, hg.top_comp]
  calc (f ≫ g)ᶜ = (f ≫ g)ᶜ ⊓ ((f ≫ g) ⊔ (fᶜ ≫ g)) := by rw [hu, inf_top_eq]
    _ ≤ fᶜ ≫ g := by simp [inf_sup_left]

theorem IsPoint.compl_comp {p : Y ⟶ Z} (hp : IsPoint p) (f : X ⟶ Y) :
    fᶜ ≫ p = (f ≫ p)ᶜ :=
  (hp.injective.compl_comp_le f).antisymm (hp.surjective.compl_comp_le f)

/-- Disjoint vectors stay disjoint after arbitrary subsequent steps. -/
theorem IsVector.disjoint_comp {f g : X ⟶ Y} (hf : IsVector f) (h : f ⊓ g = ⊥)
    (f' g' : Y ⟶ Z) : (f ≫ f') ⊓ (g ≫ g') = ⊥ := by
  have hz : fᵒ ≫ g = ⊥ := hf.disjoint_iff.mp (by simpa [inf_comm] using h)
  apply le_antisymm _ bot_le
  calc (f ≫ f') ⊓ (g ≫ g') ≤ f ≫ (f' ⊓ fᵒ ≫ g ≫ g') := comp_inf_le_comp_inf _ _ _
    _ = ⊥ := by rw [← Category.assoc fᵒ, hz]; simp

theorem isPreorder_kstar (f : X ⟶ X) : IsPreorder f∗ :=
  ⟨KleeneCategory.id_le_kstar f, (KleeneCategory.kstar_comp_kstar f).le⟩

theorem isTransitive_kplus (f : X ⟶ X) : IsTransitive f⁺ :=
  KleeneCategory.kplus_comp_kplus_le f

theorem IsReflexive.kplus {f : X ⟶ X} (h : IsReflexive f) : IsReflexive f⁺ :=
  h.trans (KleeneCategory.le_kplus f)

theorem IsSymmetric.kstar {f : X ⟶ X} (h : IsSymmetric f) : IsSymmetric f∗ := by
  change KleeneCategoryWithConverse.converse f∗ = f∗
  rw [KleeneCategoryWithConverse.converse_kstar, show
    KleeneCategoryWithConverse.converse f = f from h]

theorem IsSymmetric.kplus {f : X ⟶ X} (h : IsSymmetric f) : IsSymmetric f⁺ := by
  change KleeneCategoryWithConverse.converse f⁺ = f⁺
  rw [KleeneCategoryWithConverse.converse_kplus, show
    KleeneCategoryWithConverse.converse f = f from h]

theorem IsTransitive.kplus_eq {f : X ⟶ X} (h : IsTransitive f) : f⁺ = f :=
  (KleeneCategory.kplus_le_of_comp_le_right le_rfl h).antisymm (KleeneCategory.le_kplus f)

theorem IsTransitive.kstar_eq {f : X ⟶ X} (h : IsTransitive f) : f∗ = 𝟙 X ⊔ f := by
  rw [← KleeneCategory.id_sup_kplus, h.kplus_eq]

theorem IsPreorder.kstar_eq {f : X ⟶ X} (h : IsPreorder f) : f∗ = f := by
  rw [h.transitive.kstar_eq, sup_eq_right.mpr h.reflexive]

end AllegoryCategory
