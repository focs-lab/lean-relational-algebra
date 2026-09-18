/- SPDX-License-Identifier: LGPL-3.0-or-later
Copyright (c) 2026 Umang Mathur and contributors. See LICENSE and NOTICE.md. -/
import RelationAlgebra.Models.RelPoints
import RelationAlgebra.TypedRelationPredicates
import RelationAlgebra.Models.FinRelCategory
import RelationAlgebra.Models.SetoidRelCategory
import RelationAlgebra.Models.MatrixResidual

/-!
# Typed allegories, maps, points, and atoms

Tests of weak assumptions, composition direction, empty carriers, and model coherence.
-/

open CategoryTheory AllegoryCategory
open scoped Computability
universe u v

noncomputable section

namespace Examples.TypedAllegory

section Weak
variable {C : Type u} [Category.{v} C] [AllegoryCategory C] {X Y Z : C}

-- No Kleene, Boolean, bottom, or top structure is assumed here.
example (f : X ⟶ Y) (g h : Y ⟶ Z) (hf : Functional f) :
    f ≫ (g ⊓ h) = (f ≫ g) ⊓ (f ≫ h) := hf.comp_inf g h

example (f g : X ⟶ X) (hf : f ≤ 𝟙 X) (hg : g ≤ 𝟙 X) : f ≫ g = g ≫ f := by
  rw [comp_eq_inf_of_le_id f g hf hg, comp_eq_inf_of_le_id g f hg hf, inf_comm]

example (f : X ⟶ Y) (g : Y ⟶ Z) (hf : IsMap f) (hg : IsMap g) :
    IsMap (f ≫ g) := hf.comp hg

example (f : End X) : Allegory.Functional f ↔ Injective (show X ⟶ X from f) :=
  functional_end_iff f

example (f : X ⟶ X) (hr : IsReflexive f) (ha : IsAntisymmetric f) :
    f ⊓ fᵒ = 𝟙 X := kernel_eq_id hr ha

variable [∀ X Y : C, OrderTop (X ⟶ Y)]

example (a : X ⟶ Y) (ha : AllegoryCategory.IsAtom a) (hn : IsNonemptyObject Z) :
    ∃ (p : X ⟶ Z) (q : Y ⟶ Z), IsPoint p ∧ IsPoint q ∧ a = p ≫ qᵒ :=
  ha.exists_points hn

example (p : X ⟶ Z) (q : Y ⟶ Z) (hp : IsPoint p) (hq : IsPoint q) :
    AllegoryCategory.IsAtom (p ≫ qᵒ) := isAtom_of_points hp hq

example (p f : X ⟶ Y) (hp : IsPoint p) (hv : IsVector f) (hn : IsNonempty f)
    (hle : f ≤ p) : f = p := hp.eq_of_nonempty_vector_le hv hn hle

example (a f : X ⟶ Y) (ha : AllegoryCategory.IsAtom a) (hn : IsNonempty f)
    (hle : f ≤ a) : f = a := ha.eq_of_nonempty_le hn hle

end Weak

-- SingleObj reverses scalar multiplication, hence the swapped predicate.
example {K : Type u} [Allegory K] (X : SingleObj K) (f : X ⟶ X) :
    Functional f ↔ Allegory.Injective (show K from f) := Iff.rfl

section Relations
open RelCat

abbrev Inputs : RelCat := Bool
abbrev Outputs : RelCat := Fin 3
abbrev One : RelCat := Unit
abbrev EmptyObject : RelCat := Empty

/-- A map with different source and target types. -/
def encode : Inputs ⟶ Outputs := graph fun b ↦ if b then 2 else 0

example : IsMap encode := graph_isMap _

example : Injective encode := by
  apply (graph_injective_iff _).mpr
  intro x y h
  cases x <;> cases y <;> simp_all

example : ¬ Surjective encode := by
  intro h
  obtain ⟨x, hx⟩ := (graph_surjective_iff _).mp h 1
  cases x <;> simp_all [encode]

example : IsMap (graph (fun _ : Inputs ↦ () : Inputs → One)) := graph_isMap _

/-- Functional and injective are not interchangeable. -/
theorem constant_not_injective : ¬ Injective (graph (fun _ : Inputs ↦ () : Inputs → One)) := by
  intro h
  have he := (graph_injective_iff _).mp h (a₁ := false) (a₂ := true) rfl
  cases he

example : IsPoint (row false : Inputs ⟶ Outputs) := row_isPoint _

example : AllegoryCategory.IsAtom (singleton false (2 : Outputs)) := singleton_isAtom _ _

example : _root_.IsAtom (singleton false (2 : Outputs)) :=
  isAtom_iff_lattice_isAtom.mp (singleton_isAtom _ _)

example : (row false : Inputs ⟶ One) ≫ (row (2 : Outputs) : Outputs ⟶ One)ᵒ =
    singleton false (2 : Outputs) := by
  ext ⟨x, y⟩
  change (∃ _ : Unit, x = false ∧ y = 2) ↔ (x, y) = (false, 2)
  simp [Prod.mk.injEq]

-- Empty targets have no points, even though every relation into them is a vector.
example (f : Inputs ⟶ EmptyObject) : IsVector f := by
  apply isVector_iff.mpr
  intro _ _ z
  exact z.elim

example (f : Inputs ⟶ EmptyObject) : ¬ IsPoint f := by
  intro h
  obtain ⟨y⟩ := (isPoint_iff_exists_row.mp h).1
  exact y.elim

example (f : EmptyObject ⟶ Outputs) : ¬ AllegoryCategory.IsAtom f := by
  intro h
  obtain ⟨x, _, _⟩ := isNonempty_iff.mp h.nonempty
  exact x.elim

example : ¬ IsNonemptyObject EmptyObject := by
  rw [isNonemptyObject_iff]
  exact not_nonempty_iff.mpr inferInstance

-- An inhabited universe of relation objects detects the empty relation.
example : ¬ IsNonempty (⊥ : EmptyObject ⟶ EmptyObject) := by
  simp [isNonempty_iff_ne_bot]

example : ¬ IsPoint (row false : Inputs ⟶ EmptyObject) := by
  intro h
  obtain ⟨y⟩ := (isPoint_iff_exists_row.mp h).1
  exact y.elim

example : (singleton false (2 : Outputs)).rel ≠ (singleton true (2 : Outputs)).rel := by
  intro h
  have hm : (false, (2 : Outputs)) ∈ (singleton true (2 : Outputs)).rel := by
    rw [← h]
    simp
  simp at hm

-- Complement transport along a point changes the target type.
example (f : Outputs ⟶ Inputs) :
    fᶜ ≫ (row false : Inputs ⟶ One) = (f ≫ (row false : Inputs ⟶ One))ᶜ :=
  (row_isPoint false).compl_comp f

end Relations

section Degenerate
open scoped SetRel

-- In the one-object empty-relation algebra, top = bottom. Upstream's predicates
-- intentionally differ from nonzero morphisms and lattice atoms in this case.
abbrev D := SingleObj (SetRel Empty Empty)

local instance (X Y : D) : Subsingleton (X ⟶ Y) where
  allEq _ _ := Set.ext fun ⟨x, _⟩ ↦ x.elim

example (X : D) : IsNonempty (⊥ : X ⟶ X) := fun _ _ ↦ Subsingleton.le _ _

example (X : D) : AllegoryCategory.IsAtom (⊥ : X ⟶ X) :=
  ⟨Subsingleton.le _ _, Subsingleton.le _ _, fun _ _ ↦ Subsingleton.le _ _⟩

example (X : D) : ¬ _root_.IsAtom (⊥ : X ⟶ X) := fun h ↦ h.ne_bot rfl

end Degenerate

-- All existing relation-algebra models inherit the weak interface.
example : AllegoryCategory FinRelCat := inferInstance
example : AllegoryCategory SetoidRelCat := inferInstance
example {K : Type u} [RelationAlgebra K] : AllegoryCategory (Matrix.Mat K) := inferInstance

example (f : FinRelCat.of Bool ⟶ FinRelCat.of (Fin 3)) :
    fᵒ = KleeneCategoryWithConverse.converse f := rfl

example (X Y : SetoidRelCat) (f : X ⟶ Y) :
    fᵒ = KleeneCategoryWithConverse.converse f := rfl

example {K : Type u} [RelationAlgebra K] (f : (⟨2⟩ : Matrix.Mat K) ⟶ ⟨3⟩) :
    fᵒ = KleeneCategoryWithConverse.converse f := rfl

example {K : Type u} [RelationAlgebra K] (X : SingleObj K) (f : X ⟶ X) :
    fᵒ = KleeneCategoryWithConverse.converse f := rfl

example (X : RelCat) (f : End X) : star f = (show X ⟶ X from f)ᵒ := rfl

example (X : RelCat) (f : X ⟶ X) : IsPreorder f∗ := isPreorder_kstar f

example (X : RelCat) (f : X ⟶ X) (h : IsTransitive f) : f∗ = 𝟙 X ⊔ f := h.kstar_eq

end Examples.TypedAllegory
