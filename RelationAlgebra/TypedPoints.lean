/- SPDX-License-Identifier: LGPL-3.0-or-later
Lean translation and extensions, 2026-09-18. See LICENSE and NOTICE.md. -/
import RelationAlgebra.TypedAllegory

/-!
# Typed vectors, points, and atoms

The points/atoms development of Damien Pous's `relalg.v`, in an allegory with top.
`IsNonempty f` quantifies over every pair of objects, as upstream does. It is not
silently replaced by `f ≠ ⊥`: that equivalence needs a concrete model or additional
assumptions. Likewise `AllegoryCategory.IsAtom` is an algebraic predicate, distinct
from Mathlib's lattice `IsAtom`. Minimality below is among nonempty morphisms.
-/

open CategoryTheory
universe u v

namespace AllegoryCategory

variable {C : Type u} [Category.{v} C] [AllegoryCategory C]
  [∀ X Y : C, OrderTop (X ⟶ Y)] {W X Y Z : C}

@[simp] theorem converse_top : (⊤ : X ⟶ Y)ᵒ = ⊤ := by
  refine le_antisymm le_top ?_
  rw [← converse_le_converse_iff, converse_converse]
  exact le_top

theorem le_top_comp (f : X ⟶ Y) : f ≤ (⊤ : X ⟶ X) ≫ f := by
  simpa using comp_mono_left (le_top : 𝟙 X ≤ ⊤) f

theorem le_comp_top (f : X ⟶ Y) : f ≤ f ≫ (⊤ : Y ⟶ Y) := by
  simpa using comp_mono_right (le_top : 𝟙 Y ≤ ⊤) f

@[simp] theorem top_comp_top_left : (⊤ : X ⟶ X) ≫ (⊤ : X ⟶ Y) = ⊤ :=
  le_antisymm le_top (le_top_comp _)

@[simp] theorem top_comp_top_right : (⊤ : X ⟶ Y) ≫ (⊤ : Y ⟶ Y) = ⊤ :=
  le_antisymm le_top (le_comp_top _)

/-- Upstream's object-quantified notion of a nonempty morphism. -/
def IsNonempty (f : X ⟶ Y) : Prop :=
  ∀ P Q : C, (⊤ : P ⟶ Q) ≤ (⊤ : P ⟶ X) ≫ f ≫ (⊤ : Y ⟶ Q)

/-- Nonemptiness of an object means nonemptiness of its identity. -/
abbrev IsNonemptyObject (X : C) : Prop := IsNonempty (𝟙 X)

/-- A vector is unchanged by arbitrary steps at its target. -/
def IsVector (f : X ⟶ Y) : Prop := f ≫ (⊤ : Y ⟶ Y) = f

/-- An injective, nonempty vector. In relations, a singleton row. -/
structure IsPoint (p : X ⟶ Y) : Prop where
  vector : IsVector p
  injective : Injective p
  nonempty : IsNonempty p

/-- An algebraic atom; both its row and column closures are injective. -/
structure IsAtom (a : X ⟶ Y) : Prop where
  row : a ≫ (⊤ : Y ⟶ Y) ≫ aᵒ ≤ 𝟙 X
  column : aᵒ ≫ (⊤ : X ⟶ X) ≫ a ≤ 𝟙 Y
  nonempty : IsNonempty a

theorem IsNonempty.mono {f g : X ⟶ Y} (hf : IsNonempty f) (h : f ≤ g) : IsNonempty g :=
  fun P Q ↦ (hf P Q).trans (comp_mono_right (comp_mono_left h _) _)

theorem IsNonempty.dom {f : X ⟶ Y} (h : IsNonempty f) : IsNonemptyObject X := by
  intro P Q
  simpa using (h P Q).trans (comp_mono_right (le_top : f ≫ (⊤ : Y ⟶ Q) ≤ ⊤) _)

theorem IsNonempty.cod {f : X ⟶ Y} (h : IsNonempty f) : IsNonemptyObject Y := by
  intro P Q
  simpa [Category.assoc] using (h P Q).trans (by
    rw [← Category.assoc]
    exact comp_mono_left le_top (⊤ : Y ⟶ Q))

theorem IsNonempty.converse {f : X ⟶ Y} (h : IsNonempty f) : IsNonempty fᵒ := by
  intro P Q
  simpa [Category.assoc] using converse_mono (h Q P)

theorem top_comp_top (hY : IsNonemptyObject Y) :
    (⊤ : X ⟶ Y) ≫ (⊤ : Y ⟶ Z) = ⊤ :=
  le_antisymm le_top (by simpa using hY X Z)

theorem Surjective.top_comp {f : X ⟶ Y} (h : Surjective f) (W : C) :
    (⊤ : W ⟶ X) ≫ f = ⊤ := by
  refine le_antisymm le_top ?_
  calc (⊤ : W ⟶ Y) = (⊤ : W ⟶ Y) ≫ 𝟙 Y := by simp
    _ ≤ (⊤ : W ⟶ Y) ≫ fᵒ ≫ f := comp_mono_right h _
    _ ≤ (⊤ : W ⟶ X) ≫ f := by
      rw [← Category.assoc]
      exact comp_mono_left le_top _

theorem surjective_of_top_le {f : X ⟶ Y} (h : (⊤ : Y ⟶ Y) ≤ (⊤ : Y ⟶ X) ≫ f) :
    Surjective f := by
  calc 𝟙 Y ≤ ((⊤ : Y ⟶ X) ≫ f) ⊓ 𝟙 Y := le_inf (le_top.trans h) le_rfl
    _ ≤ ((⊤ : Y ⟶ X) ⊓ (𝟙 Y ≫ fᵒ)) ≫ f := modular _ _ _
    _ = fᵒ ≫ f := by simp

theorem Total.comp_top {f : X ⟶ Y} (h : Total f) (W : C) :
    f ≫ (⊤ : Y ⟶ W) = ⊤ := by
  simpa using congrArg converse (((surjective_converse_iff f).mpr h).top_comp W)

theorem total_of_top_le {f : X ⟶ Y} (h : (⊤ : X ⟶ X) ≤ f ≫ (⊤ : Y ⟶ X)) : Total f := by
  apply (surjective_converse_iff f).mp
  apply surjective_of_top_le
  simpa using converse_mono h

theorem IsVector.comp_le {f : X ⟶ Y} (h : IsVector f) (g : Y ⟶ Y) : f ≫ g ≤ f :=
  (comp_mono_right le_top f).trans_eq h

theorem isVector_comp_top (f : X ⟶ Y) : IsVector (f ≫ (⊤ : Y ⟶ Y)) := by
  simp [IsVector, Category.assoc]

theorem IsVector.inf {f g : X ⟶ Y} (hf : IsVector f) (hg : IsVector g) :
    IsVector (f ⊓ g) := by
  refine le_antisymm (le_inf ?_ ?_) (le_comp_top _)
  · exact (comp_mono_left inf_le_left _).trans_eq hf
  · exact (comp_mono_left inf_le_right _).trans_eq hg

theorem IsVector.surjective {f : X ⟶ Y} (hv : IsVector f) (hn : IsNonempty f) :
    Surjective f := by
  apply surjective_of_top_le
  simpa only [show f ≫ (⊤ : Y ⟶ Y) = f from hv] using hn Y Y

theorem IsPoint.surjective {p : X ⟶ Y} (h : IsPoint p) : Surjective p :=
  h.vector.surjective h.nonempty

theorem IsPoint.converse_isMap {p : X ⟶ Y} (h : IsPoint p) : IsMap pᵒ :=
  ⟨(functional_converse_iff _).mpr h.injective, (total_converse_iff _).mpr h.surjective⟩

/-- Functional morphisms are determined by their domain and an inclusion. -/
theorem Functional.antisymm {f g : X ⟶ Y} (hg : Functional g)
    (ht : g ≫ (⊤ : Y ⟶ Y) ≤ f ≫ ⊤) (hfg : f ≤ g) : f = g := by
  refine le_antisymm hfg ?_
  calc g ≤ (f ≫ (⊤ : Y ⟶ Y)) ⊓ g := le_inf ((le_comp_top g).trans ht) le_rfl
    _ ≤ f ≫ ((⊤ : Y ⟶ Y) ⊓ fᵒ ≫ g) := comp_inf_le_comp_inf _ _ _
    _ ≤ f ≫ gᵒ ≫ g := comp_mono_right (inf_le_right.trans
      (comp_mono_left (converse_mono hfg) _)) _
    _ ≤ f ≫ 𝟙 Y := comp_mono_right hg _
    _ = f := by simp

theorem Surjective.eq_of_le_injective {f g : X ⟶ Y} (hf : Surjective f)
    (hg : Injective g) (hfg : f ≤ g) : f = g := by
  apply converse_injective
  apply ((functional_converse_iff _).mpr hg).antisymm _ (converse_mono hfg)
  rw [← converse_le_converse_iff]
  simp only [converse_comp, converse_top, converse_converse]
  rw [hf.top_comp]
  exact le_top

/-- Points are minimal among nonempty vectors, without a bottom assumption. -/
theorem IsPoint.eq_of_nonempty_vector_le {p f : X ⟶ Y} (hp : IsPoint p)
    (hv : IsVector f) (hn : IsNonempty f) (hfp : f ≤ p) : f = p :=
  (hv.surjective hn).eq_of_le_injective hp.injective hfp

theorem IsPoint.extend {p : X ⟶ Y} (hp : IsPoint p) (hZ : IsNonemptyObject Z) :
    IsPoint (p ≫ (⊤ : Y ⟶ Z)) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [IsVector, Category.assoc]
  · calc (p ≫ (⊤ : Y ⟶ Z)) ≫ (p ≫ (⊤ : Y ⟶ Z))ᵒ =
          p ≫ ((⊤ : Y ⟶ Z) ≫ (⊤ : Z ⟶ Y)) ≫ pᵒ := by simp [Category.assoc]
         _ ≤ (p ≫ (⊤ : Y ⟶ Y)) ≫ pᵒ := by
           simpa [Category.assoc] using comp_mono_right
             (comp_mono_left (le_top : (⊤ : Y ⟶ Z) ≫ (⊤ : Z ⟶ Y) ≤ ⊤) pᵒ) p
         _ = p ≫ pᵒ := by rw [hp.vector]
         _ ≤ 𝟙 X := hp.injective
  · intro P Q
    simpa [Category.assoc, top_comp_top hZ] using hp.nonempty P Q

theorem IsPoint.le_comp_iff {p : Y ⟶ Z} (hp : IsPoint p) (f : X ⟶ Z) (g : X ⟶ Y) :
    f ≤ g ≫ p ↔ f ≫ pᵒ ≤ g := by
  constructor
  · intro h
    calc f ≫ pᵒ ≤ (g ≫ p) ≫ pᵒ := comp_mono_left h _
      _ = g ≫ (p ≫ pᵒ) := Category.assoc _ _ _
      _ ≤ g ≫ 𝟙 Y := comp_mono_right hp.injective _
      _ = g := by simp
  · intro h
    calc f = f ≫ 𝟙 Z := by simp
      _ ≤ f ≫ pᵒ ≫ p := comp_mono_right hp.surjective _
      _ = (f ≫ pᵒ) ≫ p := (Category.assoc _ _ _).symm
      _ ≤ g ≫ p := comp_mono_left h _

theorem IsPoint.le_comp_iff_converse {p : X ⟶ Z} {q : Y ⟶ Z}
    (hp : IsPoint p) (hq : IsPoint q) (f : X ⟶ Y) : p ≤ f ≫ q ↔ q ≤ fᵒ ≫ p := by
  rw [hq.le_comp_iff, hp.le_comp_iff, ← converse_le_converse_iff]
  simp

theorem IsAtom.converse {a : X ⟶ Y} (h : IsAtom a) : IsAtom aᵒ :=
  ⟨by simpa using h.column, by simpa using h.row, h.nonempty.converse⟩

theorem IsAtom.injective {a : X ⟶ Y} (h : IsAtom a) : Injective a := by
  calc a ≫ aᵒ ≤ (a ≫ (⊤ : Y ⟶ Y)) ≫ aᵒ := comp_mono_left (le_comp_top _) _
    _ ≤ 𝟙 X := by simpa [Category.assoc] using h.row

theorem IsAtom.functional {a : X ⟶ Y} (h : IsAtom a) : Functional a :=
  (injective_converse_iff _).mp h.converse.injective

theorem IsAtom.row_isPoint {a : X ⟶ Y} (h : IsAtom a) :
    IsPoint (a ≫ (⊤ : Y ⟶ Y)) := by
  refine ⟨isVector_comp_top a, ?_, h.nonempty.mono (le_comp_top _)⟩
  change (a ≫ (⊤ : Y ⟶ Y)) ≫ (a ≫ (⊤ : Y ⟶ Y))ᵒ ≤ 𝟙 X
  simp only [converse_comp, converse_top, Category.assoc]
  rw [← Category.assoc (⊤ : Y ⟶ Y), top_comp_top_left]
  exact h.row

theorem IsAtom.column_isPoint {a : X ⟶ Y} (h : IsAtom a) :
    IsPoint (aᵒ ≫ (⊤ : X ⟶ X)) := h.converse.row_isPoint

private theorem points_sandwich {p : X ⟶ Y} {q : Z ⟶ Y}
    (hp : IsPoint p) (hq : IsPoint q) :
    p ≫ qᵒ ≫ (⊤ : Z ⟶ Z) ≫ q ≫ pᵒ ≤ 𝟙 X := by
  have hq' : qᵒ ≫ (⊤ : Z ⟶ Y) = ⊤ := by
    simpa using congrArg converse (hq.surjective.top_comp Y)
  have hp' : (⊤ : Y ⟶ Y) ≫ pᵒ = pᵒ := by
    simpa using congrArg converse hp.vector
  calc p ≫ qᵒ ≫ (⊤ : Z ⟶ Z) ≫ q ≫ pᵒ = p ≫ pᵒ := by
         rw [← Category.assoc (⊤ : Z ⟶ Z), hq.surjective.top_comp,
           ← Category.assoc qᵒ, hq', hp']
       _ ≤ 𝟙 X := hp.injective

theorem isAtom_of_points {p : X ⟶ Y} {q : Z ⟶ Y}
    (hp : IsPoint p) (hq : IsPoint q) : IsAtom (p ≫ qᵒ) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [Category.assoc] using points_sandwich hp hq
  · simpa [Category.assoc] using points_sandwich hq hp
  · intro P Q
    simpa [← Category.assoc, hp.surjective.top_comp] using hq.nonempty.converse P Q

theorem IsAtom.row_inf_column {a : X ⟶ Y} (h : IsAtom a) :
    (a ≫ (⊤ : Y ⟶ Y)) ⊓ ((⊤ : X ⟶ X) ≫ a) = a := by
  refine le_antisymm ?_ (le_inf (le_comp_top _) (le_top_comp _))
  calc (a ≫ (⊤ : Y ⟶ Y)) ⊓ ((⊤ : X ⟶ X) ≫ a) ≤
        a ≫ ((⊤ : Y ⟶ Y) ⊓ aᵒ ≫ (⊤ : X ⟶ X) ≫ a) := comp_inf_le_comp_inf _ _ _
    _ ≤ a ≫ 𝟙 Y := comp_mono_right (inf_le_right.trans h.column) _
    _ = a := by simp

theorem IsAtom.comp_top_comp {a : X ⟶ Y} (h : IsAtom a) :
    a ≫ (⊤ : Y ⟶ X) ≫ a = a := by
  refine le_antisymm ?_ ?_
  · apply le_trans (b := (a ≫ (⊤ : Y ⟶ Y)) ⊓ ((⊤ : X ⟶ X) ≫ a))
    · refine le_inf (comp_mono_right le_top _) ?_
      rw [← Category.assoc]
      exact comp_mono_left le_top _
    · exact h.row_inf_column.le
  · exact (le_comp_converse_comp a).trans (comp_mono_right (comp_mono_left le_top _) _)

theorem IsAtom.transitive {a : X ⟶ X} (h : IsAtom a) : IsTransitive a := by
  calc a ≫ a ≤ a ≫ (⊤ : X ⟶ X) ≫ a := comp_mono_right (le_top_comp a) a
    _ = a := h.comp_top_comp

theorem IsAtom.comp_self_le_id {a : X ⟶ X} (h : IsAtom a) : a ≫ a ≤ 𝟙 X := by
  calc a ≫ a ≤ (a ≫ a) ⊓ a := le_inf le_rfl h.transitive
    _ ≤ (a ⊓ a ≫ aᵒ) ≫ (a ⊓ aᵒ ≫ a) := dedekind _ _ _
    _ ≤ (𝟙 X) ≫ 𝟙 X := comp_le_comp
      (inf_le_right.trans h.injective) (inf_le_right.trans h.functional)
    _ = 𝟙 X := by simp

/-- Every atom factors as two points over any nonempty common target. -/
theorem IsAtom.exists_points {a : X ⟶ Y} (h : IsAtom a) (hZ : IsNonemptyObject Z) :
    ∃ (p : X ⟶ Z) (q : Y ⟶ Z), IsPoint p ∧ IsPoint q ∧ a = p ≫ qᵒ := by
  refine ⟨a ≫ ⊤, aᵒ ≫ ⊤, ?_, ?_, ?_⟩
  · simpa [Category.assoc] using h.row_isPoint.extend hZ
  · simpa [Category.assoc] using h.column_isPoint.extend hZ
  · simp only [converse_comp, converse_top, converse_converse, Category.assoc]
    rw [← Category.assoc (⊤ : Y ⟶ Z), top_comp_top hZ, h.comp_top_comp]

/-- Algebraic atoms are minimal among nonempty morphisms. -/
theorem IsAtom.eq_of_nonempty_le {a f : X ⟶ Y} (h : IsAtom a)
    (hf : IsNonempty f) (hfa : f ≤ a) : f = a := by
  apply h.functional.antisymm _ hfa
  exact (h.row_isPoint.eq_of_nonempty_vector_le (isVector_comp_top f)
    (hf.mono (le_comp_top f)) (comp_mono_left hfa _)).symm.le

end AllegoryCategory
