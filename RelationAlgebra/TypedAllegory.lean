/- SPDX-License-Identifier: LGPL-3.0-or-later
Lean translation and extensions, 2026-09-18. See LICENSE and NOTICE.md. -/
import RelationAlgebra.Allegory
import RelationAlgebra.TypedBoolean

/-!
# Allegory categories and typed relational predicates

The heterogeneous allegory fragment of Damien Pous's `monoid.v` and `relalg.v`:
meet-enriched categories with a composition-reversing involution and the modular law.
The interface does not assume joins, bottom, complements, residuals, or Kleene star.
`RelationCategory` supplies an instance by forgetting its extra structure.

Composition is in execution order. Thus `Functional f` says `fᵒ ≫ f ≤ 𝟙 _`.
Mathlib's `End` and `SingleObj` reverse multiplication, so their scalar compatibility
exchanges functional with injective, and total with surjective.
-/

open CategoryTheory
universe u v

/-- A category enriched in meet semilattices, with converse and the modular law. -/
class AllegoryCategory (C : Type u) [Category.{v} C] where
  [homSemilatticeInf : ∀ X Y : C, SemilatticeInf (X ⟶ Y)]
  converse {X Y : C} : (X ⟶ Y) → (Y ⟶ X)
  converse_converse {X Y : C} (f : X ⟶ Y) : converse (converse f) = f
  converse_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    converse (f ≫ g) = converse g ≫ converse f
  converse_inf {X Y : C} (f g : X ⟶ Y) :
    converse (f ⊓ g) = converse f ⊓ converse g
  comp_mono_left {X Y Z : C} {f g : X ⟶ Y} (hfg : f ≤ g) (h : Y ⟶ Z) :
    f ≫ h ≤ g ≫ h
  comp_mono_right {X Y Z : C} {g h : Y ⟶ Z} (hgh : g ≤ h) (f : X ⟶ Y) :
    f ≫ g ≤ f ≫ h
  modular {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) :
    (f ≫ g) ⊓ h ≤ (f ⊓ h ≫ converse g) ≫ g

attribute [instance_reducible, instance 100] AllegoryCategory.homSemilatticeInf

namespace AllegoryCategory

scoped postfix:max "ᵒ" => converse
attribute [simp] converse_converse converse_comp converse_inf

variable {C : Type u} [Category.{v} C] [AllegoryCategory C] {W X Y Z : C}

@[gcongr] theorem comp_le_comp {f g : X ⟶ Y} {h k : Y ⟶ Z}
    (hfg : f ≤ g) (hhk : h ≤ k) : f ≫ h ≤ g ≫ k :=
  (comp_mono_left hfg h).trans (comp_mono_right hhk g)

@[gcongr] theorem converse_mono {f g : X ⟶ Y} (h : f ≤ g) : fᵒ ≤ gᵒ := by
  rw [← inf_eq_left, ← converse_inf, inf_eq_left.mpr h]

@[simp] theorem converse_le_converse_iff {f g : X ⟶ Y} : fᵒ ≤ gᵒ ↔ f ≤ g :=
  ⟨fun h ↦ by simpa using converse_mono h, converse_mono⟩

theorem converse_le_iff {f : X ⟶ Y} {g : Y ⟶ X} : fᵒ ≤ g ↔ f ≤ gᵒ := by
  rw [← converse_le_converse_iff, converse_converse]

@[simp] theorem converse_id (X : C) : (𝟙 X)ᵒ = 𝟙 X := by
  have h := congrArg converse (Category.id_comp ((𝟙 X)ᵒ))
  rw [converse_comp, converse_converse, Category.id_comp] at h
  exact h

theorem converse_injective : Function.Injective (converse : (X ⟶ Y) → (Y ⟶ X)) :=
  fun _ _ h ↦ by simpa using congrArg converse h

/-- The other modular law, obtained by converse. -/
theorem comp_inf_le_comp_inf (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) :
    (f ≫ g) ⊓ h ≤ f ≫ (g ⊓ fᵒ ≫ h) := by
  simpa using converse_mono (modular gᵒ fᵒ hᵒ)

/-- The full Dedekind inequality follows from the one-sided modular law. -/
theorem dedekind (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) :
    (f ≫ g) ⊓ h ≤ (f ⊓ h ≫ gᵒ) ≫ (g ⊓ fᵒ ≫ h) := by
  calc (f ≫ g) ⊓ h ≤ ((f ⊓ h ≫ gᵒ) ≫ g) ⊓ h := le_inf (modular f g h) inf_le_right
    _ ≤ (f ⊓ h ≫ gᵒ) ≫ (g ⊓ (f ⊓ h ≫ gᵒ)ᵒ ≫ h) := comp_inf_le_comp_inf _ _ _
    _ ≤ (f ⊓ h ≫ gᵒ) ≫ (g ⊓ fᵒ ≫ h) :=
      comp_mono_right (inf_le_inf_left _ (comp_mono_left (converse_mono inf_le_left) _)) _

theorem le_comp_converse_comp (f : X ⟶ Y) : f ≤ f ≫ fᵒ ≫ f := by
  calc f = (f ≫ 𝟙 Y) ⊓ f := by simp
    _ ≤ f ≫ (𝟙 Y ⊓ fᵒ ≫ f) := comp_inf_le_comp_inf _ _ _
    _ ≤ f ≫ fᵒ ≫ f := comp_mono_right inf_le_right _

/-- A relation is functional (upstream: univalent) when each input has at most one output. -/
def Functional (f : X ⟶ Y) : Prop := fᵒ ≫ f ≤ 𝟙 Y
/-- Every input has an output. -/
def Total (f : X ⟶ Y) : Prop := 𝟙 X ≤ f ≫ fᵒ
/-- Each output has at most one input. -/
def Injective (f : X ⟶ Y) : Prop := f ≫ fᵒ ≤ 𝟙 X
/-- Every output has an input. -/
def Surjective (f : X ⟶ Y) : Prop := 𝟙 Y ≤ fᵒ ≫ f
/-- A total, functional morphism. -/
structure IsMap (f : X ⟶ Y) : Prop where
  functional : Functional f
  total : Total f

@[simp] theorem functional_converse_iff (f : X ⟶ Y) : Functional fᵒ ↔ Injective f := by
  simp [Functional, Injective]
@[simp] theorem injective_converse_iff (f : X ⟶ Y) : Injective fᵒ ↔ Functional f := by
  simp [Functional, Injective]
@[simp] theorem total_converse_iff (f : X ⟶ Y) : Total fᵒ ↔ Surjective f := by
  simp [Total, Surjective]
@[simp] theorem surjective_converse_iff (f : X ⟶ Y) : Surjective fᵒ ↔ Total f := by
  simp [Total, Surjective]

@[simp] theorem functional_id (X : C) : Functional (𝟙 X) := by simp [Functional]
@[simp] theorem total_id (X : C) : Total (𝟙 X) := by simp [Total]
@[simp] theorem injective_id (X : C) : Injective (𝟙 X) := by simp [Injective]
@[simp] theorem surjective_id (X : C) : Surjective (𝟙 X) := by simp [Surjective]
theorem isMap_id (X : C) : IsMap (𝟙 X) := ⟨functional_id X, total_id X⟩

theorem Functional.comp {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : Functional f) (hg : Functional g) : Functional (f ≫ g) := by
  unfold Functional at *
  calc (f ≫ g)ᵒ ≫ (f ≫ g) = gᵒ ≫ (fᵒ ≫ f) ≫ g := by simp [Category.assoc]
    _ ≤ gᵒ ≫ 𝟙 Y ≫ g := comp_mono_right (comp_mono_left hf _) _
    _ ≤ 𝟙 Z := by simpa using hg

theorem Injective.comp {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : Injective f) (hg : Injective g) : Injective (f ≫ g) := by
  apply (functional_converse_iff _).mp
  simpa using ((functional_converse_iff g).mpr hg).comp ((functional_converse_iff f).mpr hf)

theorem Total.comp {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : Total f) (hg : Total g) : Total (f ≫ g) := by
  unfold Total at *
  calc 𝟙 X ≤ f ≫ fᵒ := hf
    _ = f ≫ 𝟙 Y ≫ fᵒ := by simp
    _ ≤ f ≫ (g ≫ gᵒ) ≫ fᵒ := comp_mono_right (comp_mono_left hg _) _
    _ = (f ≫ g) ≫ (f ≫ g)ᵒ := by simp [Category.assoc]

theorem Surjective.comp {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : Surjective f) (hg : Surjective g) : Surjective (f ≫ g) := by
  apply (total_converse_iff _).mp
  simpa using ((total_converse_iff g).mpr hg).comp ((total_converse_iff f).mpr hf)

theorem IsMap.comp {f : X ⟶ Y} {g : Y ⟶ Z} (hf : IsMap f) (hg : IsMap g) : IsMap (f ≫ g) :=
  ⟨hf.functional.comp hg.functional, hf.total.comp hg.total⟩

theorem Functional.mono {f g : X ⟶ Y} (hg : Functional g) (h : f ≤ g) : Functional f :=
  (comp_le_comp (converse_mono h) h).trans hg

theorem Injective.mono {f g : X ⟶ Y} (hg : Injective g) (h : f ≤ g) : Injective f :=
  (comp_le_comp h (converse_mono h)).trans hg

theorem Total.mono {f g : X ⟶ Y} (hf : Total f) (h : f ≤ g) : Total g :=
  hf.trans (comp_le_comp h (converse_mono h))

theorem Surjective.mono {f g : X ⟶ Y} (hf : Surjective f) (h : f ≤ g) : Surjective g :=
  hf.trans (comp_le_comp (converse_mono h) h)

/-- Functional morphisms distribute over intersection of subsequent morphisms. -/
theorem Functional.comp_inf {f : X ⟶ Y} (hf : Functional f) (g h : Y ⟶ Z) :
    f ≫ (g ⊓ h) = (f ≫ g) ⊓ (f ≫ h) := by
  refine le_antisymm (le_inf (comp_mono_right inf_le_left _) (comp_mono_right inf_le_right _)) ?_
  calc (f ≫ g) ⊓ (f ≫ h) ≤ f ≫ (g ⊓ fᵒ ≫ f ≫ h) := comp_inf_le_comp_inf _ _ _
    _ ≤ f ≫ (g ⊓ 𝟙 Y ≫ h) := by
      exact comp_mono_right (inf_le_inf_left _ (by
        simpa [Category.assoc] using comp_mono_left hf h)) _
    _ = f ≫ (g ⊓ h) := by simp

/-- Injective morphisms distribute over intersection of preceding morphisms. -/
theorem Injective.inf_comp {f : Y ⟶ Z} (hf : Injective f) (g h : X ⟶ Y) :
    (g ⊓ h) ≫ f = (g ≫ f) ⊓ (h ≫ f) := by
  apply converse_injective
  simpa using ((functional_converse_iff f).mpr hf).comp_inf gᵒ hᵒ

theorem Injective.comp_inf_eq {f : X ⟶ Y} (hf : Injective f) (g : Y ⟶ Z) (h : X ⟶ Z) :
    (f ≫ g) ⊓ h = f ≫ (g ⊓ fᵒ ≫ h) := by
  refine le_antisymm (comp_inf_le_comp_inf _ _ _) (le_inf (comp_mono_right inf_le_left _) ?_)
  calc f ≫ (g ⊓ fᵒ ≫ h) ≤ f ≫ fᵒ ≫ h := comp_mono_right inf_le_right _
    _ = (f ≫ fᵒ) ≫ h := (Category.assoc _ _ _).symm
    _ ≤ 𝟙 X ≫ h := comp_mono_left hf _
    _ = h := by simp

theorem Functional.inf_comp_eq {f : Y ⟶ Z} (hf : Functional f) (g : X ⟶ Y) (h : X ⟶ Z) :
    (g ≫ f) ⊓ h = (g ⊓ h ≫ fᵒ) ≫ f := by
  apply converse_injective
  simpa using ((injective_converse_iff f).mpr hf).comp_inf_eq gᵒ hᵒ

/-- Subidentities compose by intersection, without Boolean or Kleene structure. -/
theorem comp_eq_inf_of_le_id (f g : X ⟶ X) (hf : f ≤ 𝟙 X) (hg : g ≤ 𝟙 X) :
    f ≫ g = f ⊓ g := by
  refine le_antisymm (le_inf (by simpa using comp_mono_right hg f)
    (by simpa using comp_mono_left hf g)) ?_
  calc f ⊓ g = (f ≫ 𝟙 X) ⊓ g := by simp
    _ ≤ f ≫ (𝟙 X ⊓ fᵒ ≫ g) := comp_inf_le_comp_inf _ _ _
    _ ≤ f ≫ g := comp_mono_right (inf_le_right.trans (by
      simpa using comp_mono_left (converse_mono hf) g)) _

/-- An endomorphism contains the identity. -/
def IsReflexive (f : X ⟶ X) : Prop := 𝟙 X ≤ f
/-- An endomorphism is closed under composition. -/
def IsTransitive (f : X ⟶ X) : Prop := f ≫ f ≤ f
/-- An endomorphism equals its converse. -/
def IsSymmetric (f : X ⟶ X) : Prop := fᵒ = f
/-- Oppositely directed edges meet only on the identity. -/
def IsAntisymmetric (f : X ⟶ X) : Prop := f ⊓ fᵒ ≤ 𝟙 X

structure IsPer (f : X ⟶ X) : Prop where
  symmetric : IsSymmetric f
  transitive : IsTransitive f

structure IsPreorder (f : X ⟶ X) : Prop where
  reflexive : IsReflexive f
  transitive : IsTransitive f

structure IsOrder (f : X ⟶ X) : Prop where
  isPreorder : IsPreorder f
  antisymmetric : IsAntisymmetric f

theorem isSymmetric_iff {f : X ⟶ X} : IsSymmetric f ↔ fᵒ ≤ f :=
  ⟨fun h ↦ h.le, fun h ↦ h.antisymm (by simpa using converse_mono h)⟩

theorem IsReflexive.converse {f : X ⟶ X} (h : IsReflexive f) : IsReflexive fᵒ := by
  simpa [IsReflexive] using converse_mono h

theorem IsTransitive.converse {f : X ⟶ X} (h : IsTransitive f) : IsTransitive fᵒ := by
  simpa [IsTransitive] using converse_mono h

theorem IsSymmetric.converse {f : X ⟶ X} (h : IsSymmetric f) : IsSymmetric fᵒ := by
  simpa [IsSymmetric] using congrArg AllegoryCategory.converse h

theorem IsAntisymmetric.converse {f : X ⟶ X} (h : IsAntisymmetric f) : IsAntisymmetric fᵒ := by
  simpa [IsAntisymmetric, inf_comm] using h

theorem IsPer.converse {f : X ⟶ X} (h : IsPer f) : IsPer fᵒ :=
  ⟨h.symmetric.converse, h.transitive.converse⟩

theorem IsPreorder.converse {f : X ⟶ X} (h : IsPreorder f) : IsPreorder fᵒ :=
  ⟨h.reflexive.converse, h.transitive.converse⟩

theorem IsOrder.converse {f : X ⟶ X} (h : IsOrder f) : IsOrder fᵒ :=
  ⟨h.isPreorder.converse, h.antisymmetric.converse⟩

theorem IsSymmetric.inf {f g : X ⟶ X} (hf : IsSymmetric f) (hg : IsSymmetric g) :
    IsSymmetric (f ⊓ g) := by
  change (f ⊓ g)ᵒ = f ⊓ g
  rw [converse_inf, show fᵒ = f from hf, show gᵒ = g from hg]

theorem IsReflexive.inf {f g : X ⟶ X} (hf : IsReflexive f) (hg : IsReflexive g) :
    IsReflexive (f ⊓ g) := le_inf hf hg

theorem IsTransitive.inf {f g : X ⟶ X} (hf : IsTransitive f) (hg : IsTransitive g) :
    IsTransitive (f ⊓ g) :=
  le_inf ((comp_le_comp inf_le_left inf_le_left).trans hf)
    ((comp_le_comp inf_le_right inf_le_right).trans hg)

theorem IsAntisymmetric.inf_left {f g : X ⟶ X} (hf : IsAntisymmetric f) :
    IsAntisymmetric (f ⊓ g) :=
  (inf_le_inf inf_le_left (converse_mono inf_le_left)).trans hf

theorem kernel_eq_id {f : X ⟶ X} (hr : IsReflexive f) (ha : IsAntisymmetric f) :
    f ⊓ fᵒ = 𝟙 X := ha.antisymm (le_inf hr hr.converse)

section Bottom
variable [∀ X Y : C, OrderBot (X ⟶ Y)]

/-- An endomorphism has no identity edges. -/
def IsIrreflexive (f : X ⟶ X) : Prop := f ⊓ 𝟙 X = ⊥

@[simp] theorem converse_bot : (⊥ : X ⟶ Y)ᵒ = ⊥ :=
  le_antisymm (converse_le_iff.mpr bot_le) bot_le

theorem IsIrreflexive.converse {f : X ⟶ X} (h : IsIrreflexive f) : IsIrreflexive fᵒ := by
  simpa [IsIrreflexive] using congrArg AllegoryCategory.converse h

end Bottom

end AllegoryCategory

/-- Forget the stronger Boolean and Kleene structure of a relation category. -/
instance (priority := 100) RelationCategory.toAllegoryCategory {C : Type u} [Category.{v} C]
    [KleeneCategory C] [BooleanKleeneCategory C] [KleeneCategoryWithConverse C]
    [RelationCategory C] : AllegoryCategory C where
  homSemilatticeInf _ _ := inferInstance
  converse := KleeneCategoryWithConverse.converse
  converse_converse := KleeneCategoryWithConverse.converse_converse
  converse_comp := KleeneCategoryWithConverse.converse_comp
  converse_inf := KleeneCategoryWithConverse.converse_inf
  comp_mono_left := KleeneCategory.comp_le_comp_left
  comp_mono_right := KleeneCategory.comp_le_comp_right
  modular := RelationCategory.comp_inf_le_inf_comp

namespace CategoryTheory.SingleObj

instance (priority := 200) instAllegoryCategory {K : Type u} [Allegory K] :
    AllegoryCategory (SingleObj K) where
  homSemilatticeInf _ _ := inferInstanceAs (SemilatticeInf K)
  converse := Star.star
  converse_converse := Allegory.star_star
  converse_comp f g := Allegory.star_mul g f
  converse_inf := Allegory.star_inf
  comp_mono_left h g := Allegory.mul_mono_right h g
  comp_mono_right h f := Allegory.mul_mono_left h f
  modular f g h := Allegory.mul_inf_le_mul_inf g f h

end CategoryTheory.SingleObj

namespace CategoryTheory.End

variable {C : Type u} [Category.{v} C] [AllegoryCategory C] {X : C}

/-- Endomorphisms recover a scalar allegory; multiplication reverses execution order. -/
instance (priority := 100) instAllegory : Allegory (End X) where
  toSemilatticeInf := AllegoryCategory.homSemilatticeInf X X
  toMonoid := inferInstance
  star := AllegoryCategory.converse
  star_involutive := AllegoryCategory.converse_converse
  star_mul f g := AllegoryCategory.converse_comp g f
  star_inf := AllegoryCategory.converse_inf
  mul_mono_left h g := AllegoryCategory.comp_mono_right h g
  mul_mono_right h f := AllegoryCategory.comp_mono_left h f
  modular f g h := AllegoryCategory.comp_inf_le_comp_inf g f h

end CategoryTheory.End

namespace AllegoryCategory

variable {C : Type u} [Category.{v} C] [AllegoryCategory C] {X : C}

@[simp] theorem functional_end_iff (f : End X) :
    Allegory.Functional f ↔ Injective (show X ⟶ X from f) := Iff.rfl
@[simp] theorem injective_end_iff (f : End X) :
    Allegory.Injective f ↔ Functional (show X ⟶ X from f) := Iff.rfl
@[simp] theorem total_end_iff (f : End X) :
    Allegory.Total f ↔ Surjective (show X ⟶ X from f) := Iff.rfl
@[simp] theorem surjective_end_iff (f : End X) :
    Allegory.Surjective f ↔ Total (show X ⟶ X from f) := Iff.rfl

end AllegoryCategory

namespace CategoryTheory.RelCat

open AllegoryCategory

variable {X Y : RelCat.{u}} {f : X ⟶ Y}

@[simp] theorem Hom.rel_allegoryConverse (f : X ⟶ Y) :
    (AllegoryCategory.converse f).rel = f.rel.inv := rfl

theorem functional_iff : Functional f ↔ ∀ x y z, (x, y) ∈ f.rel → (x, z) ∈ f.rel → y = z := by
  constructor
  · intro h x y z hxy hxz
    exact h (a := (y, z)) ⟨x, hxy, hxz⟩
  · intro h ⟨y, z⟩ ⟨x, hxy, hxz⟩
    exact h x y z hxy hxz

theorem total_iff : Total f ↔ ∀ x, ∃ y, (x, y) ∈ f.rel := by
  constructor
  · intro h x
    obtain ⟨y, hxy, _⟩ := h (a := (x, x)) rfl
    exact ⟨y, hxy⟩
  · rintro h ⟨x, x'⟩ (he : x = x')
    obtain ⟨y, hxy⟩ := h x
    exact ⟨y, hxy, he ▸ hxy⟩

theorem injective_iff : Injective f ↔ ∀ x y z, (x, z) ∈ f.rel → (y, z) ∈ f.rel → x = y := by
  constructor
  · intro h x y z hxz hyz
    exact h (a := (x, y)) ⟨z, hxz, hyz⟩
  · intro h ⟨x, y⟩ ⟨z, hxz, hyz⟩
    exact h x y z hxz hyz

theorem surjective_iff : Surjective f ↔ ∀ y, ∃ x, (x, y) ∈ f.rel := by
  constructor
  · intro h y
    obtain ⟨x, hxy, _⟩ := h (a := (y, y)) rfl
    exact ⟨x, hxy⟩
  · rintro h ⟨y, y'⟩ (he : y = y')
    obtain ⟨x, hxy⟩ := h y
    exact ⟨x, hxy, he ▸ hxy⟩

theorem isMap_iff : IsMap f ↔ ∀ x, ∃! y, (x, y) ∈ f.rel := by
  constructor
  · intro h x
    obtain ⟨y, hxy⟩ := total_iff.mp h.total x
    exact ⟨y, hxy, fun z hxz ↦ functional_iff.mp h.functional x z y hxz hxy⟩
  · intro h
    refine ⟨functional_iff.mpr (fun x y z hxy hxz ↦ ?_), total_iff.mpr (fun x ↦ ?_)⟩
    · obtain ⟨w, _, hw⟩ := h x
      exact (hw y hxy).trans (hw z hxz).symm
    · exact ⟨(h x).choose, (h x).choose_spec.1⟩

/-- The relational graph of an ordinary function. -/
def graph (f : X → Y) : X ⟶ Y := .ofRel {xy | f xy.1 = xy.2}

@[simp] theorem graph_mem (f : X → Y) (x : X) (y : Y) :
    (x, y) ∈ (graph f).rel ↔ f x = y := Iff.rfl

theorem graph_isMap (f : X → Y) : IsMap (graph f) :=
  isMap_iff.mpr fun x ↦ ⟨f x, rfl, fun _ h ↦ h.symm⟩

theorem graph_injective_iff (f : X → Y) : Injective (graph f) ↔ Function.Injective f := by
  rw [injective_iff]
  constructor
  · intro h x y he
    exact h x y (f y) he rfl
  · intro h x y z hx hy
    exact h (hx.trans hy.symm)

theorem graph_surjective_iff (f : X → Y) : Surjective (graph f) ↔ Function.Surjective f :=
  surjective_iff

/-- Maps in the relation allegory are exactly graphs of functions. -/
theorem isMap_iff_exists_graph : IsMap f ↔ ∃ g : X → Y, graph g = f := by
  classical
  constructor
  · intro h
    let g : X → Y := fun x ↦ (isMap_iff.mp h x).choose
    refine ⟨g, ?_⟩
    ext ⟨x, y⟩
    change g x = y ↔ (x, y) ∈ f.rel
    exact ⟨fun he ↦ he ▸ (isMap_iff.mp h x).choose_spec.1,
      fun hx ↦ ((isMap_iff.mp h x).choose_spec.2 y hx).symm⟩
  · rintro ⟨g, rfl⟩
    exact graph_isMap g

end CategoryTheory.RelCat
