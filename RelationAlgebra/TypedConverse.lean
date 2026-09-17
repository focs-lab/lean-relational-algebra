import RelationAlgebra.Typed
import RelationAlgebra.Converse
import RelationAlgebra.Models.MatrixExt
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Typed converse

A converse reverses the endpoints of a morphism. Its three axioms are involution,
additivity, and reversal of composition; preservation of identity, bottom, order, and
Kleene star follows. This is the Kleene-algebra-with-converse fragment of Damien Pous'
`kleene.v`, without the additional Boolean or Dedekind axioms of relation algebra.

The models are heterogeneous relations and rectangular matrices. Matrix converse is
**conjugate transpose**: transpose alone does not reverse products over noncommutative
coefficients. On endomorphisms the interface agrees with Mathlib's `StarRing`.
-/

open CategoryTheory
open scoped Computability

universe u v

/-- A Kleene category with an additive, composition-reversing involution. -/
class KleeneCategoryWithConverse (C : Type u) [Category.{v} C] [KleeneCategory C] where
  /-- Reverse the endpoints of a morphism. -/
  converse {X Y : C} : (X ⟶ Y) → (Y ⟶ X)
  converse_converse {X Y : C} (f : X ⟶ Y) : converse (converse f) = f
  converse_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    converse (f ≫ g) = converse g ≫ converse f
  converse_sup {X Y : C} (f g : X ⟶ Y) :
    converse (f ⊔ g) = converse f ⊔ converse g

namespace KleeneCategoryWithConverse

scoped postfix:max "ᵒ" => converse
attribute [simp] converse_converse converse_comp converse_sup

variable {C : Type u} [Category.{v} C] [KleeneCategory C]
  [KleeneCategoryWithConverse C] {X Y : C}

@[simp] theorem converse_id (X : C) : converse (𝟙 X) = 𝟙 X := by
  have h := congrArg converse (Category.id_comp (converse (𝟙 X)))
  rw [converse_comp, converse_converse, Category.id_comp] at h
  exact h

@[gcongr] theorem converse_mono {f g : X ⟶ Y} (h : f ≤ g) : converse f ≤ converse g := by
  apply sup_eq_right.mp
  rw [← converse_sup, sup_eq_right.mpr h]

@[simp] theorem converse_le_converse_iff {f g : X ⟶ Y} :
    converse f ≤ converse g ↔ f ≤ g :=
  ⟨fun h ↦ by simpa using converse_mono h, converse_mono⟩

@[simp] theorem converse_bot : converse (⊥ : X ⟶ Y) = ⊥ := by
  apply le_antisymm _ bot_le
  simpa using converse_mono (bot_le : (⊥ : X ⟶ Y) ≤ converse (⊥ : Y ⟶ X))

@[simp] theorem converse_eqToHom {X Y : C} (h : X = Y) :
    converse (eqToHom h) = eqToHom h.symm := by
  subst Y
  simp

instance instStarEnd : Star (End X) := ⟨converse⟩

instance instStarRingEnd : StarRing (End X) where
  star_involutive := converse_converse
  star_mul f g := converse_comp g f
  star_add := converse_sup

@[simp] theorem star_end (f : End X) : star f = converse f := rfl

@[simp] theorem converse_kstar (f : X ⟶ X) : converse (f∗) = (converse f)∗ :=
  KleeneAlgebra.star_kstar (K := End X) f

end KleeneCategoryWithConverse

namespace CategoryTheory.SingleObj

instance instKleeneCategoryWithConverse {K : Type u} [KleeneAlgebra K] [StarRing K] :
    KleeneCategoryWithConverse (SingleObj K) where
  converse := Star.star
  converse_converse := star_star
  converse_comp f g := star_mul g f
  converse_sup := KleeneAlgebra.star_sup

@[simp] theorem converse_as_star {K : Type u} [KleeneAlgebra K] [StarRing K]
    (f : (SingleObj.star K) ⟶ (SingleObj.star K)) :
    KleeneCategoryWithConverse.converse f = Star.star (f : K) := rfl

end CategoryTheory.SingleObj

namespace CategoryTheory.RelCat

instance instKleeneCategoryWithConverse : KleeneCategoryWithConverse RelCat.{u} where
  converse f := .ofRel f.rel.inv
  converse_converse f := by ext ⟨x, y⟩; rfl
  converse_comp f g := by
    ext ⟨x, y⟩
    change (∃ z, _ ∧ _) ↔ (∃ z, _ ∧ _)
    exact exists_congr fun _ ↦ and_comm
  converse_sup f g := by ext ⟨x, y⟩; rfl

@[simp] theorem Hom.rel_converse {X Y : RelCat.{u}} (f : X ⟶ Y) :
    (KleeneCategoryWithConverse.converse f).rel = f.rel.inv := rfl

end CategoryTheory.RelCat

namespace Matrix.Mat

noncomputable instance instKleeneCategoryWithConverse {K : Type u}
    [KleeneAlgebra K] [StarRing K] : KleeneCategoryWithConverse (Mat K) where
  converse := Matrix.conjTranspose
  converse_converse := Matrix.conjTranspose_conjTranspose
  converse_comp := Matrix.conjTranspose_mul
  converse_sup {X Y} f g := by
    apply Matrix.ext
    intro i j
    exact KleeneAlgebra.star_sup (f j i) (g j i)

@[simp] theorem converse_as_conjTranspose {K : Type u} [KleeneAlgebra K] [StarRing K]
    {X Y : Mat K} (f : X ⟶ Y) :
    KleeneCategoryWithConverse.converse f = f.conjTranspose := rfl

end Matrix.Mat
