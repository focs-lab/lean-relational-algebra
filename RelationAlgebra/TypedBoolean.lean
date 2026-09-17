import RelationAlgebra.TypedConverse

/-!
# Boolean Kleene categories and typed relation algebra

Boolean operations live on each hom-set, using exactly the order, join, and bottom of
the existing Kleene category. `BooleanKleeneCategory` supplies the remaining operations
and laws; `RelationCategory` adds the typed Dedekind law to converse. This follows the
Boolean relation-algebra fragment of Damien Pous' `monoid.v` and `relalg.v`.

Complement is relative to the universal relation between the same two objects. It is
not the complement of a KAT test, which is relative to the identity at one object.
-/

open CategoryTheory KleeneCategoryWithConverse
open scoped Computability KleeneCategoryWithConverse

universe u v

/-- Boolean hom-sets extending the existing Kleene-category order without a second order. -/
class BooleanKleeneCategory (C : Type u) [Category.{v} C] [KleeneCategory C] where
  inf {X Y : C} : (X ⟶ Y) → (X ⟶ Y) → (X ⟶ Y)
  top {X Y : C} : X ⟶ Y
  compl {X Y : C} : (X ⟶ Y) → (X ⟶ Y)
  inf_le_left {X Y : C} (f g : X ⟶ Y) : inf f g ≤ f
  inf_le_right {X Y : C} (f g : X ⟶ Y) : inf f g ≤ g
  le_inf {X Y : C} (f g h : X ⟶ Y) : f ≤ g → f ≤ h → f ≤ inf g h
  le_sup_inf {X Y : C} (f g h : X ⟶ Y) : inf (f ⊔ g) (f ⊔ h) ≤ f ⊔ inf g h
  le_top {X Y : C} (f : X ⟶ Y) : f ≤ top
  inf_compl_le_bot {X Y : C} (f : X ⟶ Y) : inf f (compl f) ≤ ⊥
  top_le_sup_compl {X Y : C} (f : X ⟶ Y) : top ≤ f ⊔ compl f

namespace BooleanKleeneCategory

variable {C : Type u} [Category.{v} C] [KleeneCategory C] [BooleanKleeneCategory C]

/-- The Boolean algebra shares its order, join, and bottom with `KleeneCategory`. -/
instance homBooleanAlgebra {X Y : C} : BooleanAlgebra (X ⟶ Y) where
  __ := KleeneCategory.homSemilatticeSup X Y
  __ := KleeneCategory.homOrderBot X Y
  inf := inf
  top := top
  compl := compl
  inf_le_left := inf_le_left
  inf_le_right := inf_le_right
  le_inf := le_inf
  le_sup_inf := le_sup_inf
  le_top := le_top
  inf_compl_le_bot := inf_compl_le_bot
  top_le_sup_compl := top_le_sup_compl

instance endBooleanAlgebra {X : C} : BooleanAlgebra (End X) :=
  inferInstanceAs (BooleanAlgebra (X ⟶ X))

end BooleanKleeneCategory

namespace KleeneCategory

variable {C : Type u} [Category.{v} C] [KleeneCategory C] [BooleanKleeneCategory C] {X : C}

@[simp] theorem kstar_top : (⊤ : X ⟶ X)∗ = ⊤ := le_antisymm le_top (le_kstar _)

end KleeneCategory

namespace KleeneCategoryWithConverse

variable {C : Type u} [Category.{v} C] [KleeneCategory C]
  [BooleanKleeneCategory C] [KleeneCategoryWithConverse C] {X Y : C}

@[simp] theorem converse_inf (f g : X ⟶ Y) : (f ⊓ g)ᵒ = fᵒ ⊓ gᵒ := by
  have key {A B : C} (a b : A ⟶ B) : (a ⊓ b)ᵒ ≤ aᵒ ⊓ bᵒ :=
    le_inf (converse_mono inf_le_left) (converse_mono inf_le_right)
  refine (key f g).antisymm ?_
  simpa using converse_mono (key fᵒ gᵒ)

@[simp] theorem converse_top : (⊤ : X ⟶ Y)ᵒ = ⊤ := by
  apply le_antisymm le_top
  simpa using converse_mono (le_top : (⊤ : Y ⟶ X)ᵒ ≤ (⊤ : X ⟶ Y))

@[simp] theorem converse_compl (f : X ⟶ Y) : (fᶜ)ᵒ = (fᵒ)ᶜ := by
  refine (compl_unique ?_ ?_).symm
  · rw [← converse_inf, inf_compl_eq_bot, converse_bot]
  · rw [← converse_sup, sup_compl_eq_top, converse_top]

end KleeneCategoryWithConverse

/-- A Boolean Kleene category with converse satisfying the typed Dedekind law. -/
class RelationCategory (C : Type u) [Category.{v} C] [KleeneCategory C]
    [BooleanKleeneCategory C] [KleeneCategoryWithConverse C] : Prop where
  dedekind {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) :
    (f ≫ g) ⊓ h ≤ (f ⊓ h ≫ gᵒ) ≫ (g ⊓ fᵒ ≫ h)

namespace RelationCategory

open KleeneCategory
variable {C : Type u} [Category.{v} C] [KleeneCategory C]
  [BooleanKleeneCategory C] [KleeneCategoryWithConverse C] [RelationCategory C]
  {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z}

theorem comp_inf_le_inf_comp (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) :
    (f ≫ g) ⊓ h ≤ (f ⊓ h ≫ gᵒ) ≫ g :=
  (dedekind f g h).trans (comp_le_comp_right inf_le_left _)

theorem comp_inf_le_comp_inf (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) :
    (f ≫ g) ⊓ h ≤ f ≫ (g ⊓ fᵒ ≫ h) :=
  (dedekind f g h).trans (comp_le_comp_left inf_le_left _)

theorem converse_comp_compl_le_compl (hh : f ≫ g ≤ h) : fᵒ ≫ hᶜ ≤ gᶜ := by
  rw [le_compl_iff_disjoint_right, disjoint_iff_inf_le]
  calc (fᵒ ≫ hᶜ) ⊓ g ≤ fᵒ ≫ (hᶜ ⊓ fᵒᵒ ≫ g) := comp_inf_le_comp_inf _ _ _
    _ = fᵒ ≫ (hᶜ ⊓ f ≫ g) := by rw [converse_converse]
    _ ≤ fᵒ ≫ (hᶜ ⊓ h) := comp_le_comp_right (inf_le_inf_left _ hh) _
    _ = ⊥ := by rw [compl_inf_eq_bot, comp_bot]

theorem compl_comp_converse_le_compl (hh : f ≫ g ≤ h) : hᶜ ≫ gᵒ ≤ fᶜ := by
  rw [le_compl_iff_disjoint_right, disjoint_iff_inf_le]
  calc (hᶜ ≫ gᵒ) ⊓ f ≤ (hᶜ ⊓ f ≫ gᵒᵒ) ≫ gᵒ := comp_inf_le_inf_comp _ _ _
    _ = (hᶜ ⊓ f ≫ g) ≫ gᵒ := by rw [converse_converse]
    _ ≤ (hᶜ ⊓ h) ≫ gᵒ := comp_le_comp_left (inf_le_inf_left _ hh) _
    _ = ⊥ := by rw [compl_inf_eq_bot, bot_comp]

/-- The left Schröder equivalence, with all three endpoint types retained. -/
theorem schroeder_left : f ≫ g ≤ h ↔ fᵒ ≫ hᶜ ≤ gᶜ :=
  ⟨converse_comp_compl_le_compl, fun hh ↦ by simpa using converse_comp_compl_le_compl hh⟩

/-- The right Schröder equivalence. -/
theorem schroeder_right : f ≫ g ≤ h ↔ hᶜ ≫ gᵒ ≤ fᶜ :=
  ⟨compl_comp_converse_le_compl, fun hh ↦ by simpa using compl_comp_converse_le_compl hh⟩

theorem le_comp_converse_comp (f : X ⟶ Y) : f ≤ f ≫ fᵒ ≫ f := by
  calc f = (f ≫ 𝟙 Y) ⊓ f := by simp
    _ ≤ f ≫ (𝟙 Y ⊓ fᵒ ≫ f) := comp_inf_le_comp_inf _ _ _
    _ ≤ f ≫ fᵒ ≫ f := comp_le_comp_right inf_le_right _

end RelationCategory

namespace CategoryTheory.RelCat

instance instBooleanKleeneCategory : BooleanKleeneCategory RelCat.{u} where
  inf f g := .ofRel (f.rel ∩ g.rel)
  top := .ofRel Set.univ
  compl f := .ofRel f.relᶜ
  inf_le_left _ _ := Set.inter_subset_left
  inf_le_right _ _ := Set.inter_subset_right
  le_inf _ _ _ hf hg := Set.subset_inter hf hg
  le_sup_inf f g h := by
    change (f.rel ⊔ g.rel) ⊓ (f.rel ⊔ h.rel) ≤ f.rel ⊔ g.rel ⊓ h.rel
    exact _root_.le_sup_inf
  le_top _ := Set.subset_univ _
  inf_compl_le_bot f := by
    change f.rel ⊓ f.relᶜ ≤ ⊥
    simp
  top_le_sup_compl f := by
    change ⊤ ≤ f.rel ⊔ f.relᶜ
    simp

instance instRelationCategory : RelationCategory RelCat.{u} where
  dedekind f g h := by
    rintro ⟨x, z⟩ ⟨⟨y, hxy, hyz⟩, hxz⟩
    exact ⟨y, ⟨hxy, z, hxz, hyz⟩, hyz, x, hxy, hxz⟩

@[simp] theorem Hom.rel_inf {X Y : RelCat.{u}} (f g : X ⟶ Y) :
    (f ⊓ g).rel = f.rel ∩ g.rel := rfl

@[simp] theorem Hom.rel_top {X Y : RelCat.{u}} : (⊤ : X ⟶ Y).rel = Set.univ := rfl

@[simp] theorem Hom.rel_compl {X Y : RelCat.{u}} (f : X ⟶ Y) :
    fᶜ.rel = f.relᶜ := rfl

end CategoryTheory.RelCat

namespace CategoryTheory.SingleObj

instance instBooleanKleeneCategory {K : Type u} [RelationAlgebra K] :
    BooleanKleeneCategory (SingleObj K) where
  inf := (· ⊓ ·)
  top := ⊤
  compl := Compl.compl
  inf_le_left _ _ := inf_le_left
  inf_le_right _ _ := inf_le_right
  le_inf _ _ _ := le_inf
  le_sup_inf _ _ _ := le_sup_inf
  le_top _ := le_top
  inf_compl_le_bot _ := (inf_compl_eq_bot).le
  top_le_sup_compl _ := (sup_compl_eq_top).ge

instance instRelationCategory {K : Type u} [RelationAlgebra K] :
    RelationCategory (SingleObj K) where
  dedekind f g h := RelationAlgebra.dedekind g f h

end CategoryTheory.SingleObj

namespace CategoryTheory.End

variable {C : Type u} [Category.{v} C] [KleeneCategory C]
  [BooleanKleeneCategory C] [KleeneCategoryWithConverse C] [RelationCategory C] {X : C}

/-- Endomorphisms recover the untyped relation algebra, with reversed multiplication. -/
instance instRelationAlgebra : RelationAlgebra (End X) where
  __ := (inferInstance : KleeneAlgebra (End X))
  __ := BooleanKleeneCategory.endBooleanAlgebra
  star := converse
  star_involutive := converse_converse
  star_mul f g := converse_comp g f
  star_add := converse_sup
  dedekind f g h := RelationCategory.dedekind g f h

end CategoryTheory.End
