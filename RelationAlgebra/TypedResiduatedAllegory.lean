/- SPDX-License-Identifier: LGPL-3.0-or-later
Lean translation and extensions, 2026-09-18. See LICENSE and NOTICE.md. -/
import RelationAlgebra.ResiduatedAllegory
import RelationAlgebra.TypedPoints
import RelationAlgebra.TypedResiduated

/-!
# Residuated allegory categories

Pous's `AL+DIV` interface on the existing hom-set orders of `AllegoryCategory`.
No joins, bounds, Boolean complements, or Kleene star are assumed by the core.
Bounds are used only in sections explicitly requiring them. Composition preserves
every existing supremum by adjunction, rather than extra axioms.

The instance from `RelationCategory` uses its canonical allegory and any supplied
`ResiduatedKleeneCategory` operations. No bridge combines unrelated order structures.
-/

open CategoryTheory AllegoryCategory
open scoped AllegoryCategory
universe u v

/-- Both composition maps have right adjoints on the existing hom-set orders. -/
class ResiduatedAllegoryCategory (C : Type u) [Category.{v} C] [AllegoryCategory C] where
  ldiv {X Y Z : C} : (X ⟶ Y) → (X ⟶ Z) → (Y ⟶ Z)
  rdiv {X Y Z : C} : (X ⟶ Z) → (Y ⟶ Z) → (X ⟶ Y)
  ldiv_spec {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) :
    g ≤ ldiv f h ↔ f ≫ g ≤ h
  rdiv_spec {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) :
    f ≤ rdiv h g ↔ f ≫ g ≤ h

namespace ResiduatedAllegoryCategory

scoped infixr:65 " ⇘ " => ldiv
scoped infixl:66 " ⇙ " => rdiv

variable {C : Type u} [Category.{v} C] [AllegoryCategory C] [ResiduatedAllegoryCategory C]
  {W X Y Z : C}

theorem gc_comp_ldiv (f : X ⟶ Y) : GaloisConnection (fun g : Y ⟶ Z ↦ f ≫ g) (ldiv f) :=
  fun _ _ ↦ (ldiv_spec _ _ _).symm

theorem gc_comp_rdiv (g : Y ⟶ Z) : GaloisConnection (fun f : X ⟶ Y ↦ f ≫ g) (fun h ↦ h ⇙ g) :=
  fun _ _ ↦ (rdiv_spec _ _ _).symm

/-- Composition preserves any supremum that exists; no complete lattice is assumed. -/
theorem isLUB_comp {s : Set (X ⟶ Y)} {f : X ⟶ Y} (hs : IsLUB s f) (g : Y ⟶ Z) :
    IsLUB ((fun k ↦ k ≫ g) '' s) (f ≫ g) := (gc_comp_rdiv g).isLUB_l_image hs

theorem comp_isLUB (f : X ⟶ Y) {s : Set (Y ⟶ Z)} {g : Y ⟶ Z} (hs : IsLUB s g) :
    IsLUB ((fun k ↦ f ≫ k) '' s) (f ≫ g) := (gc_comp_ldiv f).isLUB_l_image hs

/-- Residuals preserve any infimum that exists. -/
theorem ldiv_isGLB (f : X ⟶ Y) {s : Set (X ⟶ Z)} {h : X ⟶ Z} (hs : IsGLB s h) :
    IsGLB (ldiv f '' s) (f ⇘ h) := (gc_comp_ldiv f).isGLB_u_image hs

theorem isGLB_rdiv {s : Set (X ⟶ Z)} {h : X ⟶ Z} (hs : IsGLB s h) (g : Y ⟶ Z) :
    IsGLB ((fun k ↦ k ⇙ g) '' s) (h ⇙ g) := (gc_comp_rdiv g).isGLB_u_image hs

theorem comp_ldiv_le (f : X ⟶ Y) (h : X ⟶ Z) : f ≫ (f ⇘ h) ≤ h :=
  (ldiv_spec _ _ _).mp le_rfl

theorem rdiv_comp_le (g : Y ⟶ Z) (h : X ⟶ Z) : (h ⇙ g) ≫ g ≤ h :=
  (rdiv_spec _ _ _).mp le_rfl

theorem le_ldiv_comp (f : X ⟶ Y) (g : Y ⟶ Z) : g ≤ f ⇘ (f ≫ g) :=
  (ldiv_spec _ _ _).mpr le_rfl

theorem le_comp_rdiv (f : X ⟶ Y) (g : Y ⟶ Z) : f ≤ (f ≫ g) ⇙ g :=
  (rdiv_spec _ _ _).mpr le_rfl

theorem ldiv_le_ldiv {f f' : X ⟶ Y} {h h' : X ⟶ Z} (hf : f' ≤ f) (hh : h ≤ h') :
    f ⇘ h ≤ f' ⇘ h' :=
  (ldiv_spec _ _ _).mpr (((comp_mono_left hf _).trans (comp_ldiv_le f h)).trans hh)

theorem rdiv_le_rdiv {g g' : Y ⟶ Z} {h h' : X ⟶ Z} (hg : g' ≤ g) (hh : h ≤ h') :
    h ⇙ g ≤ h' ⇙ g' :=
  (rdiv_spec _ _ _).mpr (((comp_mono_right hg _).trans (rdiv_comp_le g h)).trans hh)

@[simp] theorem id_ldiv (h : X ⟶ Y) : (𝟙 X) ⇘ h = h := by
  apply eq_of_forall_le_iff
  intro k
  rw [ldiv_spec, Category.id_comp]

@[simp] theorem rdiv_id (h : X ⟶ Y) : h ⇙ (𝟙 Y) = h := by
  apply eq_of_forall_le_iff
  intro k
  rw [rdiv_spec, Category.comp_id]

/-- Residuation of a composite can be performed one factor at a time. -/
theorem comp_ldiv (f : W ⟶ X) (g : X ⟶ Y) (h : W ⟶ Z) :
    (f ≫ g) ⇘ h = g ⇘ (f ⇘ h) := by
  apply eq_of_forall_le_iff
  intro k
  rw [ldiv_spec, ldiv_spec, ldiv_spec, Category.assoc]

theorem rdiv_comp (g : W ⟶ X) (k : X ⟶ Y) (h : Z ⟶ Y) :
    h ⇙ (g ≫ k) = (h ⇙ k) ⇙ g := by
  apply eq_of_forall_le_iff
  intro f
  rw [rdiv_spec, rdiv_spec, rdiv_spec, Category.assoc]

theorem ldiv_rdiv (f : W ⟶ X) (h : W ⟶ Z) (g : Y ⟶ Z) :
    f ⇘ (h ⇙ g) = (f ⇘ h) ⇙ g := by
  apply eq_of_forall_le_iff
  intro k
  rw [ldiv_spec, rdiv_spec, rdiv_spec, ldiv_spec, Category.assoc]

theorem le_iff_id_le_ldiv (f h : X ⟶ Y) : f ≤ h ↔ 𝟙 Y ≤ f ⇘ h := by
  rw [ldiv_spec, Category.comp_id]

theorem le_iff_id_le_rdiv (f h : X ⟶ Y) : f ≤ h ↔ 𝟙 X ≤ h ⇙ f := by
  rw [rdiv_spec, Category.id_comp]

theorem id_le_ldiv_self (f : X ⟶ Y) : 𝟙 Y ≤ f ⇘ f := by
  rw [ldiv_spec, Category.comp_id]

theorem id_le_rdiv_self (f : X ⟶ Y) : 𝟙 X ≤ f ⇙ f := by
  rw [rdiv_spec, Category.id_comp]

theorem ldiv_comp_ldiv_le (f : W ⟶ X) (g : W ⟶ Y) (h : W ⟶ Z) :
    (f ⇘ g) ≫ (g ⇘ h) ≤ f ⇘ h := by
  rw [ldiv_spec, ← Category.assoc]
  exact (comp_mono_left (comp_ldiv_le f g) _).trans (comp_ldiv_le g h)

theorem rdiv_comp_rdiv_le (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ Z) :
    (f ⇙ g) ≫ (g ⇙ h) ≤ f ⇙ h := by
  rw [rdiv_spec, Category.assoc]
  exact (comp_mono_right (rdiv_comp_le h g) _).trans (rdiv_comp_le g f)

/-- The adjunction characterizes the residual uniquely. -/
theorem ldiv_eq_of_spec (f : X ⟶ Y) (h : X ⟶ Z) (k : Y ⟶ Z)
    (hk : ∀ g, g ≤ k ↔ f ≫ g ≤ h) : f ⇘ h = k := by
  apply eq_of_forall_le_iff
  intro g
  rw [ldiv_spec, hk]

theorem rdiv_eq_of_spec (h : X ⟶ Z) (g : Y ⟶ Z) (k : X ⟶ Y)
    (hk : ∀ f, f ≤ k ↔ f ≫ g ≤ h) : h ⇙ g = k := by
  apply eq_of_forall_le_iff
  intro f
  rw [rdiv_spec, hk]

@[simp] theorem converse_ldiv (f : X ⟶ Y) (h : X ⟶ Z) : (f ⇘ h)ᵒ = hᵒ ⇙ fᵒ := by
  apply eq_of_forall_le_iff
  intro k
  rw [← converse_le_converse_iff, converse_converse, ldiv_spec, rdiv_spec,
    ← converse_le_converse_iff, converse_comp, converse_converse]

@[simp] theorem converse_rdiv (h : X ⟶ Z) (g : Y ⟶ Z) : (h ⇙ g)ᵒ = gᵒ ⇘ hᵒ := by
  apply eq_of_forall_le_iff
  intro k
  rw [← converse_le_converse_iff, converse_converse, rdiv_spec, ldiv_spec,
    ← converse_le_converse_iff, converse_comp, converse_converse]

/-- Right adjoints preserve meets on every hom-set. -/
theorem ldiv_inf (f : X ⟶ Y) (h k : X ⟶ Z) : f ⇘ (h ⊓ k) = (f ⇘ h) ⊓ (f ⇘ k) := by
  apply eq_of_forall_le_iff
  intro g
  rw [le_inf_iff, ldiv_spec, ldiv_spec, ldiv_spec, le_inf_iff]

theorem inf_rdiv (h k : X ⟶ Z) (g : Y ⟶ Z) : (h ⊓ k) ⇙ g = (h ⇙ g) ⊓ (k ⇙ g) := by
  apply eq_of_forall_le_iff
  intro f
  rw [le_inf_iff, rdiv_spec, rdiv_spec, rdiv_spec, le_inf_iff]

theorem isPreorder_ldiv_self (f : X ⟶ Y) : IsPreorder (f ⇘ f) :=
  ⟨id_le_ldiv_self f, ldiv_comp_ldiv_le f f f⟩

theorem isPreorder_rdiv_self (f : X ⟶ Y) : IsPreorder (f ⇙ f) :=
  ⟨id_le_rdiv_self f, rdiv_comp_rdiv_le f f f⟩

section Bottom
variable [∀ X Y : C, OrderBot (X ⟶ Y)]

/-- Left adjoints preserve bottom; no annihilation axiom is needed. -/
@[simp] theorem bot_comp (g : Y ⟶ Z) : (⊥ : X ⟶ Y) ≫ g = ⊥ :=
  le_antisymm ((rdiv_spec _ _ _).mp bot_le) bot_le

@[simp] theorem comp_bot (f : X ⟶ Y) : f ≫ (⊥ : Y ⟶ Z) = ⊥ :=
  le_antisymm ((ldiv_spec _ _ _).mp bot_le) bot_le

/-- A zero-intersection form of Schröder's law without Boolean complements. -/
theorem comp_inf_eq_bot_iff (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) :
    (f ≫ g) ⊓ h = ⊥ ↔ g ⊓ (fᵒ ≫ h) = ⊥ := by
  constructor
  · intro he
    apply le_antisymm _ bot_le
    calc g ⊓ (fᵒ ≫ h) = (fᵒ ≫ h) ⊓ g := inf_comm _ _
      _ ≤ fᵒ ≫ (h ⊓ (fᵒ)ᵒ ≫ g) := comp_inf_le_comp_inf _ _ _
      _ = ⊥ := by rw [converse_converse, inf_comm h, he, comp_bot]
  · intro he
    exact le_antisymm ((comp_inf_le_comp_inf f g h).trans_eq (by rw [he, comp_bot])) bot_le

/-- The other zero-intersection law, obtained by converse. -/
theorem inf_comp_eq_bot_iff (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) :
    (f ≫ g) ⊓ h = ⊥ ↔ f ⊓ (h ≫ gᵒ) = ⊥ := by
  have conv_zero {P Q : C} (k : P ⟶ Q) : kᵒ = ⊥ ↔ k = ⊥ := by
    rw [← converse_bot, converse_injective.eq_iff]
  simpa only [← converse_comp, ← converse_inf, conv_zero] using
    comp_inf_eq_bot_iff gᵒ fᵒ hᵒ

end Bottom

section Top
variable [∀ X Y : C, OrderTop (X ⟶ Y)]

@[simp] theorem ldiv_top (f : X ⟶ Y) : f ⇘ (⊤ : X ⟶ Z) = ⊤ :=
  top_unique ((ldiv_spec _ _ _).mpr le_top)

@[simp] theorem top_rdiv (g : Y ⟶ Z) : (⊤ : X ⟶ Z) ⇙ g = ⊤ :=
  top_unique ((rdiv_spec _ _ _).mpr le_top)

end Top

section Bounded
variable [∀ X Y : C, OrderBot (X ⟶ Y)] [∀ X Y : C, OrderTop (X ⟶ Y)]

@[simp] theorem bot_ldiv (h : X ⟶ Z) : (⊥ : X ⟶ Y) ⇘ h = ⊤ :=
  top_unique ((ldiv_spec _ _ _).mpr (by simp))

@[simp] theorem rdiv_bot (h : X ⟶ Z) : h ⇙ (⊥ : Y ⟶ Z) = ⊤ :=
  top_unique ((rdiv_spec _ _ _).mpr (by simp))

/-- Pous's `disjoint_vect_iff'`, using residuals without complements or star. -/
theorem isVector_disjoint_iff {f g : X ⟶ Y} (hg : IsVector g) :
    f ⊓ g = ⊥ ↔ gᵒ ≫ f = ⊥ := by
  simpa only [inf_top_eq, converse_converse, show g ≫ (⊤ : Y ⟶ Y) = g from hg] using
    (comp_inf_eq_bot_iff gᵒ f (⊤ : Y ⟶ Y)).symm

end Bounded

end ResiduatedAllegoryCategory

namespace RelationCategory

variable {C : Type u} [Category.{v} C] [KleeneCategory C]
  [BooleanKleeneCategory C] [KleeneCategoryWithConverse C] [RelationCategory C]
  [ResiduatedKleeneCategory C]

/-- Use existing residuals on the canonical relation-category allegory. -/
instance (priority := 100) toResiduatedAllegoryCategory : ResiduatedAllegoryCategory C where
  ldiv := ResiduatedKleeneCategory.ldiv
  rdiv := ResiduatedKleeneCategory.rdiv
  ldiv_spec := ResiduatedKleeneCategory.ldiv_spec
  rdiv_spec := ResiduatedKleeneCategory.rdiv_spec

end RelationCategory

namespace CategoryTheory.SingleObj

/-- Single-object composition reverses multiplication, exchanging the two residuals. -/
instance (priority := 200) instResiduatedAllegoryCategory {K : Type u} [Allegory K]
    [ResiduatedAllegory K] : ResiduatedAllegoryCategory (SingleObj K) where
  ldiv f h := ResiduatedAllegory.rdiv h f
  rdiv h g := ResiduatedAllegory.ldiv g h
  ldiv_spec f g h := ResiduatedAllegory.rdiv_spec g f h
  rdiv_spec f g h := ResiduatedAllegory.ldiv_spec g f h

end CategoryTheory.SingleObj

namespace CategoryTheory.End

variable {C : Type u} [Category.{v} C] [AllegoryCategory C]
  [ResiduatedAllegoryCategory C] {X : C}

/-- Endomorphism multiplication reverses composition, exchanging the two residuals. -/
instance (priority := 100) instResiduatedAllegory : ResiduatedAllegory (End X) where
  ldiv f h := ResiduatedAllegoryCategory.rdiv h f
  rdiv h g := ResiduatedAllegoryCategory.ldiv g h
  ldiv_spec f g h := ResiduatedAllegoryCategory.rdiv_spec g f h
  rdiv_spec f g h := ResiduatedAllegoryCategory.ldiv_spec g f h

end CategoryTheory.End

namespace ResiduatedAllegoryCategory

section Compatibility
variable {C : Type u} [Category.{v} C] [KleeneCategory C]
  [BooleanKleeneCategory C] [KleeneCategoryWithConverse C] [RelationCategory C]
  [ResiduatedKleeneCategory C] [ResiduatedAllegoryCategory C] {X Y Z : C}

/-- Any weak residual on the canonical allegory agrees with the Kleene interface. -/
theorem ldiv_eq_kleene (f : X ⟶ Y) (h : X ⟶ Z) :
    f ⇘ h = ResiduatedKleeneCategory.ldiv f h :=
  ldiv_eq_of_spec f h _ (fun _ ↦ ResiduatedKleeneCategory.ldiv_spec _ _ _)

theorem rdiv_eq_kleene (h : X ⟶ Z) (g : Y ⟶ Z) :
    h ⇙ g = ResiduatedKleeneCategory.rdiv h g :=
  rdiv_eq_of_spec h g _ (fun _ ↦ ResiduatedKleeneCategory.rdiv_spec _ _ _)

end Compatibility

section End
variable {C : Type u} [Category.{v} C] [AllegoryCategory C]
  [ResiduatedAllegoryCategory C] {X : C}

@[simp] theorem end_ldiv (f h : End X) : ResiduatedAllegory.ldiv f h = h ⇙ f := rfl
@[simp] theorem end_rdiv (h g : End X) : ResiduatedAllegory.rdiv h g = g ⇘ h := rfl

end End

end ResiduatedAllegoryCategory

namespace CategoryTheory.SingleObj

variable {K : Type u} [Allegory K] [ResiduatedAllegory K] {X Y Z : SingleObj K}

@[simp] theorem weak_ldiv (f : X ⟶ Y) (h : X ⟶ Z) :
    ResiduatedAllegoryCategory.ldiv f h = ResiduatedAllegory.rdiv h f := rfl
@[simp] theorem weak_rdiv (h : X ⟶ Z) (g : Y ⟶ Z) :
    ResiduatedAllegoryCategory.rdiv h g = ResiduatedAllegory.ldiv g h := rfl

end CategoryTheory.SingleObj

namespace CategoryTheory.RelCat

variable {X Y Z : RelCat.{u}}

/-- The weak left residual has the same universal predecessor semantics. -/
theorem Hom.mem_weak_ldiv (f : X ⟶ Y) (h : X ⟶ Z) (y : Y) (z : Z) :
    (y, z) ∈ (ResiduatedAllegoryCategory.ldiv f h).rel ↔
      ∀ x, (x, y) ∈ f.rel → (x, z) ∈ h.rel := by
  rw [ResiduatedAllegoryCategory.ldiv_eq_kleene, Hom.mem_ldiv]

/-- The weak right residual has the same universal successor semantics. -/
theorem Hom.mem_weak_rdiv (h : X ⟶ Z) (g : Y ⟶ Z) (x : X) (y : Y) :
    (x, y) ∈ (ResiduatedAllegoryCategory.rdiv h g).rel ↔
      ∀ z, (y, z) ∈ g.rel → (x, z) ∈ h.rel := by
  rw [ResiduatedAllegoryCategory.rdiv_eq_kleene, Hom.mem_rdiv]

end CategoryTheory.RelCat
