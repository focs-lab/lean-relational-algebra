import RelationAlgebra.TypedBoolean
import RelationAlgebra.Residuated

/-!
# Residuals of typed composition

`f ⇘ h : Y ⟶ Z` is the greatest `g` with `f ≫ g ≤ h`; `h ⇙ g : X ⟶ Y`
is the greatest `f` with the same property. No complete lattice is assumed.
The scopes and argument order parallel the untyped factors in `Residuated.lean`.

Following Pous' `factors.v`, we prove the adjunction, cancellation, variance, composition,
and iteration laws. In a Boolean relation category, Schröder's laws construct both
residuals using converse and complement. The heterogeneous relational model also exposes
their pointwise universal-quantifier specifications.
-/

open CategoryTheory KleeneCategory KleeneCategoryWithConverse
open scoped Computability KleeneCategoryWithConverse

universe u v

/-- Both composition maps have right adjoints on the existing hom-set orders. -/
class ResiduatedKleeneCategory (C : Type u) [Category.{v} C] [KleeneCategory C] where
  ldiv {X Y Z : C} : (X ⟶ Y) → (X ⟶ Z) → (Y ⟶ Z)
  rdiv {X Y Z : C} : (X ⟶ Z) → (Y ⟶ Z) → (X ⟶ Y)
  ldiv_spec {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) :
    g ≤ ldiv f h ↔ f ≫ g ≤ h
  rdiv_spec {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) :
    f ≤ rdiv h g ↔ f ≫ g ≤ h

namespace ResiduatedKleeneCategory

scoped infixr:65 " ⇘ " => ldiv
scoped infixl:66 " ⇙ " => rdiv

variable {C : Type u} [Category.{v} C] [KleeneCategory C] [ResiduatedKleeneCategory C]
  {W X Y Z : C}

theorem gc_comp_ldiv (f : X ⟶ Y) : GaloisConnection (fun g : Y ⟶ Z ↦ f ≫ g) (ldiv f) :=
  fun _ _ ↦ (ldiv_spec _ _ _).symm

theorem gc_comp_rdiv (g : Y ⟶ Z) : GaloisConnection (fun f : X ⟶ Y ↦ f ≫ g) (fun h ↦ h ⇙ g) :=
  fun _ _ ↦ (rdiv_spec _ _ _).symm

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
  (ldiv_spec _ _ _).mpr (((comp_le_comp_left hf _).trans (comp_ldiv_le f h)).trans hh)

theorem rdiv_le_rdiv {g g' : Y ⟶ Z} {h h' : X ⟶ Z} (hg : g' ≤ g) (hh : h ≤ h') :
    h ⇙ g ≤ h' ⇙ g' :=
  (rdiv_spec _ _ _).mpr (((comp_le_comp_right hg _).trans (rdiv_comp_le g h)).trans hh)

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
  exact (comp_le_comp_left (comp_ldiv_le f g) _).trans (comp_ldiv_le g h)

theorem rdiv_comp_rdiv_le (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ Z) :
    (f ⇙ g) ≫ (g ⇙ h) ≤ f ⇙ h := by
  rw [rdiv_spec, Category.assoc]
  exact (comp_le_comp_right (rdiv_comp_le h g) _).trans (rdiv_comp_le g f)

@[simp] theorem kstar_ldiv_self (f : X ⟶ Y) : (f ⇘ f)∗ = f ⇘ f :=
  le_antisymm (kstar_le_of_comp_le_left (id_le_ldiv_self f) (ldiv_comp_ldiv_le f f f))
    (KleeneCategory.le_kstar _)

@[simp] theorem kstar_rdiv_self (f : X ⟶ Y) : (f ⇙ f)∗ = f ⇙ f :=
  le_antisymm (kstar_le_of_comp_le_left (id_le_rdiv_self f) (rdiv_comp_rdiv_le f f f))
    (KleeneCategory.le_kstar _)

section Boolean
variable [BooleanKleeneCategory C]

@[simp] theorem bot_ldiv (h : X ⟶ Z) : (⊥ : X ⟶ Y) ⇘ h = ⊤ := by
  apply top_unique
  rw [ldiv_spec, bot_comp]
  exact bot_le

@[simp] theorem rdiv_bot (h : X ⟶ Z) : h ⇙ (⊥ : Y ⟶ Z) = ⊤ := by
  apply top_unique
  rw [rdiv_spec, comp_bot]
  exact bot_le

@[simp] theorem ldiv_top (f : X ⟶ Y) : f ⇘ (⊤ : X ⟶ Z) = ⊤ := by
  apply top_unique
  rw [ldiv_spec]
  exact le_top

@[simp] theorem top_rdiv (g : Y ⟶ Z) : (⊤ : X ⟶ Z) ⇙ g = ⊤ := by
  apply top_unique
  rw [rdiv_spec]
  exact le_top

theorem sup_ldiv (f g : X ⟶ Y) (h : X ⟶ Z) : (f ⊔ g) ⇘ h = (f ⇘ h) ⊓ (g ⇘ h) := by
  apply eq_of_forall_le_iff
  intro k
  rw [le_inf_iff, ldiv_spec, ldiv_spec, ldiv_spec, sup_comp, sup_le_iff]

theorem ldiv_inf (f : X ⟶ Y) (h k : X ⟶ Z) : f ⇘ (h ⊓ k) = (f ⇘ h) ⊓ (f ⇘ k) := by
  apply eq_of_forall_le_iff
  intro g
  rw [le_inf_iff, ldiv_spec, ldiv_spec, ldiv_spec, le_inf_iff]

theorem rdiv_sup (h : X ⟶ Z) (f g : Y ⟶ Z) : h ⇙ (f ⊔ g) = (h ⇙ f) ⊓ (h ⇙ g) := by
  apply eq_of_forall_le_iff
  intro k
  rw [le_inf_iff, rdiv_spec, rdiv_spec, rdiv_spec, comp_sup, sup_le_iff]

theorem inf_rdiv (h k : X ⟶ Z) (g : Y ⟶ Z) : (h ⊓ k) ⇙ g = (h ⇙ g) ⊓ (k ⇙ g) := by
  apply eq_of_forall_le_iff
  intro f
  rw [le_inf_iff, rdiv_spec, rdiv_spec, rdiv_spec, le_inf_iff]

end Boolean

section Converse
variable [KleeneCategoryWithConverse C]

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

end Converse
end ResiduatedKleeneCategory

namespace RelationCategory

variable {C : Type u} [Category.{v} C] [KleeneCategory C]
  [BooleanKleeneCategory C] [KleeneCategoryWithConverse C] [RelationCategory C]

/-- Schröder's laws construct residuals without arbitrary joins. -/
noncomputable instance (priority := 100) toResiduatedKleeneCategory :
    ResiduatedKleeneCategory C where
  ldiv f h := (fᵒ ≫ hᶜ)ᶜ
  rdiv h g := (hᶜ ≫ gᵒ)ᶜ
  ldiv_spec _ _ _ := by rw [le_compl_comm, ← schroeder_left]
  rdiv_spec _ _ _ := by rw [le_compl_comm, ← schroeder_right]

end RelationCategory

namespace ResiduatedKleeneCategory

open scoped ResiduatedKleeneCategory
variable {C : Type u} [Category.{v} C] [KleeneCategory C]
  [BooleanKleeneCategory C] [KleeneCategoryWithConverse C] [RelationCategory C]
  [ResiduatedKleeneCategory C] {X Y Z : C}

/-- Any residual satisfying the adjunction agrees with the Boolean formula. -/
theorem ldiv_eq_compl (f : X ⟶ Y) (h : X ⟶ Z) : f ⇘ h = (fᵒ ≫ hᶜ)ᶜ := by
  apply eq_of_forall_le_iff
  intro g
  rw [ldiv_spec, le_compl_comm, ← RelationCategory.schroeder_left]

theorem rdiv_eq_compl (h : X ⟶ Z) (g : Y ⟶ Z) : h ⇙ g = (hᶜ ≫ gᵒ)ᶜ := by
  apply eq_of_forall_le_iff
  intro f
  rw [rdiv_spec, le_compl_comm, ← RelationCategory.schroeder_right]

end ResiduatedKleeneCategory

namespace CategoryTheory.RelCat

open scoped ResiduatedKleeneCategory
variable {X Y Z : RelCat.{u}}

/-- Left residual compares all predecessors, even for different endpoint types. -/
theorem Hom.mem_ldiv (f : X ⟶ Y) (h : X ⟶ Z) (y : Y) (z : Z) :
    (y, z) ∈ (f ⇘ h).rel ↔ ∀ x, (x, y) ∈ f.rel → (x, z) ∈ h.rel := by
  classical
  change (¬ ∃ x, (x, y) ∈ f.rel ∧ (x, z) ∉ h.rel) ↔ _
  simp only [not_exists, not_and, not_not]

/-- Right residual compares all successors. -/
theorem Hom.mem_rdiv (h : X ⟶ Z) (g : Y ⟶ Z) (x : X) (y : Y) :
    (x, y) ∈ (h ⇙ g).rel ↔ ∀ z, (y, z) ∈ g.rel → (x, z) ∈ h.rel := by
  classical
  change (¬ ∃ z, (x, z) ∉ h.rel ∧ (y, z) ∈ g.rel) ↔ _
  simp only [not_exists, not_and]
  apply forall_congr'
  intro z
  constructor
  · intro hh hg
    by_contra hn
    exact hh hn hg
  · intro hh hn hg
    exact hn (hh hg)

end CategoryTheory.RelCat

namespace CategoryTheory.SingleObj

/-- One-object composition reverses multiplication, so left and right factors swap. -/
instance instResiduatedKleeneCategory {K : Type u} [ResiduatedKleeneAlgebra K] :
    ResiduatedKleeneCategory (SingleObj K) where
  ldiv f h := ResiduatedIdemSemiring.rdiv h f
  rdiv h g := ResiduatedIdemSemiring.ldiv g h
  ldiv_spec f g h := ResiduatedIdemSemiring.rdiv_spec g f h
  rdiv_spec f g h := ResiduatedIdemSemiring.ldiv_spec g f h

end CategoryTheory.SingleObj

namespace CategoryTheory.End

variable {C : Type u} [Category.{v} C] [KleeneCategory C]
  [ResiduatedKleeneCategory C] {X : C}

/-- Endomorphism residuals swap the typed factors because `End` reverses multiplication. -/
instance instResiduatedKleeneAlgebra : ResiduatedKleeneAlgebra (End X) where
  __ := (inferInstance : KleeneAlgebra (End X))
  ldiv f h := ResiduatedKleeneCategory.rdiv h f
  rdiv h g := ResiduatedKleeneCategory.ldiv g h
  ldiv_spec f g h := ResiduatedKleeneCategory.rdiv_spec g f h
  rdiv_spec f g h := ResiduatedKleeneCategory.ldiv_spec g f h

end CategoryTheory.End
