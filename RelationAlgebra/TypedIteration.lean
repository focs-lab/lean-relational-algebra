import RelationAlgebra.Kleene.Iteration
import RelationAlgebra.TypedBoolean

/-!
# Typed strict iteration

For an endomorphism `f`, `f⁺ = f ≫ f∗` means one or more steps. The induction and
bisimulation rules allow rectangular contexts. There is no strict iteration on a morphism
whose source and target differ. The notation shares the `Computability` scope with star.

This follows Pous' `kleene.v`, at the Kleene-category level. `End` and `SingleObj` reverse
multiplication, so their agreement with scalar iteration uses the proved star-commutation
law rather than definitional equality. In `RelCat`, strict iteration is `Relation.TransGen`.
-/

open CategoryTheory
open scoped Computability KleeneCategoryWithConverse

universe u v

namespace KleeneCategory

variable {C : Type u} [Category.{v} C] [KleeneCategory C] {X Y : C}

instance instKPlusHom : KPlus (X ⟶ X) := ⟨fun f ↦ f ≫ f∗⟩

theorem kplus_eq_comp_kstar (f : X ⟶ X) : f⁺ = f ≫ f∗ := rfl

theorem kplus_eq_kstar_comp (f : X ⟶ X) : f⁺ = f∗ ≫ f := (kstar_comp_comm f).symm

/-- `End` reverses multiplication; commutation makes the two strict iterations agree. -/
theorem End.kplus_def (f : End X) : f⁺ = (show X ⟶ X from f)⁺ := kstar_comp_comm f

theorem le_kplus (f : X ⟶ X) : f ≤ f⁺ := le_comp_kstar f f

theorem kplus_le_kstar (f : X ⟶ X) : f⁺ ≤ f∗ := comp_kstar_le_kstar f

@[gcongr] theorem kplus_mono {f g : X ⟶ X} (h : f ≤ g) : f⁺ ≤ g⁺ :=
  comp_le_comp h (kstar_mono h)

@[simp] theorem kplus_bot : (⊥ : X ⟶ X)⁺ = ⊥ := bot_comp _

@[simp] theorem kplus_id : (𝟙 X)⁺ = 𝟙 X := by
  rw [kplus_eq_comp_kstar, kstar_id, Category.id_comp]

@[simp] theorem kplus_top [BooleanKleeneCategory C] : (⊤ : X ⟶ X)⁺ = ⊤ :=
  le_antisymm le_top (le_kplus _)

theorem id_sup_kplus (f : X ⟶ X) : 𝟙 X ⊔ f⁺ = f∗ := by
  simpa only [End.kplus_def] using KleeneAlgebra.one_add_kplus (End.of f)

theorem kplus_unfold_left (f : X ⟶ X) : f ⊔ f ≫ f⁺ = f⁺ := by
  simpa only [End.kplus_def] using KleeneAlgebra.kplus_unfold_right (End.of f)

theorem kplus_unfold_right (f : X ⟶ X) : f ⊔ f⁺ ≫ f = f⁺ := by
  simpa only [End.kplus_def] using KleeneAlgebra.kplus_unfold_left (End.of f)

theorem comp_kplus_le_kplus (f : X ⟶ X) : f ≫ f⁺ ≤ f⁺ :=
  le_sup_right.trans (kplus_unfold_left f).le

theorem kplus_comp_le_kplus (f : X ⟶ X) : f⁺ ≫ f ≤ f⁺ :=
  le_sup_right.trans (kplus_unfold_right f).le

/-- Rectangular strict left induction. -/
theorem kplus_comp_le {f : X ⟶ X} {g h : X ⟶ Y}
    (hfg : f ≫ g ≤ h) (hfh : f ≫ h ≤ h) : f⁺ ≫ g ≤ h := by
  rw [kplus_eq_kstar_comp, Category.assoc]
  exact kstar_comp_le hfg hfh

/-- Rectangular strict right induction. -/
theorem comp_kplus_le {f : X ⟶ X} {g h : Y ⟶ X}
    (hgf : g ≫ f ≤ h) (hhf : h ≫ f ≤ h) : g ≫ f⁺ ≤ h := by
  rw [kplus_eq_comp_kstar, ← Category.assoc]
  exact comp_kstar_le hgf hhf

theorem kplus_le_of_comp_le_right {f g : X ⟶ X} (hfg : f ≤ g) (h : f ≫ g ≤ g) :
    f⁺ ≤ g := by
  rw [kplus_eq_kstar_comp]
  exact kstar_comp_le hfg h

theorem kplus_le_of_comp_le_left {f g : X ⟶ X} (hfg : f ≤ g) (h : g ≫ f ≤ g) :
    f⁺ ≤ g := comp_kstar_le hfg h

theorem kplus_comp_kplus_le (f : X ⟶ X) : f⁺ ≫ f⁺ ≤ f⁺ :=
  kplus_comp_le (comp_kplus_le_kplus f) (comp_kplus_le_kplus f)

theorem isLeast_kplus (f : X ⟶ X) : IsLeast {g | f ≤ g ∧ g ≫ g ≤ g} f⁺ :=
  ⟨⟨le_kplus f, kplus_comp_kplus_le f⟩, fun _ h ↦
    kplus_le_of_comp_le_right h.1 ((comp_le_comp_left h.1 _).trans h.2)⟩

@[simp] theorem kplus_idem (f : X ⟶ X) : f⁺⁺ = f⁺ :=
  (kplus_le_of_comp_le_right le_rfl (kplus_comp_kplus_le f)).antisymm (le_kplus _)

@[simp] theorem kstar_kplus (f : X ⟶ X) : (f⁺)∗ = f∗ :=
  ((kstar_mono (kplus_le_kstar f)).trans (kstar_idem f).le).antisymm
    (kstar_mono (le_kplus f))

@[simp] theorem kplus_kstar (f : X ⟶ X) : (f∗)⁺ = f∗ := by
  rw [kplus_eq_comp_kstar, kstar_idem, kstar_comp_kstar]

theorem kplus_comp_kstar (f : X ⟶ X) : f⁺ ≫ f∗ = f⁺ := by
  rw [kplus_eq_comp_kstar, Category.assoc, kstar_comp_kstar]

theorem kstar_comp_kplus (f : X ⟶ X) : f∗ ≫ f⁺ = f⁺ := by
  rw [kplus_eq_kstar_comp, ← Category.assoc, kstar_comp_kstar]

theorem kplus_comp_le_comp_kplus_of_le {f : X ⟶ X} {g : Y ⟶ Y} {h : X ⟶ Y}
    (hfg : f ≫ h ≤ h ≫ g) : f⁺ ≫ h ≤ h ≫ g⁺ := by
  calc f⁺ ≫ h = f ≫ f∗ ≫ h := Category.assoc _ _ _
    _ ≤ f ≫ h ≫ g∗ := comp_le_comp_right (kstar_comp_le_comp_kstar_of_le hfg) _
    _ = (f ≫ h) ≫ g∗ := (Category.assoc _ _ _).symm
    _ ≤ (h ≫ g) ≫ g∗ := comp_le_comp_left hfg _
    _ = h ≫ g⁺ := Category.assoc _ _ _

theorem comp_kplus_le_kplus_comp_of_le {f : X ⟶ X} {g : Y ⟶ Y} {h : X ⟶ Y}
    (hfg : h ≫ g ≤ f ≫ h) : h ≫ g⁺ ≤ f⁺ ≫ h := by
  calc h ≫ g⁺ = (h ≫ g) ≫ g∗ := (Category.assoc _ _ _).symm
    _ ≤ (f ≫ h) ≫ g∗ := comp_le_comp_left hfg _
    _ = f ≫ h ≫ g∗ := Category.assoc _ _ _
    _ ≤ f ≫ f∗ ≫ h := comp_le_comp_right (comp_kstar_le_kstar_comp_of_le hfg) _
    _ = f⁺ ≫ h := (Category.assoc _ _ _).symm

theorem kplus_comp_eq_comp_kplus_of_eq {f : X ⟶ X} {g : Y ⟶ Y} {h : X ⟶ Y}
    (hfg : f ≫ h = h ≫ g) : f⁺ ≫ h = h ≫ g⁺ :=
  (kplus_comp_le_comp_kplus_of_le hfg.le).antisymm (comp_kplus_le_kplus_comp_of_le hfg.ge)

theorem comp_kplus_eq_kplus_comp (f : X ⟶ Y) (g : Y ⟶ X) :
    f ≫ (g ≫ f)⁺ = (f ≫ g)⁺ ≫ f :=
  (kplus_comp_eq_comp_kplus_of_eq (Category.assoc f g f)).symm

theorem kplus_sup_kplus (f g : X ⟶ X) : (f⁺ ⊔ g⁺)⁺ = (f ⊔ g)⁺ := by
  apply le_antisymm
  · apply (isLeast_kplus _).2
    exact ⟨sup_le (kplus_mono le_sup_left) (kplus_mono le_sup_right), kplus_comp_kplus_le _⟩
  · exact kplus_mono (sup_le_sup (le_kplus f) (le_kplus g))

theorem kplus_comp_of_idempotent (f e : X ⟶ X) (hf : f ≫ f = f) :
    (f ≫ e)⁺ ≫ f = (f ≫ e ≫ f)⁺ := by
  symm
  calc (f ≫ e ≫ f)⁺ = (f ≫ e) ≫ f ≫ ((f ≫ e) ≫ f)∗ := by
        simp only [kplus_eq_comp_kstar, Category.assoc]
    _ = (f ≫ e) ≫ (f ≫ (f ≫ e))∗ ≫ f := by rw [comp_kstar_eq_kstar_comp]
    _ = (f ≫ e) ≫ (f ≫ e)∗ ≫ f := by rw [← Category.assoc f f e, hf]
    _ = (f ≫ e)⁺ ≫ f := (Category.assoc _ _ _).symm

end KleeneCategory

namespace KleeneCategoryWithConverse

variable {C : Type u} [Category.{v} C] [KleeneCategory C] [KleeneCategoryWithConverse C]
  {X : C}

@[simp] theorem converse_kplus (f : X ⟶ X) : (f⁺)ᵒ = (fᵒ)⁺ := by
  rw [KleeneCategory.kplus_eq_comp_kstar, converse_comp, converse_kstar,
    ← KleeneCategory.kplus_eq_kstar_comp]

end KleeneCategoryWithConverse

namespace CategoryTheory.SingleObj

/-- Compatibility accounts for the reversal of multiplication in `SingleObj`. -/
theorem kplus_as_kplus {K : Type u} [KleeneAlgebra K] {X : SingleObj K} (f : X ⟶ X) :
    (KleeneCategory.instKPlusHom (C := SingleObj K) (X := X)).kplus f =
      (KleeneAlgebra.instKPlus (K := K)).kplus f :=
  KleeneAlgebra.kstar_mul_comm (K := K) f

end CategoryTheory.SingleObj

namespace CategoryTheory.RelCat

@[simp] theorem mem_kplus {X : RelCat.{u}} (f : X ⟶ X) (x y : X) :
    (x, y) ∈ (f⁺).rel ↔ Relation.TransGen (fun a b ↦ (a, b) ∈ f.rel) x y :=
  (Relation.TransGen.head'_iff (r := fun a b ↦ (a, b) ∈ f.rel)).symm

end CategoryTheory.RelCat
