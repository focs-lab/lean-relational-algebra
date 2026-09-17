import RelationAlgebra.TypedConverse

/-! # Converse models and compatibility checks -/

open CategoryTheory KleeneCategoryWithConverse
open scoped Computability KleeneCategoryWithConverse

universe u v

namespace TypedConverseExamples

section Abstract
variable {C : Type u} [Category.{v} C] [KleeneCategory C] [KleeneCategoryWithConverse C]
  {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (r : X ⟶ X)

example : (f ≫ g)ᵒ = gᵒ ≫ fᵒ := converse_comp _ _
example : (fᵒ)ᵒ = f := converse_converse _
example : (r∗)ᵒ = (rᵒ)∗ := converse_kstar _
example : (⊥ : X ⟶ Y)ᵒ = ⊥ := converse_bot
example : (𝟙 X)ᵒ = 𝟙 X := converse_id _
example : Star.star (R := End X) (f ≫ fᵒ) = (f ≫ fᵒ)ᵒ := rfl
example : Star.star (R := End X) ((f ≫ fᵒ : End X)∗) = ((f ≫ fᵒ)ᵒ)∗ :=
  KleeneAlgebra.star_kstar (K := End X) _
end Abstract

private def numbers : RelCat := ℕ
private def booleans : RelCat := Bool

/-- Heterogeneous converse reverses the actual relation arguments. -/
theorem relation_converse (f : numbers ⟶ booleans) (b : Bool) (n : ℕ) :
    (b, n) ∈ fᵒ.rel ↔ (n, b) ∈ f.rel := Iff.rfl

/-- The matrix instance conjugates coefficients as well as swapping indices. -/
theorem matrix_converse {K : Type u} [KleeneAlgebra K] [StarRing K]
    (f : (⟨2⟩ : Matrix.Mat K) ⟶ ⟨3⟩) (i : Fin 3) (j : Fin 2) :
    fᵒ i j = Star.star (f j i) := rfl

/-- Square matrices agree with Mathlib's existing star-ring instance. -/
example {K : Type u} [KleeneAlgebra K] [StarRing K]
    (f : (⟨2⟩ : Matrix.Mat K) ⟶ ⟨2⟩) :
    fᵒ = Star.star (R := Matrix (Fin 2) (Fin 2) K) f := rfl

/-- One-object composition reverses multiplication, consistently with its converse. -/
example {K : Type u} [KleeneAlgebra K] [StarRing K]
    (f g : (SingleObj.star K) ⟶ SingleObj.star K) :
    (f ≫ g)ᵒ = Star.star (f : K) * Star.star (g : K) := star_mul g f

end TypedConverseExamples
