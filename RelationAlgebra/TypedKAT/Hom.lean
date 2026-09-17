import RelationAlgebra.TypedKAT
import Mathlib.Order.Hom.BoundedLattice

/-!
# Homomorphisms of typed Kleene algebras with tests

A `TypedKAT.Hom T U obj` preserves identity, composition, zero, choice, star, and the
Boolean test embedding. Its object map is fixed in the type, so the uniqueness clause
of the free-model universal property can be stated without transports between hom-sets.
The test maps are Boolean homomorphisms (`BoundedLatticeHom` also preserves complement).
-/

open CategoryTheory
open scoped Computability

universe u₁ v₁ w₁ u₂ v₂ w₂

namespace TypedKAT

variable {C : Type u₁} [Category.{v₁} C] [KleeneCategory C]
  {D : Type u₂} [Category.{v₂} D] [KleeneCategory D]
  (T : C → Type w₁) [∀ X, BooleanAlgebra (T X)] [TypedKAT C T]
  (U : D → Type w₂) [∀ X, BooleanAlgebra (U X)] [TypedKAT D U]

/-- A homomorphism of typed KATs over a specified object map. -/
structure Hom (obj : C → D) where
  /-- The map on parallel morphisms. -/
  map {X Y : C} : (X ⟶ Y) → (obj X ⟶ obj Y)
  /-- The Boolean homomorphism on tests at each object. -/
  testMap (X : C) : BoundedLatticeHom (T X) (U (obj X))
  map_id (X : C) : map (𝟙 X) = 𝟙 (obj X)
  map_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : map (f ≫ g) = map f ≫ map g
  map_bot {X Y : C} : map (⊥ : X ⟶ Y) = ⊥
  map_sup {X Y : C} (f g : X ⟶ Y) : map (f ⊔ g) = map f ⊔ map g
  map_star {X : C} (f : X ⟶ X) : map f∗ = (map f)∗
  map_test {X : C} (b : T X) : map (test b) = test (testMap X b)

namespace Hom

variable {T U} {obj : C → D}

attribute [simp] map_id map_comp map_bot map_sup map_star map_test

/-- Equality of the morphism maps and Boolean maps determines a typed KAT homomorphism. -/
@[ext] theorem ext {F G : Hom T U obj}
    (hm : ∀ X Y (f : X ⟶ Y), F.map f = G.map f)
    (ht : ∀ X b, F.testMap X b = G.testMap X b) : F = G := by
  have hm' : @F.map = @G.map := funext fun X ↦ funext fun Y ↦ funext (hm X Y)
  have ht' : F.testMap = G.testMap := funext fun X ↦ BoundedLatticeHom.ext (ht X)
  cases F
  cases G
  cases hm'
  cases ht'
  rfl

/-- Forgetting the order, star, and test structure gives an ordinary functor. -/
def toFunctor (F : Hom T U obj) : C ⥤ D where
  obj := obj
  map := F.map
  map_id := F.map_id
  map_comp := F.map_comp

/-- Typed KAT homomorphisms preserve the order on every hom-set. -/
theorem monotone (F : Hom T U obj) {X Y : C} : Monotone (F.map (X := X) (Y := Y)) := by
  intro f g h
  apply sup_eq_right.mp
  rw [← F.map_sup, sup_eq_right.mpr h]

end Hom
end TypedKAT
