import RelationAlgebra.Models.FinRelCategory
import RelationAlgebra.Decide.HKATTactic
import RelationAlgebra.Decide.RaTactic

/-!
# Executable heterogeneous finite relations

Two different finite state spaces, computed compositions and residuals, and abstract
typed KA/KAT proofs using the same morphisms. All computations are checked by the kernel.
-/

open CategoryTheory
open scoped Computability TypedKAT KleeneCategoryWithConverse ResiduatedKleeneCategory

namespace Examples.FiniteRelations

abbrev Bits := FinRelCat.of Bool
abbrev States := FinRelCat.of (Fin 3)

/-- Encode false as state 0 and true as state 2. -/
def encode : Bits ⟶ States := fun b i ↦ decide (i.val = if b then 2 else 0)

/-- A transition from 0 to 1 and from 1 to 2. -/
def advance : States ⟶ States := fun i j ↦ decide (j.val = i.val + 1)

theorem encode_roundTrip : encode ≫ encodeᵒ = 𝟙 Bits := by decide

set_option maxRecDepth 4096 in
theorem reachable : advance∗ 0 2 = true := by decide

set_option maxRecDepth 4096 in
theorem no_return : advance∗ 2 0 = false := by decide

set_option maxRecDepth 4096 in
theorem strict_reachable : advance⁺ 0 2 = true := by decide

set_option maxRecDepth 4096 in
theorem strict_no_empty_path : advance⁺ 0 0 = false := by decide

theorem residual_computes : (encode ⇘ encode) 0 0 = true := by decide

theorem residual_vacuous : (encode ⇘ encode) 1 2 = true := by decide

theorem residual_rejects : (encode ⇘ encode) 0 2 = false := by decide

example : (encode ⇙ encode) false true = false := by decide

example : (TypedKAT.test (T := fun X : FinRelCat ↦ X → Bool) (fun b : Bool ↦ b) : Bits ⟶ Bits)
      true true = true := by decide

example : (TypedKAT.test (T := fun X : FinRelCat ↦ X → Bool) (fun b : Bool ↦ b) : Bits ⟶ Bits)
      false false = false := by decide

example (R : Bits ⟶ States) (S : States ⟶ Bits) :
    R ≫ (S ≫ R)∗ = (R ≫ S)∗ ≫ R := by kat

example (R : Bits ⟶ States) (S : States ⟶ Bits) :
    R ≫ (S ≫ R)⁺ = (R ≫ S)⁺ ≫ R := by kat

example (R : Bits ⟶ States) (S : States ⟶ Bits) :
    (R ≫ S)ᵒ = Sᵒ ≫ Rᵒ := by ra

example (R : Bits ⟶ States) : R ⊔ Rᶜ = ⊤ := by ra

example (R : Bits ⟶ States) (T : Bits ⟶ Bits) : R ≫ (R ⇘ T) ≤ T := by ra

example (R : Bits ⟶ States) (S : States ⟶ Bits) (h : R ≫ S = ⊥) :
    R ≫ (S ≫ R)∗ ≫ S = ⊥ := by hkat

example (R : Bits ⟶ States) :
    FinRelCat.toRelCat.map Rᶜ = (FinRelCat.toRelCat.map R)ᶜ := by simp

example (R : States ⟶ States) :
    FinRelCat.toRelCat.map R∗ = (FinRelCat.toRelCat.map R)∗ := by simp

example (R : States ⟶ States) : (R∗ : FinRel (Fin 3) (Fin 3)) = FinRel.tc R := rfl

example : (⊥ : FinRelCat.of (Fin 0) ⟶ States) ≫ encodeᵒ = ⊥ := by decide

example : (⊥ : FinRelCat.of (Fin 0) ⟶ FinRelCat.of (Fin 0))∗ = 𝟙 _ := by decide

example : True := by
  fail_if_success have _ := encode ≫ encode
  trivial

end Examples.FiniteRelations
