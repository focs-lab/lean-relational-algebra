import RelationAlgebra.Models.SetoidRelCategory
import RelationAlgebra.Decide.HKATTactic
import RelationAlgebra.Decide.RaTactic

/-!
# Relations between different setoids

Natural numbers modulo parity are related to two concrete states. Identity relates
different representatives of the same class; the quotient interpretation is faithful.
-/

open CategoryTheory
open scoped Computability TypedKAT KleeneCategoryWithConverse ResiduatedKleeneCategory

namespace Examples.SetoidRelations

def parity : Setoid ℕ where
  r a b := a % 2 = b % 2
  iseqv := ⟨fun _ ↦ rfl, Eq.symm, Eq.trans⟩

abbrev Parity : SetoidRelCat := { carrier := ℕ, setoid := parity }
abbrev Two : SetoidRelCat := { carrier := Fin 2, setoid := discreteSetoid (Fin 2) }
abbrev Exact : SetoidRelCat := { carrier := ℕ, setoid := discreteSetoid ℕ }

def classify : Parity ⟶ Two :=
  SetoidRelCat.Hom.ofRel (fun a b ↦ a % 2 = b.val) (by
    intro a a' b b' ha hb h
    change a % 2 = a' % 2 at ha
    change b = b' at hb
    subst b'
    exact ha.symm.trans h)

theorem same_class_is_identity : ((𝟙 Parity) : Parity ⟶ Parity).rel 0 2 := by
  change 0 % 2 = 2 % 2
  decide

theorem different_class_not_identity : ¬ ((𝟙 Parity) : Parity ⟶ Parity).rel 0 1 := by
  change ¬ (0 % 2 = 1 % 2)
  decide

/-- The same carrier can carry a second, different identity relation. -/
theorem exact_identity_differs : ¬ ((𝟙 Exact) : Exact ⟶ Exact).rel 0 2 := by
  change (0 : ℕ) ≠ 2
  decide

theorem classify_even : classify.rel 4 0 := rfl

theorem classify_odd : classify.rel 3 1 := rfl

theorem zero_star_equivalence : ((⊥ : Parity ⟶ Parity)∗).rel 0 2 := by
  rw [KleeneCategory.kstar_bot]
  exact same_class_is_identity

example : ¬ ((⊥ : Parity ⟶ Parity)⁺).rel 0 2 := by
  rw [KleeneCategory.kplus_bot]
  exact id

theorem quotient_classify :
    (⟦4⟧, ⟦(0 : Fin 2)⟧) ∈ (SetoidRelCat.toRelCat.map classify).rel :=
  (@HSetoidRel.mem_toQuotient _ _ Parity.setoid Two.setoid classify 4 0).mpr classify_even

example (R : Parity ⟶ Two) (S : Two ⟶ Parity) :
    R ≫ (S ≫ R)∗ = (R ≫ S)∗ ≫ R := by kat

example (R : Parity ⟶ Two) (S : Two ⟶ Parity) :
    R ≫ (S ≫ R)⁺ = (R ≫ S)⁺ ≫ R := by kat

example (R : Parity ⟶ Two) : R ⊔ Rᶜ = ⊤ := by ra

example (R : Parity ⟶ Two) (S : Two ⟶ Parity) : (R ≫ S)ᵒ = Sᵒ ≫ Rᵒ := by ra

example (R : Parity ⟶ Two) (T : Parity ⟶ Parity) : R ≫ (R ⇘ T) ≤ T := by ra

example (R : Parity ⟶ Two) (S : Two ⟶ Parity) (h : R ≫ S = ⊥) :
    R ≫ (S ≫ R)∗ ≫ S = ⊥ := by hkat

example (P : Set (Quotient parity)) :
    (TypedKAT.test (T := fun X : SetoidRelCat ↦ Set (Quotient X.setoid)) P : Parity ⟶ Parity) ≫
      TypedKAT.test (T := fun X : SetoidRelCat ↦ Set (Quotient X.setoid)) Pᶜ = ⊥ := by kat

example (R S : Parity ⟶ Two)
    (h : SetoidRelCat.toRelCat.map R = SetoidRelCat.toRelCat.map S) : R = S :=
  SetoidRelCat.homOrderIso.injective h

example (R : Parity ⟶ Parity) :
    SetoidRelCat.toSquare R∗ = (SetoidRelCat.toSquare R)∗ :=
  SetoidRelCat.square_kstar R

example (R : Parity ⟶ Two) :
    SetoidRelCat.toRelCat.map Rᶜ = (SetoidRelCat.toRelCat.map R)ᶜ := by simp

example : True := by
  fail_if_success have _ := classify ≫ classify
  trivial

end Examples.SetoidRelations
