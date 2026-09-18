/- SPDX-License-Identifier: LGPL-3.0-or-later
Copyright (c) 2026 Umang Mathur and contributors. See LICENSE and NOTICE.md. -/
import RelationAlgebra.TypedResiduatedAllegory
import RelationAlgebra.Models.FinRelCategory
import RelationAlgebra.Models.SetoidRelCategory
import RelationAlgebra.Models.MatrixResidual

/-!
# Weak residuation: abstract laws, a non-Boolean model, and compatibility

The three-element chain uses meet as composition and implication as residual.
Its middle element has no complement. No Kleene or Boolean category instance is
supplied, so these examples exercise the new weak interface independently.
-/

open CategoryTheory AllegoryCategory ResiduatedAllegoryCategory
open scoped AllegoryCategory ResiduatedAllegoryCategory
universe u v

namespace Examples.ResiduatedAllegory

section Abstract
variable {C : Type u} [Category.{v} C] [AllegoryCategory C]
  [ResiduatedAllegoryCategory C] {W X Y Z : C}

example (f : W ⟶ X) (g : X ⟶ Y) (h : W ⟶ Z) :
    (f ≫ g) ⇘ h = g ⇘ (f ⇘ h) := comp_ldiv _ _ _

example (f : X ⟶ Y) (h : X ⟶ Z) (g : Y ⟶ Z) (hg : g ≤ f ⇘ h) :
    f ≫ g ≤ h := (ldiv_spec _ _ _).mp hg

example (f : X ⟶ Y) (h : X ⟶ Z) (g : Y ⟶ Z) (hf : f ≤ h ⇙ g) :
    f ≫ g ≤ h := (rdiv_spec _ _ _).mp hf

example (f : X ⟶ Y) (h : X ⟶ Z) : (f ⇘ h)ᵒ = hᵒ ⇙ fᵒ := converse_ldiv _ _

example (h : X ⟶ Z) (g : Y ⟶ Z) : (h ⇙ g)ᵒ = gᵒ ⇘ hᵒ := converse_rdiv _ _

example (f : X ⟶ Y) (h k : X ⟶ Z) :
    f ⇘ (h ⊓ k) = (f ⇘ h) ⊓ (f ⇘ k) := ldiv_inf _ _ _

example (f : X ⟶ Y) : IsPreorder (f ⇘ f) := isPreorder_ldiv_self f

example (f : X ⟶ Y) {s : Set (Y ⟶ Z)} {g : Y ⟶ Z} (hs : IsLUB s g) :
    IsLUB ((fun k ↦ f ≫ k) '' s) (f ≫ g) := comp_isLUB f hs

example (a h : End X) : ResiduatedAllegory.ldiv a h = h ⇙ a := end_ldiv _ _

example (h b : End X) : ResiduatedAllegory.rdiv h b = b ⇘ h := end_rdiv _ _

variable [∀ X Y : C, OrderBot (X ⟶ Y)]

-- Bottom annihilation is derived, not part of AllegoryCategory's axioms.
example (f : X ⟶ Y) : f ≫ (⊥ : Y ⟶ Z) = ⊥ := comp_bot _

example (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) :
    (f ≫ g) ⊓ h = ⊥ ↔ g ⊓ (fᵒ ≫ h) = ⊥ := comp_inf_eq_bot_iff _ _ _

example (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) :
    (f ≫ g) ⊓ h = ⊥ ↔ f ⊓ (h ≫ gᵒ) = ⊥ := inf_comp_eq_bot_iff _ _ _

variable [∀ X Y : C, OrderTop (X ⟶ Y)]

/-- The previously missing upstream theorem, with no Boolean or Kleene hypotheses. -/
theorem vector_disjoint (f g : X ⟶ Y) (hg : IsVector g) :
    f ⊓ g = ⊥ ↔ gᵒ ≫ f = ⊥ := isVector_disjoint_iff hg

end Abstract

section Scalar
variable {K : Type u} [Allegory K] [ResiduatedAllegory K]

example (a b c : K) : b ≤ ResiduatedAllegory.ldiv a c ↔ a * b ≤ c :=
  ResiduatedAllegory.ldiv_spec _ _ _

example (X : SingleObj K) (a c : X ⟶ X) :
    a ⇘ c = ResiduatedAllegory.rdiv c a := SingleObj.weak_ldiv _ _

example (X : SingleObj K) (b c : X ⟶ X) :
    c ⇙ b = ResiduatedAllegory.ldiv b c := SingleObj.weak_rdiv _ _

-- Passing to SingleObj and then End restores the original scalar orientation.
example (X : SingleObj K) (a c : End X) :
    ResiduatedAllegory.ldiv (K := End X) a c =
      ResiduatedAllegory.ldiv (K := K) a c := rfl

end Scalar

namespace ThreeChain

inductive Obj | one

instance : Category Obj where
  Hom _ _ := Fin 3
  id _ := 2
  comp f g := min f g
  id_comp f := min_eq_right (by omega)
  comp_id f := min_eq_left (by omega)
  assoc f g h := min_assoc f g h

instance (X Y : Obj) : LinearOrder (X ⟶ Y) := inferInstanceAs (LinearOrder (Fin 3))
instance (X Y : Obj) (n : ℕ) : OfNat (X ⟶ Y) n := inferInstanceAs (OfNat (Fin 3) n)

instance : AllegoryCategory Obj where
  homSemilatticeInf _ _ := inferInstanceAs (SemilatticeInf (Fin 3))
  converse f := f
  converse_converse _ := rfl
  converse_comp f g := min_comm (α := Fin 3) f g
  converse_inf _ _ := rfl
  comp_mono_left h k := min_le_min_right (α := Fin 3) k h
  comp_mono_right h k := min_le_min_left (α := Fin 3) k h
  modular f g h := by
    change (f ⊓ g) ⊓ h ≤ (f ⊓ (h ⊓ g)) ⊓ g
    simp [inf_comm, inf_left_comm]

instance (X Y : Obj) : OrderBot (X ⟶ Y) := inferInstanceAs (OrderBot (Fin 3))
instance (X Y : Obj) : OrderTop (X ⟶ Y) := inferInstanceAs (OrderTop (Fin 3))

/-- Implication in a finite chain. -/
def residual (a c : Fin 3) : Fin 3 := if a ≤ c then 2 else c

theorem residual_spec (a b c : Fin 3) : b ≤ residual a c ↔ min a b ≤ c := by
  exact (by decide : ∀ a b c : Fin 3, b ≤ residual a c ↔ min a b ≤ c) a b c

instance : ResiduatedAllegoryCategory Obj where
  ldiv := residual
  rdiv c b := residual b c
  ldiv_spec := residual_spec
  rdiv_spec a b c := by
    change a ≤ residual b c ↔ min (a : Fin 3) b ≤ c
    simpa only [min_comm] using residual_spec b a c

abbrev O := Obj.one

example : (1 : O ⟶ O) ⇘ (0 : O ⟶ O) = 0 := by decide
example : (1 : O ⟶ O) ⇘ (1 : O ⟶ O) = 2 := by decide
example : (2 : O ⟶ O) ⇙ (1 : O ⟶ O) = 2 := by decide
example : ((1 : O ⟶ O) ⇘ (0 : O ⟶ O)) ⇘ (0 : O ⟶ O) = 2 := by decide

/-- The middle element has no Boolean complement. -/
theorem middle_has_no_complement :
    ¬ ∃ c : Fin 3, min 1 c = 0 ∧ max 1 c = 2 := by decide

theorem isVector (f : O ⟶ O) : IsVector f := by
  change min (f : Fin 3) 2 = f
  exact (by decide : ∀ k : Fin 3, min k 2 = k) f

example (f g : O ⟶ O) : f ⊓ g = ⊥ ↔ gᵒ ≫ f = ⊥ :=
  isVector_disjoint_iff (isVector g)

example : True := by
  fail_if_success have _ := (inferInstance : KleeneCategory Obj)
  fail_if_success have _ := (inferInstance : BooleanAlgebra (Fin 3))
  trivial

end ThreeChain

section Relations
abbrev Nats : RelCat := ℕ
abbrev Bits : RelCat := Bool
abbrev One : RelCat := Unit
abbrev EmptyObject : RelCat := Empty

example (f : Nats ⟶ Bits) (h : Nats ⟶ One) (b : Bool) :
    (b, ()) ∈ (f ⇘ h).rel ↔ ∀ n, (n, b) ∈ f.rel → (n, ()) ∈ h.rel :=
  RelCat.Hom.mem_weak_ldiv _ _ _ _

example (h : Nats ⟶ One) (g : Bits ⟶ One) (n : ℕ) (b : Bool) :
    (n, b) ∈ (h ⇙ g).rel ↔ ∀ z, (b, z) ∈ g.rel → (n, z) ∈ h.rel :=
  RelCat.Hom.mem_weak_rdiv _ _ _ _

example (f : EmptyObject ⟶ Bits) (h : EmptyObject ⟶ One) : f ⇘ h = ⊤ := by
  apply le_antisymm le_top
  intro ⟨b, z⟩ _
  apply (RelCat.Hom.mem_weak_ldiv _ _ _ _).mpr
  intro n
  exact n.elim

example (h : Nats ⟶ EmptyObject) (g : Bits ⟶ EmptyObject) : h ⇙ g = ⊤ := by
  apply le_antisymm le_top
  intro ⟨n, b⟩ _
  apply (RelCat.Hom.mem_weak_rdiv _ _ _ _).mpr
  intro z
  exact z.elim

example (f : Nats ⟶ Bits) (h : Nats ⟶ One) :
    f ⇘ h = ResiduatedKleeneCategory.ldiv f h := rfl

-- The two residuals are not interchangeable, even on a single object.
example : ResiduatedAllegoryCategory.ldiv (⊥ : Bits ⟶ Bits) (⊤ : Bits ⟶ Bits) ≠
    ResiduatedAllegoryCategory.rdiv (⊥ : Bits ⟶ Bits) (⊤ : Bits ⟶ Bits) := by
  rw [bot_ldiv]
  intro he
  have hm : (false, false) ∈
      (ResiduatedAllegoryCategory.rdiv (⊥ : Bits ⟶ Bits) ⊤).rel := by rw [← he]; trivial
  have hf := (RelCat.Hom.mem_weak_rdiv _ _ _ _).mp hm false trivial
  exact hf

end Relations

section Finite
abbrev FinBits := FinRelCat.of Bool
abbrev States := FinRelCat.of (Fin 3)

def encode : FinBits ⟶ States := fun b i ↦ decide (i.val = if b then 2 else 0)

example : (encode ⇘ encode) 0 0 = true := by decide
example : (encode ⇘ encode) 1 2 = true := by decide
example : (encode ⇘ encode) 0 2 = false := by decide
example : (encode ⇙ encode) false true = false := by decide
example : (⊥ : FinRelCat.of Empty ⟶ FinBits) ⇘ (⊥ : FinRelCat.of Empty ⟶ States) = ⊤ :=
  bot_ldiv _

end Finite

noncomputable section Compatibility

example : ResiduatedAllegoryCategory SetoidRelCat := inferInstance
example {K : Type u} [RelationAlgebra K] : ResiduatedAllegoryCategory (Matrix.Mat K) :=
  inferInstance

example (X Y Z : SetoidRelCat) (f : X ⟶ Y) (h : X ⟶ Z) :
    f ⇘ h = ResiduatedKleeneCategory.ldiv f h := rfl

example {K : Type u} [RelationAlgebra K]
    (f : (⟨2⟩ : Matrix.Mat K) ⟶ ⟨3⟩) (h : (⟨2⟩ : Matrix.Mat K) ⟶ ⟨4⟩) :
    f ⇘ h = ResiduatedKleeneCategory.ldiv f h := rfl

-- Over an arbitrary relation algebra, the two inference paths may use different
-- residual definitions. Adjoint uniqueness proves their equality on the shared order.
example {K : Type u} [RelationAlgebra K] (X : SingleObj K) (f h : X ⟶ X) :
    f ⇘ h = ResiduatedKleeneCategory.ldiv f h := ldiv_eq_kleene _ _

example (X : RelCat) (f h : End X) :
    ResiduatedAllegory.ldiv f h = ResiduatedIdemSemiring.ldiv f h := rfl

end Compatibility

end Examples.ResiduatedAllegory
