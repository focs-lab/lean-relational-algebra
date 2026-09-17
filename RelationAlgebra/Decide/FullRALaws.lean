import RelationAlgebra.Models.MatrixResidual

/-!
# Supporting laws for Boolean and residual normalization

These equations and implications are used directly by the proof-producing extension
of `ra`. Boolean operations and residuals are not passed to the Kleene-only erasure theorem.
-/

open CategoryTheory
open scoped Computability RelationAlgebra

namespace RelationAlgebra.FullRALaws

variable {K : Type*} [KleeneAlgebra K]

theorem sup_mul (a b c : K) : (a ⊔ b) * c = a * c ⊔ b * c := by
  simp only [← add_eq_sup, add_mul]

theorem mul_sup (a b c : K) : a * (b ⊔ c) = a * b ⊔ a * c := by
  simp only [← add_eq_sup, mul_add]

theorem bot_mul (a : K) : (⊥ : K) * a = ⊥ := by rw [bot_eq_zero, zero_mul]
theorem mul_bot (a : K) : a * (⊥ : K) = ⊥ := by rw [bot_eq_zero, mul_zero]
theorem kstar_bot : (⊥ : K)∗ = 1 := by rw [bot_eq_zero, kstar_zero]

omit [KleeneAlgebra K] in
theorem le_ldiv [ResiduatedKleeneAlgebra K] {a b c : K} (h : a * b ≤ c) : b ≤ a ⇘ c :=
  (ResiduatedIdemSemiring.ldiv_spec _ _ _).mpr h

omit [KleeneAlgebra K] in
theorem le_rdiv [ResiduatedKleeneAlgebra K] {a b c : K} (h : a * b ≤ c) : a ≤ c ⇙ b :=
  (ResiduatedIdemSemiring.rdiv_spec _ _ _).mpr h

section Dedekind
variable [RelationAlgebra K]

omit [KleeneAlgebra K] in
theorem dedekind_comm (a b c : K) : c ⊓ (a * b) ≤
    (a ⊓ c * star b) * (b ⊓ star a * c) := by
  rw [inf_comm]
  exact RelationAlgebra.dedekind _ _ _
end Dedekind

section Typed
variable {C : Type*} [Category C] [KleeneCategory C] [ResiduatedKleeneCategory C]
  {X Y Z : C}

open scoped ResiduatedKleeneCategory

omit [ResiduatedKleeneCategory C] in
theorem typed_kstar_bot : (⊥ : X ⟶ X)∗ = 𝟙 X := kstar_zero (α := End X)

theorem typed_le_ldiv {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} (hh : f ≫ g ≤ h) :
    g ≤ f ⇘ h := (ResiduatedKleeneCategory.ldiv_spec _ _ _).mpr hh

theorem typed_le_rdiv {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} (hh : f ≫ g ≤ h) :
    f ≤ h ⇙ g := (ResiduatedKleeneCategory.rdiv_spec _ _ _).mpr hh
section Relation
variable [BooleanKleeneCategory C] [KleeneCategoryWithConverse C] [RelationCategory C]

open scoped KleeneCategoryWithConverse

omit [ResiduatedKleeneCategory C] in
theorem typed_dedekind_comm (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) :
    h ⊓ (f ≫ g) ≤ (f ⊓ h ≫ gᵒ) ≫ (g ⊓ fᵒ ≫ h) := by
  rw [inf_comm]
  exact RelationCategory.dedekind _ _ _
end Relation
end Typed
end RelationAlgebra.FullRALaws
