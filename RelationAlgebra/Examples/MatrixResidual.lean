import RelationAlgebra.Models.MatrixResidual

/-! # Rectangular residuals, empty dimensions, and square-model compatibility -/

open CategoryTheory
open scoped RelationAlgebra ResiduatedKleeneCategory KleeneCategoryWithConverse

namespace MatrixResidualExamples

section General
variable {K : Type*} [ResiduatedKleeneLattice K]

theorem rectangular_left (A : Matrix (Fin 2) (Fin 3) K)
    (B : Matrix (Fin 3) (Fin 4) K) (H : Matrix (Fin 2) (Fin 4) K) :
    B ≤ Matrix.lres A H ↔ A * B ≤ H := Matrix.le_lres_iff _ _ _

theorem rectangular_right (A : Matrix (Fin 2) (Fin 3) K)
    (B : Matrix (Fin 3) (Fin 4) K) (H : Matrix (Fin 2) (Fin 4) K) :
    A ≤ Matrix.rres H B ↔ A * B ≤ H := Matrix.le_rres_iff _ _ _

/-- No source constraints means every matrix is allowed. -/
theorem empty_source (A : Matrix (Fin 0) (Fin 3) K) (H : Matrix (Fin 0) (Fin 4) K) :
    Matrix.lres A H = fun _ _ ↦ ⊤ := by
  ext i j
  simp [Matrix.lres]

/-- No target constraints likewise produces top, not the zero matrix. -/
theorem empty_target (H : Matrix (Fin 2) (Fin 0) K) (B : Matrix (Fin 3) (Fin 0) K) :
    Matrix.rres H B = fun _ _ ↦ ⊤ := by
  ext i j
  simp [Matrix.rres]

example (A H : Matrix (Fin 2) (Fin 2) K) :
    ResiduatedIdemSemiring.ldiv A H = Matrix.lres A H := rfl

example (A H : Matrix (Fin 2) (Fin 2) K) :
    ResiduatedIdemSemiring.rdiv H A = Matrix.rres H A := rfl

example (A : (⟨2⟩ : Matrix.Mat K) ⟶ ⟨3⟩) (H : (⟨2⟩ : Matrix.Mat K) ⟶ ⟨4⟩) :
    ResiduatedKleeneCategory.ldiv A H = Matrix.lres A H := rfl

example (B : (⟨3⟩ : Matrix.Mat K) ⟶ ⟨4⟩) (H : (⟨2⟩ : Matrix.Mat K) ⟶ ⟨4⟩) :
    ResiduatedKleeneCategory.rdiv H B = Matrix.rres H B := rfl

end General

section Boolean
variable {K : Type*} [RelationAlgebra K]

/-- The finite-meet residual agrees with the independent Boolean construction. -/
theorem complement_formula (A : (⟨2⟩ : Matrix.Mat K) ⟶ ⟨3⟩)
    (H : (⟨2⟩ : Matrix.Mat K) ⟶ ⟨4⟩) :
    Matrix.lres A H = (Aᵒ ≫ Hᶜ)ᶜ := ResiduatedKleeneCategory.ldiv_eq_compl A H

noncomputable example : RelationAlgebra (Matrix (Fin 0) (Fin 0) K) := inferInstance
noncomputable example : RelationAlgebra (Matrix (Fin 2) (Fin 2) K) := inferInstance

example (A : (⟨2⟩ : Matrix.Mat K) ⟶ ⟨3⟩) (B : (⟨3⟩ : Matrix.Mat K) ⟶ ⟨4⟩)
    (H : (⟨2⟩ : Matrix.Mat K) ⟶ ⟨4⟩) :
    (A ≫ B) ⊓ H ≤ (A ⊓ H ≫ Bᵒ) ≫ (B ⊓ Aᵒ ≫ H) := RelationCategory.dedekind _ _ _

end Boolean
end MatrixResidualExamples
