import RelationAlgebra.Models.MatrixExt

/-!
# Kleene algebra homomorphisms commute with the matrix star

If `φ : K₁ → K₂` preserves `0`, `1`, `+`, `*` and `∗`, then it also commutes with the Kleene
star of matrices:

  `(M∗).map φ = (M.map φ)∗`.

This is what makes the matrix construction *uniform* across Kleene algebras, and it is the step
that lets the completeness proof for Kleene algebra with tests move a matrix identity proved over
regular languages into an arbitrary Kleene algebra.

The proof is by induction on the size of the index type, using the block formula
`Matrix.kstar_fromBlocks`, which determines the star of a matrix from the stars of strictly
smaller ones.  Only one direction needs the induction; the other follows from the axioms.
-/

open scoped Computability

namespace Matrix

variable {K₁ K₂ : Type*} [KleeneAlgebra K₁] [KleeneAlgebra K₂] {φ : K₁ → K₂}

/-- The hypotheses making `φ` a Kleene algebra homomorphism. -/
structure IsKAHom (φ : K₁ → K₂) : Prop where
  /-- `φ` preserves `0`. -/
  map_zero : φ 0 = 0
  /-- `φ` preserves `1`. -/
  map_one : φ 1 = 1
  /-- `φ` preserves `+`. -/
  map_add : ∀ a b, φ (a + b) = φ a + φ b
  /-- `φ` preserves `*`. -/
  map_mul : ∀ a b, φ (a * b) = φ a * φ b
  /-- `φ` preserves the Kleene star. -/
  map_kstar : ∀ a, φ a∗ = (φ a)∗

namespace IsKAHom

theorem map_le (h : IsKAHom φ) {a b : K₁} (hab : a ≤ b) : φ a ≤ φ b := by
  have : φ (a + b) = φ b := by rw [add_eq_right_iff_le.2 hab]
  rw [h.map_add] at this
  exact add_eq_right_iff_le.1 this

variable {m n p : Type*}

theorem matrix_map_zero (h : IsKAHom φ) : (0 : Matrix m n K₁).map φ = 0 :=
  Matrix.map_zero φ h.map_zero

theorem matrix_map_add (h : IsKAHom φ) (A B : Matrix m n K₁) :
    (A + B).map φ = A.map φ + B.map φ :=
  Matrix.map_add φ h.map_add A B

theorem matrix_map_le (h : IsKAHom φ) {A B : Matrix m n K₁} (hAB : A ≤ B) :
    A.map φ ≤ B.map φ := fun i j ↦ h.map_le (hAB i j)

theorem matrix_map_one (h : IsKAHom φ) [DecidableEq n] : (1 : Matrix n n K₁).map φ = 1 := by
  ext i j
  simp only [Matrix.map_apply, Matrix.one_apply]
  split_ifs
  · exact h.map_one
  · exact h.map_zero

theorem matrix_map_mul (h : IsKAHom φ) [Fintype n] (A : Matrix m n K₁) (B : Matrix n p K₁) :
    (A * B).map φ = A.map φ * B.map φ := by
  ext i k
  simp only [Matrix.map_apply, Matrix.mul_apply]
  classical
  induction (Finset.univ : Finset n) using Finset.induction_on with
  | empty => simp [h.map_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, h.map_add, h.map_mul, ih]

end IsKAHom

/-! ### Reindexing commutes with the star -/

section Reindex

variable {K : Type*} [KleeneAlgebra K] {m n : Type*} [Fintype m] [DecidableEq m]
  [Fintype n] [DecidableEq n]

theorem reindex_kstar (e : n ≃ m) (M : Matrix n n K) :
    (reindex e e M)∗ = reindex e e (M∗) := by
  have hkey := (KleeneStar.ofInstance (n := n)).equiv e.symm |>.kstar_eq (reindex e e M)
  simp only [KleeneStar.equiv, KleeneStar.ofInstance] at hkey
  rw [← hkey]
  simp

end Reindex

/-! ### Reindexing commutes with `map` -/

theorem reindex_map {K₁ K₂ : Type*} {m n : Type*} (e : n ≃ m) (M : Matrix n n K₁)
    (φ : K₁ → K₂) : (reindex e e M).map φ = reindex e e (M.map φ) :=
  (Matrix.submatrix_map φ _ _ M).symm

theorem reindex_reindex_symm {A m n : Type*} (e : m ≃ n) (X : Matrix n n A) :
    reindex e e (reindex e.symm e.symm X) = X := by
  rw [← Matrix.reindex_symm, Equiv.apply_symm_apply]

/-! ### The main lemma -/

section Main

variable {K₁ K₂ : Type*} [KleeneAlgebra K₁] [KleeneAlgebra K₂] {φ : K₁ → K₂}

/-- The easy inclusion, which needs no induction. -/
theorem kstar_map_le_map_kstar (h : IsKAHom φ) {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n K₁) : (M.map φ)∗ ≤ (M∗).map φ := by
  refine kstar_le_of_mul_le_right ?_ ?_
  · rw [← h.matrix_map_one]
    exact h.matrix_map_le one_le_kstar
  · rw [← h.matrix_map_mul]
    exact h.matrix_map_le mul_kstar_le_kstar

private theorem map_kstar_blocks (h : IsKAHom φ) {N : ℕ}
    (ih : ∀ M : Matrix (Fin N) (Fin N) K₁, (M∗).map φ = (M.map φ)∗)
    (B : Matrix (Fin N ⊕ Fin 1) (Fin N ⊕ Fin 1) K₁) : (B∗).map φ = (B.map φ)∗ := by
  have hone : ∀ C : Matrix (Fin 1) (Fin 1) K₁, (C∗).map φ = (C.map φ)∗ := by
    intro C
    rw [kstar_unique, kstar_unique]
    ext i j
    simp [h.map_kstar]
  obtain ⟨A₁, A₂, A₃, A₄, rfl⟩ : ∃ a b c d, B = fromBlocks a b c d :=
    ⟨_, _, _, _, (fromBlocks_toBlocks B).symm⟩
  rw [kstar_fromBlocks, fromBlocks_map, fromBlocks_map, kstar_fromBlocks]
  have hD : (A₄∗).map φ = (A₄.map φ)∗ := hone _
  have hF : ((A₁ + A₂ * A₄∗ * A₃)∗).map φ
      = (A₁.map φ + A₂.map φ * (A₄.map φ)∗ * A₃.map φ)∗ := by
    rw [ih, h.matrix_map_add, h.matrix_map_mul, h.matrix_map_mul, hD]
  rw [fromBlocks_inj]
  refine ⟨hF, ?_, ?_, ?_⟩ <;>
    simp only [h.matrix_map_add, h.matrix_map_mul, hD, hF]

/-- Transport the statement along an equivalence of index types. -/
private theorem map_kstar_of_equiv {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] (e : m ≃ n) (hm : ∀ A : Matrix m m K₁, (A∗).map φ = (A.map φ)∗)
    (M : Matrix n n K₁) : (M∗).map φ = (M.map φ)∗ := by
  calc (M∗).map φ = ((reindex e e (reindex e.symm e.symm M))∗).map φ := by
        rw [reindex_reindex_symm]
    _ = (reindex e e ((reindex e.symm e.symm M)∗)).map φ := by rw [reindex_kstar]
    _ = reindex e e (((reindex e.symm e.symm M)∗).map φ) := reindex_map e _ φ
    _ = reindex e e (((reindex e.symm e.symm M).map φ)∗) := by rw [hm]
    _ = (reindex e e ((reindex e.symm e.symm M).map φ))∗ := (reindex_kstar e _).symm
    _ = (M.map φ)∗ := by rw [reindex_map, reindex_reindex_symm]

private theorem map_kstar_fin (h : IsKAHom φ) :
    ∀ (N : ℕ) (M : Matrix (Fin N) (Fin N) K₁), (M∗).map φ = (M.map φ)∗ := by
  intro N
  induction N with
  | zero =>
    intro M
    ext i
    exact absurd i.2 (by omega)
  | succ N ih =>
    exact map_kstar_of_equiv finSumFinEquiv (map_kstar_blocks h ih)

/-- **A Kleene algebra homomorphism commutes with the matrix star.** -/
theorem map_kstar (h : IsKAHom φ) {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n K₁) :
    (M∗).map φ = (M.map φ)∗ := by
  classical
  exact map_kstar_of_equiv (Fintype.equivFin n).symm (map_kstar_fin h (Fintype.card n)) M

end Main

end Matrix
