import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Logic.Equiv.Fin.Basic
import RelationAlgebra.Kleene.Basic

/-!
# Matrices over a Kleene algebra

If `K` is a Kleene algebra and `n` is a finite type, then `Matrix n n K` is again a Kleene
algebra (Kozen).  Addition, multiplication, `0` and `1` are the usual matrix operations (from
Mathlib's `Matrix.semiring`), the order is entrywise, and the star is given, for a `2 × 2`
block matrix, by the formula

  `(fromBlocks A B C D)∗ = fromBlocks F (F * B * D∗) (D∗ * C * F) (D∗ + D∗ * C * F * B * D∗)`
  where `F = (A + B * D∗ * C)∗`

(`Matrix.kstar_fromBlocks`).  The construction proceeds by induction on the size of the index
type, splitting `Fin (k + 1) ≃ Fin k ⊕ Fin 1`, and is transported to an arbitrary finite index
type along `Fintype.equivFin`.  Since the star of a Kleene algebra is uniquely determined by
the axioms (`Matrix.KleeneStar.kstar_eq`), the block formula holds for the resulting instance
whatever the chosen enumeration.

This is the Lean counterpart of `matrix.v` in Pous' `relation-algebra` library.

## Main declarations

* `Matrix.instIdemSemiring`: `Matrix n n K` is an idempotent semiring when `K` is.
* `Matrix.instKleeneAlgebra`: `Matrix n n K` is a Kleene algebra when `K` is.
* `Matrix.kstar_fromBlocks`: the block formula for the star.
-/

open scoped Computability

namespace Matrix

variable {K : Type*}

/-! ### The entrywise order on matrices over an idempotent semiring -/

section IdemSemiring

variable [IdemSemiring K] {l m n o : Type*}

instance instSemilatticeSup : SemilatticeSup (Matrix m n K) :=
  inferInstanceAs (SemilatticeSup (m → n → K))

instance instOrderBot : OrderBot (Matrix m n K) := inferInstanceAs (OrderBot (m → n → K))

theorem le_def {A B : Matrix m n K} : A ≤ B ↔ ∀ i j, A i j ≤ B i j := Iff.rfl

@[simp] theorem sup_apply (A B : Matrix m n K) (i : m) (j : n) : (A ⊔ B) i j = A i j ⊔ B i j :=
  rfl

@[simp] theorem bot_apply (i : m) (j : n) : (⊥ : Matrix m n K) i j = ⊥ := rfl

theorem add_eq_sup (A B : Matrix m n K) : A + B = A ⊔ B := by
  ext i j
  exact _root_.add_eq_sup _ _

protected theorem zero_le (A : Matrix m n K) : 0 ≤ A := fun _ _ ↦ zero_le

theorem add_le_iff {A B C : Matrix m n K} : A + B ≤ C ↔ A ≤ C ∧ B ≤ C :=
  ⟨fun h ↦ ⟨fun i j ↦ (_root_.add_le_iff.1 (h i j)).1, fun i j ↦ (_root_.add_le_iff.1 (h i j)).2⟩,
    fun h i j ↦ _root_.add_le_iff.2 ⟨h.1 i j, h.2 i j⟩⟩

protected theorem add_le {A B C : Matrix m n K} (hA : A ≤ C) (hB : B ≤ C) : A + B ≤ C :=
  add_le_iff.2 ⟨hA, hB⟩

protected theorem le_self_add (A B : Matrix m n K) : A ≤ A + B := fun _ _ ↦ le_self_add

protected theorem le_add_self (A B : Matrix m n K) : B ≤ A + B := fun _ _ ↦ le_add_self

protected theorem add_le_add {A B C D : Matrix m n K} (h₁ : A ≤ C) (h₂ : B ≤ D) :
    A + B ≤ C + D :=
  fun i j ↦ _root_.add_le_add (h₁ i j) (h₂ i j)

/-- Matrix multiplication is monotone in both arguments. -/
theorem mul_le_mul_of_le [Fintype m] {A B : Matrix l m K} {C D : Matrix m n K} (h₁ : A ≤ B)
    (h₂ : C ≤ D) : A * C ≤ B * D := fun i j ↦ by
  simp only [mul_apply]
  exact Finset.sum_le_sum fun k _ ↦ mul_le_mul' (h₁ i k) (h₂ k j)

@[gcongr]
theorem mul_mono_right [Fintype m] {C D : Matrix m n K} (h : C ≤ D) (A : Matrix l m K) :
    A * C ≤ A * D :=
  mul_le_mul_of_le le_rfl h

@[gcongr]
theorem mul_mono_left [Fintype m] {A B : Matrix l m K} (h : A ≤ B) (C : Matrix m n K) :
    A * C ≤ B * C :=
  mul_le_mul_of_le h le_rfl

theorem fromBlocks_le_fromBlocks {A A' : Matrix n l K} {B B' : Matrix n m K} {C C' : Matrix o l K}
    {D D' : Matrix o m K} :
    fromBlocks A B C D ≤ fromBlocks A' B' C' D' ↔ A ≤ A' ∧ B ≤ B' ∧ C ≤ C' ∧ D ≤ D' := by
  constructor
  · intro h
    exact ⟨fun i j ↦ h (Sum.inl i) (Sum.inl j), fun i j ↦ h (Sum.inl i) (Sum.inr j),
      fun i j ↦ h (Sum.inr i) (Sum.inl j), fun i j ↦ h (Sum.inr i) (Sum.inr j)⟩
  · rintro ⟨hA, hB, hC, hD⟩ (i | i) (j | j)
    exacts [hA i j, hB i j, hC i j, hD i j]

theorem reindex_le_reindex_iff (e₁ : m ≃ l) (e₂ : n ≃ o) {A B : Matrix m n K} :
    reindex e₁ e₂ A ≤ reindex e₁ e₂ B ↔ A ≤ B := by
  constructor
  · intro h i j
    simpa using h (e₁ i) (e₂ j)
  · intro h i j
    exact h _ _

theorem reindex_mul [Fintype m] [Fintype n] (e : m ≃ n) (A B : Matrix m m K) :
    reindex e e (A * B) = reindex e e A * reindex e e B := by
  simp

theorem reindex_one [DecidableEq m] [DecidableEq n] (e : m ≃ n) :
    reindex e e (1 : Matrix m m K) = 1 :=
  submatrix_one_equiv e.symm

omit [IdemSemiring K] in
theorem reindex_symm_reindex (e : m ≃ n) (M : Matrix m m K) :
    reindex e.symm e.symm (reindex e e M) = M := by
  simp

/-- Square matrices over an idempotent semiring form an idempotent semiring. -/
instance instIdemSemiring [Fintype n] [DecidableEq n] : IdemSemiring (Matrix n n K) where
  __ := Matrix.semiring
  __ := instSemilatticeSup
  __ := instOrderBot
  add_eq_sup := add_eq_sup

end IdemSemiring

/-! ### Kleene stars on square matrices -/

section KleeneAlgebra

variable [KleeneAlgebra K]

/-- Auxiliary structure: a Kleene star on `n × n` matrices over `K` satisfying Kozen's axioms.
The construction of the Kleene algebra `Matrix n n K` proceeds by building such a structure by
induction on the size of `n`. -/
structure KleeneStar (n : Type*) [Fintype n] [DecidableEq n] (K : Type*) [KleeneAlgebra K] where
  /-- The star operation. -/
  kstar : Matrix n n K → Matrix n n K
  one_le_kstar (M : Matrix n n K) : 1 ≤ kstar M
  mul_kstar_le_kstar (M : Matrix n n K) : M * kstar M ≤ kstar M
  kstar_mul_le_kstar (M : Matrix n n K) : kstar M * M ≤ kstar M
  mul_kstar_le_self (M X : Matrix n n K) : X * M ≤ X → X * kstar M ≤ X
  kstar_mul_le_self (M X : Matrix n n K) : M * X ≤ X → kstar M * X ≤ X

namespace KleeneStar

section Rectangular

variable {n : Type*} [Fintype n] [DecidableEq n] (S : KleeneStar n K)

/-- The induction axiom with a rectangular left factor, obtained from the square one by
considering the square matrix all of whose rows are a given row. -/
theorem mul_kstar_le_self' {p : Type*} (M : Matrix n n K) (X : Matrix p n K) (h : X * M ≤ X) :
    X * S.kstar M ≤ X := by
  intro i j
  let Xi : Matrix n n K := of fun _ k ↦ X i k
  have hrow : ∀ (N : Matrix n n K) (a b : n), (Xi * N) a b = (X * N) i b := fun N a b ↦ by
    simp only [mul_apply, Xi, of_apply]
  have hXi : Xi * M ≤ Xi := fun a b ↦ by
    rw [hrow]
    exact h i b
  have := S.mul_kstar_le_self M Xi hXi j j
  rwa [hrow] at this

/-- The induction axiom with a rectangular right factor. -/
theorem kstar_mul_le_self' {p : Type*} (M : Matrix n n K) (X : Matrix n p K) (h : M * X ≤ X) :
    S.kstar M * X ≤ X := by
  intro i j
  let Xj : Matrix n n K := of fun k _ ↦ X k j
  have hcol : ∀ (N : Matrix n n K) (a b : n), (N * Xj) a b = (N * X) a j := fun N a b ↦ by
    simp only [mul_apply, Xj, of_apply]
  have hXj : M * Xj ≤ Xj := fun a b ↦ by
    rw [hcol]
    exact h a j
  have := S.kstar_mul_le_self M Xj hXj i i
  rwa [hcol] at this

end Rectangular

section Transport

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- Transport a Kleene star along an equivalence of index types. -/
def equiv (e : m ≃ n) (S : KleeneStar n K) : KleeneStar m K where
  kstar M := reindex e.symm e.symm (S.kstar (reindex e e M))
  one_le_kstar M :=
    calc (1 : Matrix m m K) = reindex e.symm e.symm 1 := (reindex_one e.symm).symm
      _ ≤ _ := (reindex_le_reindex_iff _ _).2 (S.one_le_kstar _)
  mul_kstar_le_kstar M :=
    calc M * reindex e.symm e.symm (S.kstar (reindex e e M))
        = reindex e.symm e.symm (reindex e e M * S.kstar (reindex e e M)) := by
          rw [reindex_mul, reindex_symm_reindex]
      _ ≤ _ := (reindex_le_reindex_iff _ _).2 (S.mul_kstar_le_kstar _)
  kstar_mul_le_kstar M :=
    calc reindex e.symm e.symm (S.kstar (reindex e e M)) * M
        = reindex e.symm e.symm (S.kstar (reindex e e M) * reindex e e M) := by
          rw [reindex_mul, reindex_symm_reindex]
      _ ≤ _ := (reindex_le_reindex_iff _ _).2 (S.kstar_mul_le_kstar _)
  mul_kstar_le_self M X h := by
    have h' : reindex e e X * reindex e e M ≤ reindex e e X := by
      rw [← reindex_mul]
      exact (reindex_le_reindex_iff _ _).2 h
    calc X * reindex e.symm e.symm (S.kstar (reindex e e M))
        = reindex e.symm e.symm (reindex e e X * S.kstar (reindex e e M)) := by
          rw [reindex_mul, reindex_symm_reindex]
      _ ≤ reindex e.symm e.symm (reindex e e X) :=
          (reindex_le_reindex_iff _ _).2 (S.mul_kstar_le_self _ _ h')
      _ = X := reindex_symm_reindex e X
  kstar_mul_le_self M X h := by
    have h' : reindex e e M * reindex e e X ≤ reindex e e X := by
      rw [← reindex_mul]
      exact (reindex_le_reindex_iff _ _).2 h
    calc reindex e.symm e.symm (S.kstar (reindex e e M)) * X
        = reindex e.symm e.symm (S.kstar (reindex e e M) * reindex e e X) := by
          rw [reindex_mul, reindex_symm_reindex]
      _ ≤ reindex e.symm e.symm (reindex e e X) :=
          (reindex_le_reindex_iff _ _).2 (S.kstar_mul_le_self _ _ h')
      _ = X := reindex_symm_reindex e X

end Transport

section Base

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The (unique) Kleene star on matrices indexed by an empty type. -/
def empty [IsEmpty n] : KleeneStar n K where
  kstar M := M
  one_le_kstar _ i _ := isEmptyElim i
  mul_kstar_le_kstar _ i _ := isEmptyElim i
  kstar_mul_le_kstar _ i _ := isEmptyElim i
  mul_kstar_le_self _ _ _ i _ := isEmptyElim i
  kstar_mul_le_self _ _ _ i _ := isEmptyElim i

/-- The Kleene star on `1 × 1` matrices: the star of the unique entry. -/
def unique [Unique n] : KleeneStar n K where
  kstar M := of fun _ _ ↦ (M default default)∗
  one_le_kstar M i j := by
    obtain rfl : i = default := Subsingleton.elim _ _
    obtain rfl : j = default := Subsingleton.elim _ _
    simp only [one_apply_eq, of_apply]
    exact _root_.one_le_kstar
  mul_kstar_le_kstar M i j := by
    obtain rfl : i = default := Subsingleton.elim _ _
    obtain rfl : j = default := Subsingleton.elim _ _
    simp only [mul_apply, Fintype.sum_unique, of_apply]
    exact _root_.mul_kstar_le_kstar
  kstar_mul_le_kstar M i j := by
    obtain rfl : i = default := Subsingleton.elim _ _
    obtain rfl : j = default := Subsingleton.elim _ _
    simp only [mul_apply, Fintype.sum_unique, of_apply]
    exact _root_.kstar_mul_le_kstar
  mul_kstar_le_self M X h i j := by
    obtain rfl : i = default := Subsingleton.elim _ _
    obtain rfl : j = default := Subsingleton.elim _ _
    have := h default default
    simp only [mul_apply, Fintype.sum_unique] at this
    simp only [mul_apply, Fintype.sum_unique, of_apply]
    exact _root_.mul_kstar_le_self this
  kstar_mul_le_self M X h i j := by
    obtain rfl : i = default := Subsingleton.elim _ _
    obtain rfl : j = default := Subsingleton.elim _ _
    have := h default default
    simp only [mul_apply, Fintype.sum_unique] at this
    simp only [mul_apply, Fintype.sum_unique, of_apply]
    exact _root_.kstar_mul_le_self this

end Base

/-! ### The block construction -/

section Block

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- The block formula for the star of `fromBlocks A B C D`, given a star `Ds` for `D` and a
star `F` for `A + B * Ds * C`. -/
def blockStar (B : Matrix m n K) (C : Matrix n m K) (Ds : Matrix n n K) (F : Matrix m m K) :
    Matrix (m ⊕ n) (m ⊕ n) K :=
  fromBlocks F (F * B * Ds) (Ds * C * F) (Ds + Ds * C * F * B * Ds)

variable (S : KleeneStar m K) (T : KleeneStar n K)
  (A : Matrix m m K) (B : Matrix m n K) (C : Matrix n m K) (D : Matrix n n K)

theorem one_le_blockStar :
    1 ≤ blockStar B C (T.kstar D) (S.kstar (A + B * T.kstar D * C)) := by
  rw [blockStar, ← fromBlocks_one, fromBlocks_le_fromBlocks]
  exact ⟨S.one_le_kstar _, Matrix.zero_le _, Matrix.zero_le _,
    (T.one_le_kstar D).trans (Matrix.le_self_add _ _)⟩

theorem mul_blockStar_le :
    fromBlocks A B C D * blockStar B C (T.kstar D) (S.kstar (A + B * T.kstar D * C)) ≤
      blockStar B C (T.kstar D) (S.kstar (A + B * T.kstar D * C)) := by
  set Ds := T.kstar D with hDs
  set G := A + B * Ds * C with hG
  set F := S.kstar G with hF
  have hDs1 : 1 ≤ Ds := T.one_le_kstar D
  have hDs2 : D * Ds ≤ Ds := T.mul_kstar_le_kstar D
  have hF1 : 1 ≤ F := S.one_le_kstar G
  have hGF : G * F ≤ F := S.mul_kstar_le_kstar G
  have hAG : A ≤ G := Matrix.le_self_add _ _
  have hBDsCG : B * Ds * C ≤ G := Matrix.le_add_self _ _
  rw [blockStar, fromBlocks_multiply, fromBlocks_le_fromBlocks]
  refine ⟨Matrix.add_le ?_ ?_, Matrix.add_le ?_ ?_, Matrix.add_le ?_ ?_, Matrix.add_le ?_ ?_⟩
  · calc A * F ≤ G * F := mul_mono_left hAG F
      _ ≤ F := hGF
  · calc B * (Ds * C * F) = B * Ds * C * F := by simp only [Matrix.mul_assoc]
      _ ≤ G * F := mul_mono_left hBDsCG F
      _ ≤ F := hGF
  · calc A * (F * B * Ds) = A * F * (B * Ds) := by simp only [Matrix.mul_assoc]
      _ ≤ G * F * (B * Ds) := mul_mono_left (mul_mono_left hAG F) _
      _ ≤ F * (B * Ds) := mul_mono_left hGF _
      _ = F * B * Ds := (Matrix.mul_assoc _ _ _).symm
  · rw [Matrix.mul_add]
    refine Matrix.add_le ?_ ?_
    · calc B * Ds = 1 * (B * Ds) := (Matrix.one_mul _).symm
        _ ≤ F * (B * Ds) := mul_mono_left hF1 _
        _ = F * B * Ds := (Matrix.mul_assoc _ _ _).symm
    · calc B * (Ds * C * F * B * Ds) = B * Ds * C * F * (B * Ds) := by
            simp only [Matrix.mul_assoc]
        _ ≤ G * F * (B * Ds) := mul_mono_left (mul_mono_left hBDsCG F) _
        _ ≤ F * (B * Ds) := mul_mono_left hGF _
        _ = F * B * Ds := (Matrix.mul_assoc _ _ _).symm
  · calc C * F = 1 * (C * F) := (Matrix.one_mul _).symm
      _ ≤ Ds * (C * F) := mul_mono_left hDs1 _
      _ = Ds * C * F := (Matrix.mul_assoc _ _ _).symm
  · calc D * (Ds * C * F) = D * Ds * (C * F) := by simp only [Matrix.mul_assoc]
      _ ≤ Ds * (C * F) := mul_mono_left hDs2 _
      _ = Ds * C * F := (Matrix.mul_assoc _ _ _).symm
  · calc C * (F * B * Ds) = 1 * (C * F * B * Ds) := by simp only [Matrix.mul_assoc, Matrix.one_mul]
      _ ≤ Ds * (C * F * B * Ds) := mul_mono_left hDs1 _
      _ = Ds * C * F * B * Ds := by simp only [Matrix.mul_assoc]
      _ ≤ Ds + Ds * C * F * B * Ds := Matrix.le_add_self _ _
  · rw [Matrix.mul_add]
    refine Matrix.add_le ?_ ?_
    · exact hDs2.trans (Matrix.le_self_add _ _)
    · calc D * (Ds * C * F * B * Ds) = D * Ds * (C * F * B * Ds) := by
            simp only [Matrix.mul_assoc]
        _ ≤ Ds * (C * F * B * Ds) := mul_mono_left hDs2 _
        _ = Ds * C * F * B * Ds := by simp only [Matrix.mul_assoc]
        _ ≤ Ds + Ds * C * F * B * Ds := Matrix.le_add_self _ _

theorem blockStar_mul_le :
    blockStar B C (T.kstar D) (S.kstar (A + B * T.kstar D * C)) * fromBlocks A B C D ≤
      blockStar B C (T.kstar D) (S.kstar (A + B * T.kstar D * C)) := by
  set Ds := T.kstar D with hDs
  set G := A + B * Ds * C with hG
  set F := S.kstar G with hF
  have hDs1 : 1 ≤ Ds := T.one_le_kstar D
  have hDs3 : Ds * D ≤ Ds := T.kstar_mul_le_kstar D
  have hF1 : 1 ≤ F := S.one_le_kstar G
  have hFG : F * G ≤ F := S.kstar_mul_le_kstar G
  have hAG : A ≤ G := Matrix.le_self_add _ _
  have hBDsCG : B * Ds * C ≤ G := Matrix.le_add_self _ _
  rw [blockStar, fromBlocks_multiply, fromBlocks_le_fromBlocks]
  refine ⟨Matrix.add_le ?_ ?_, Matrix.add_le ?_ ?_, Matrix.add_le ?_ ?_, Matrix.add_le ?_ ?_⟩
  · calc F * A ≤ F * G := mul_mono_right hAG F
      _ ≤ F := hFG
  · calc F * B * Ds * C = F * (B * Ds * C) := by simp only [Matrix.mul_assoc]
      _ ≤ F * G := mul_mono_right hBDsCG F
      _ ≤ F := hFG
  · calc F * B = F * B * 1 := (Matrix.mul_one _).symm
      _ ≤ F * B * Ds := mul_mono_right hDs1 _
  · calc F * B * Ds * D = F * B * (Ds * D) := by simp only [Matrix.mul_assoc]
      _ ≤ F * B * Ds := mul_mono_right hDs3 _
  · calc Ds * C * F * A = Ds * C * (F * A) := by simp only [Matrix.mul_assoc]
      _ ≤ Ds * C * (F * G) := mul_mono_right (mul_mono_right hAG F) _
      _ ≤ Ds * C * F := mul_mono_right hFG _
  · rw [Matrix.add_mul]
    refine Matrix.add_le ?_ ?_
    · calc Ds * C = Ds * C * 1 := (Matrix.mul_one _).symm
        _ ≤ Ds * C * F := mul_mono_right hF1 _
    · calc Ds * C * F * B * Ds * C = Ds * C * (F * (B * Ds * C)) := by
            simp only [Matrix.mul_assoc]
        _ ≤ Ds * C * (F * G) := mul_mono_right (mul_mono_right hBDsCG F) _
        _ ≤ Ds * C * F := mul_mono_right hFG _
  · calc Ds * C * F * B = Ds * C * F * B * 1 := (Matrix.mul_one _).symm
      _ ≤ Ds * C * F * B * Ds := mul_mono_right hDs1 _
      _ ≤ Ds + Ds * C * F * B * Ds := Matrix.le_add_self _ _
  · rw [Matrix.add_mul]
    refine Matrix.add_le ?_ ?_
    · exact hDs3.trans (Matrix.le_self_add _ _)
    · calc Ds * C * F * B * Ds * D = Ds * C * F * B * (Ds * D) := by simp only [Matrix.mul_assoc]
        _ ≤ Ds * C * F * B * Ds := mul_mono_right hDs3 _
        _ ≤ Ds + Ds * C * F * B * Ds := Matrix.le_add_self _ _

/-- The right-induction axiom for a row of blocks. -/
theorem rowBlock_le {p : Type*} (Y₁ : Matrix p m K) (Y₂ : Matrix p n K) (h₁ : Y₁ * A ≤ Y₁)
    (h₂ : Y₂ * C ≤ Y₁) (h₃ : Y₁ * B ≤ Y₂) (h₄ : Y₂ * D ≤ Y₂) :
    Y₁ * S.kstar (A + B * T.kstar D * C) + Y₂ * (T.kstar D * C * S.kstar (A + B * T.kstar D * C))
        ≤ Y₁ ∧
      Y₁ * (S.kstar (A + B * T.kstar D * C) * B * T.kstar D) +
        Y₂ * (T.kstar D + T.kstar D * C * S.kstar (A + B * T.kstar D * C) * B * T.kstar D)
          ≤ Y₂ := by
  set Ds := T.kstar D with hDs
  set G := A + B * Ds * C with hG
  set F := S.kstar G with hF
  have hY₂Ds : Y₂ * Ds ≤ Y₂ := T.mul_kstar_le_self' D Y₂ h₄
  have hY₁F : Y₁ * F ≤ Y₁ := by
    refine S.mul_kstar_le_self' G Y₁ ?_
    rw [hG, Matrix.mul_add]
    refine Matrix.add_le h₁ ?_
    calc Y₁ * (B * Ds * C) = Y₁ * B * Ds * C := by simp only [Matrix.mul_assoc]
      _ ≤ Y₂ * Ds * C := mul_mono_left (mul_mono_left h₃ _) _
      _ ≤ Y₂ * C := mul_mono_left hY₂Ds _
      _ ≤ Y₁ := h₂
  refine ⟨Matrix.add_le hY₁F ?_, Matrix.add_le ?_ ?_⟩
  · calc Y₂ * (Ds * C * F) = Y₂ * Ds * C * F := by simp only [Matrix.mul_assoc]
      _ ≤ Y₂ * C * F := mul_mono_left (mul_mono_left hY₂Ds _) _
      _ ≤ Y₁ * F := mul_mono_left h₂ _
      _ ≤ Y₁ := hY₁F
  · calc Y₁ * (F * B * Ds) = Y₁ * F * B * Ds := by simp only [Matrix.mul_assoc]
      _ ≤ Y₁ * B * Ds := mul_mono_left (mul_mono_left hY₁F _) _
      _ ≤ Y₂ * Ds := mul_mono_left h₃ _
      _ ≤ Y₂ := hY₂Ds
  · rw [Matrix.mul_add]
    refine Matrix.add_le hY₂Ds ?_
    calc Y₂ * (Ds * C * F * B * Ds) = Y₂ * Ds * C * F * B * Ds := by simp only [Matrix.mul_assoc]
      _ ≤ Y₂ * C * F * B * Ds :=
          mul_mono_left (mul_mono_left (mul_mono_left (mul_mono_left hY₂Ds _) _) _) _
      _ ≤ Y₁ * F * B * Ds := mul_mono_left (mul_mono_left (mul_mono_left h₂ _) _) _
      _ ≤ Y₁ * B * Ds := mul_mono_left (mul_mono_left hY₁F _) _
      _ ≤ Y₂ * Ds := mul_mono_left h₃ _
      _ ≤ Y₂ := hY₂Ds

/-- The left-induction axiom for a column of blocks. -/
theorem colBlock_le {p : Type*} (Z₁ : Matrix m p K) (Z₂ : Matrix n p K) (h₁ : A * Z₁ ≤ Z₁)
    (h₂ : B * Z₂ ≤ Z₁) (h₃ : C * Z₁ ≤ Z₂) (h₄ : D * Z₂ ≤ Z₂) :
    S.kstar (A + B * T.kstar D * C) * Z₁ + S.kstar (A + B * T.kstar D * C) * B * T.kstar D * Z₂
        ≤ Z₁ ∧
      T.kstar D * C * S.kstar (A + B * T.kstar D * C) * Z₁ +
        (T.kstar D + T.kstar D * C * S.kstar (A + B * T.kstar D * C) * B * T.kstar D) * Z₂
          ≤ Z₂ := by
  set Ds := T.kstar D with hDs
  set G := A + B * Ds * C with hG
  set F := S.kstar G with hF
  have hDsZ₂ : Ds * Z₂ ≤ Z₂ := T.kstar_mul_le_self' D Z₂ h₄
  have hFZ₁ : F * Z₁ ≤ Z₁ := by
    refine S.kstar_mul_le_self' G Z₁ ?_
    rw [hG, Matrix.add_mul]
    refine Matrix.add_le h₁ ?_
    calc B * Ds * C * Z₁ = B * (Ds * (C * Z₁)) := by simp only [Matrix.mul_assoc]
      _ ≤ B * (Ds * Z₂) := mul_mono_right (mul_mono_right h₃ _) _
      _ ≤ B * Z₂ := mul_mono_right hDsZ₂ _
      _ ≤ Z₁ := h₂
  refine ⟨Matrix.add_le hFZ₁ ?_, Matrix.add_le ?_ ?_⟩
  · calc F * B * Ds * Z₂ = F * (B * (Ds * Z₂)) := by simp only [Matrix.mul_assoc]
      _ ≤ F * (B * Z₂) := mul_mono_right (mul_mono_right hDsZ₂ _) _
      _ ≤ F * Z₁ := mul_mono_right h₂ _
      _ ≤ Z₁ := hFZ₁
  · calc Ds * C * F * Z₁ = Ds * (C * (F * Z₁)) := by simp only [Matrix.mul_assoc]
      _ ≤ Ds * (C * Z₁) := mul_mono_right (mul_mono_right hFZ₁ _) _
      _ ≤ Ds * Z₂ := mul_mono_right h₃ _
      _ ≤ Z₂ := hDsZ₂
  · rw [Matrix.add_mul]
    refine Matrix.add_le hDsZ₂ ?_
    calc Ds * C * F * B * Ds * Z₂ = Ds * (C * (F * (B * (Ds * Z₂)))) := by
          simp only [Matrix.mul_assoc]
      _ ≤ Ds * (C * (F * (B * Z₂))) :=
          mul_mono_right (mul_mono_right (mul_mono_right (mul_mono_right hDsZ₂ _) _) _) _
      _ ≤ Ds * (C * (F * Z₁)) := mul_mono_right (mul_mono_right (mul_mono_right h₂ _) _) _
      _ ≤ Ds * (C * Z₁) := mul_mono_right (mul_mono_right hFZ₁ _) _
      _ ≤ Ds * Z₂ := mul_mono_right h₃ _
      _ ≤ Z₂ := hDsZ₂

theorem mul_blockStar_le_self (X : Matrix (m ⊕ n) (m ⊕ n) K) (h : X * fromBlocks A B C D ≤ X) :
    X * blockStar B C (T.kstar D) (S.kstar (A + B * T.kstar D * C)) ≤ X := by
  rw [← fromBlocks_toBlocks X] at h ⊢
  rw [fromBlocks_multiply, fromBlocks_le_fromBlocks] at h
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  rw [add_le_iff] at h₁ h₂ h₃ h₄
  rw [blockStar, fromBlocks_multiply, fromBlocks_le_fromBlocks]
  obtain ⟨r₁, r₂⟩ := rowBlock_le S T A B C D _ _ h₁.1 h₁.2 h₂.1 h₂.2
  obtain ⟨r₃, r₄⟩ := rowBlock_le S T A B C D _ _ h₃.1 h₃.2 h₄.1 h₄.2
  exact ⟨r₁, r₂, r₃, r₄⟩

theorem blockStar_mul_le_self (X : Matrix (m ⊕ n) (m ⊕ n) K) (h : fromBlocks A B C D * X ≤ X) :
    blockStar B C (T.kstar D) (S.kstar (A + B * T.kstar D * C)) * X ≤ X := by
  rw [← fromBlocks_toBlocks X] at h ⊢
  rw [fromBlocks_multiply, fromBlocks_le_fromBlocks] at h
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  rw [add_le_iff] at h₁ h₂ h₃ h₄
  rw [blockStar, fromBlocks_multiply, fromBlocks_le_fromBlocks]
  obtain ⟨c₁, c₃⟩ := colBlock_le S T A B C D _ _ h₁.1 h₁.2 h₃.1 h₃.2
  obtain ⟨c₂, c₄⟩ := colBlock_le S T A B C D _ _ h₂.1 h₂.2 h₄.1 h₄.2
  exact ⟨c₁, c₂, c₃, c₄⟩

/-- Kleene stars on `m × m` and `n × n` matrices combine to one on `(m ⊕ n) × (m ⊕ n)`
matrices, via the block formula. -/
def sum : KleeneStar (m ⊕ n) K where
  kstar M := blockStar M.toBlocks₁₂ M.toBlocks₂₁ (T.kstar M.toBlocks₂₂)
    (S.kstar (M.toBlocks₁₁ + M.toBlocks₁₂ * T.kstar M.toBlocks₂₂ * M.toBlocks₂₁))
  one_le_kstar M := one_le_blockStar S T _ _ _ _
  mul_kstar_le_kstar M := by
    have := mul_blockStar_le S T M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂
    rwa [fromBlocks_toBlocks] at this
  kstar_mul_le_kstar M := by
    have := blockStar_mul_le S T M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂
    rwa [fromBlocks_toBlocks] at this
  mul_kstar_le_self M X h := by
    refine mul_blockStar_le_self S T M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ X ?_
    rwa [fromBlocks_toBlocks]
  kstar_mul_le_self M X h := by
    refine blockStar_mul_le_self S T M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ X ?_
    rwa [fromBlocks_toBlocks]

end Block

/-! ### Induction on the size -/

/-- A Kleene star on `Fin k` matrices, by induction on `k`. -/
def fin : ∀ k : ℕ, KleeneStar (Fin k) K
  | 0 => empty
  | k + 1 => ((fin k).sum unique).equiv finSumFinEquiv.symm

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The Kleene algebra structure on `Matrix n n K` determined by a Kleene star. -/
abbrev toKleeneAlgebra (S : KleeneStar n K) : KleeneAlgebra (Matrix n n K) where
  __ := instIdemSemiring
  kstar := S.kstar
  one_le_kstar := S.one_le_kstar
  mul_kstar_le_kstar := S.mul_kstar_le_kstar
  kstar_mul_le_kstar := S.kstar_mul_le_kstar
  mul_kstar_le_self := S.mul_kstar_le_self
  kstar_mul_le_self := S.kstar_mul_le_self

end KleeneStar

/-- Square matrices over a Kleene algebra form a Kleene algebra. -/
noncomputable instance instKleeneAlgebra {n : Type*} [Fintype n] [DecidableEq n] :
    KleeneAlgebra (Matrix n n K) :=
  ((KleeneStar.fin (Fintype.card n)).equiv (Fintype.equivFin n)).toKleeneAlgebra

namespace KleeneStar

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The Kleene star of `Matrix n n K` is unique: any structure satisfying the axioms agrees with
the instance. -/
theorem kstar_eq (S : KleeneStar n K) (M : Matrix n n K) : S.kstar M = M∗ :=
  le_antisymm
    (calc S.kstar M = S.kstar M * 1 := (Matrix.mul_one _).symm
      _ ≤ S.kstar M * M∗ := mul_mono_right _root_.one_le_kstar _
      _ ≤ M∗ := S.kstar_mul_le_self M M∗ _root_.mul_kstar_le_kstar)
    (kstar_le_of_mul_le_right (S.one_le_kstar M) (S.mul_kstar_le_kstar M))

/-- The Kleene star of the instance, packaged as a `KleeneStar`. -/
noncomputable def ofInstance : KleeneStar n K where
  kstar M := M∗
  one_le_kstar _ := _root_.one_le_kstar
  mul_kstar_le_kstar _ := _root_.mul_kstar_le_kstar
  kstar_mul_le_kstar _ := _root_.kstar_mul_le_kstar
  mul_kstar_le_self _ _ := _root_.mul_kstar_le_self
  kstar_mul_le_self _ _ := _root_.kstar_mul_le_self

end KleeneStar

/-- **The block formula for the Kleene star of a matrix.** -/
theorem kstar_fromBlocks {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m m K) (B : Matrix m n K) (C : Matrix n m K) (D : Matrix n n K) :
    (fromBlocks A B C D)∗ =
      fromBlocks (A + B * D∗ * C)∗ ((A + B * D∗ * C)∗ * B * D∗) (D∗ * C * (A + B * D∗ * C)∗)
        (D∗ + D∗ * C * (A + B * D∗ * C)∗ * B * D∗) := by
  have := (KleeneStar.ofInstance.sum KleeneStar.ofInstance).kstar_eq (fromBlocks A B C D)
  rw [← this]
  simp only [KleeneStar.sum, KleeneStar.blockStar, KleeneStar.ofInstance, toBlocks_fromBlocks₁₁,
    toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂]

/-- The star of a `1 × 1` matrix is the star of its entry. -/
theorem kstar_unique {n : Type*} [Fintype n] [DecidableEq n] [Unique n] (M : Matrix n n K) :
    M∗ = of fun _ _ ↦ (M default default)∗ :=
  (KleeneStar.unique.kstar_eq M).symm

end KleeneAlgebra

end Matrix
