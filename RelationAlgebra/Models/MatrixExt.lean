import Mathlib.Computability.Language
import RelationAlgebra.Decide.Tactic
import RelationAlgebra.KAT.Defs
import RelationAlgebra.Kleene.Complete
import RelationAlgebra.Models.Matrix
import RelationAlgebra.Models.Rel
import RelationAlgebra.Typed

/-!
# Matrices over a Kleene algebra: further constructions

`RelationAlgebra.Models.Matrix` proves that `Matrix n n K` is a Kleene algebra for finite `n`
and `[KleeneAlgebra K]`, by Kozen's block construction.  This file adds the material that the
Rocq library `relation-algebra` of Damien Pous collects in `theories/matrix.v` and
`theories/matrix_ext.v`: the *rectangular* (typed) star induction rules, the star of a
block-triangular matrix, completeness, tests, and the typed structure `MX n m` of rectangular
matrices.

## Main declarations

* `Matrix.mul_kstar_le_of_rect`, `Matrix.kstar_mul_le_of_rect`: Kozen's star induction axioms
  for the Kleene algebra instance, with a *rectangular* side factor.  These do not follow
  equationally from the square ones, and they are what makes the matrix construction usable.
* `Matrix.mul_kstar_eq_kstar_mul_of_eq`: rectangular bisimulation,
  `X * M = M' * X → X * M∗ = M'∗ * X`, together with its two inequality halves.
* `Matrix.kstar_fromBlocks_diag`, `Matrix.kstar_fromBlocks_upper`,
  `Matrix.kstar_fromBlocks_lower`: the star of a block-triangular matrix.
* `Matrix.instCompleteLattice`, `Matrix.instCompleteKleeneAlgebra`: matrices over a complete
  Kleene algebra form a complete Kleene algebra.  The instance is built *on top of*
  `Matrix.instKleeneAlgebra`, so the two stars agree definitionally and
  `Matrix.kstar_eq_iSup_pow` holds.  As a consequence the `ka` tactic of
  `RelationAlgebra.Decide.Tactic` applies to matrices over relations and over languages; see
  the regression `example`s at the end of the file.
* `Matrix.kstarFin`: a *computable* star on `Matrix (Fin n) (Fin n) K`, equal to the star of the
  (noncomputable) instance (`Matrix.kstarFin_eq`).
* `Matrix.instKAT`: the diagonal matrices of tests form a Boolean algebra of tests for
  `Matrix n n K`, so matrices over a KAT form a KAT.
* `Matrix.Mat`: the *typed* structure of rectangular matrices, as a `KleeneCategory`.

## References

* [D. Kozen, *A completeness theorem for Kleene algebras and the algebra of regular events*,
  Information and Computation 110(2):366-390, 1994][kozen1994]: the matrix construction and the
  block formula for the star.
* D. Pous, the Rocq library `relation-algebra`, files `theories/matrix.v` and
  `theories/matrix_ext.v`, of which this file is a partial Lean counterpart.
-/

open scoped Computability

namespace Matrix

variable {K : Type*}

/-! ### Bilinearity of matrix multiplication for the lattice operations -/

section Bilinear

variable [IdemSemiring K] {l m n : Type*}

theorem bot_eq_zero : (⊥ : Matrix m n K) = 0 := by
  ext i j
  exact le_antisymm bot_le zero_le

variable [Fintype m]

theorem sup_mul (A B : Matrix l m K) (C : Matrix m n K) : (A ⊔ B) * C = A * C ⊔ B * C := by
  rw [← add_eq_sup, ← add_eq_sup, Matrix.add_mul]

theorem mul_sup (A : Matrix l m K) (B C : Matrix m n K) : A * (B ⊔ C) = A * B ⊔ A * C := by
  rw [← add_eq_sup, ← add_eq_sup, Matrix.mul_add]

theorem bot_mul (A : Matrix m n K) : (⊥ : Matrix l m K) * A = ⊥ := by
  rw [bot_eq_zero, Matrix.zero_mul, bot_eq_zero]

theorem mul_bot (A : Matrix l m K) : A * (⊥ : Matrix m n K) = ⊥ := by
  rw [bot_eq_zero, Matrix.mul_zero, bot_eq_zero]

end Bilinear

/-! ### Rectangular star induction and bisimulation

`RelationAlgebra.Models.Matrix` proves the rectangular induction axioms for an abstract
`Matrix.KleeneStar`; we restate them for the Kleene algebra instance itself, and deduce the
rectangular bisimulation rules.  These are the *typed* forms of Kozen's axioms (Pous,
`kleene.v`): they are strictly stronger than their square instances. -/

section Rectangular

variable [KleeneAlgebra K] {n p : Type*} [Fintype n] [DecidableEq n]

/-- Rectangular right star induction: if `X ≤ C` and `C * M ≤ C` then `X * M∗ ≤ C`. -/
theorem mul_kstar_le_of_rect {M : Matrix n n K} {X C : Matrix p n K} (h₁ : X ≤ C)
    (h₂ : C * M ≤ C) : X * M∗ ≤ C :=
  (mul_mono_left h₁ _).trans (KleeneStar.ofInstance.mul_kstar_le_self' M C h₂)

/-- Rectangular left star induction: if `X ≤ C` and `M * C ≤ C` then `M∗ * X ≤ C`. -/
theorem kstar_mul_le_of_rect {M : Matrix n n K} {X C : Matrix n p K} (h₁ : X ≤ C)
    (h₂ : M * C ≤ C) : M∗ * X ≤ C :=
  (mul_mono_right h₁ _).trans (KleeneStar.ofInstance.kstar_mul_le_self' M C h₂)

variable [Fintype p] [DecidableEq p]

/-- Rectangular bisimulation, one half: if `X` simulates `M` by `M'`, then it simulates `M∗`
by `M'∗`. -/
theorem mul_kstar_le_kstar_mul_of_rect {X : Matrix p n K} {M : Matrix n n K} {M' : Matrix p p K}
    (h : X * M ≤ M' * X) : X * M∗ ≤ M'∗ * X := by
  refine mul_kstar_le_of_rect ?_ ?_
  · calc X = 1 * X := (Matrix.one_mul X).symm
      _ ≤ M'∗ * X := mul_mono_left _root_.one_le_kstar X
  · calc M'∗ * X * M = M'∗ * (X * M) := Matrix.mul_assoc _ _ _
      _ ≤ M'∗ * (M' * X) := mul_mono_right h _
      _ = M'∗ * M' * X := (Matrix.mul_assoc _ _ _).symm
      _ ≤ M'∗ * X := mul_mono_left _root_.kstar_mul_le_kstar X

/-- Rectangular bisimulation, the other half. -/
theorem kstar_mul_le_mul_kstar_of_rect {X : Matrix p n K} {M : Matrix n n K} {M' : Matrix p p K}
    (h : M' * X ≤ X * M) : M'∗ * X ≤ X * M∗ := by
  refine kstar_mul_le_of_rect (M := M') ?_ ?_
  · calc X = X * 1 := (Matrix.mul_one X).symm
      _ ≤ X * M∗ := mul_mono_right _root_.one_le_kstar X
  · calc M' * (X * M∗) = M' * X * M∗ := (Matrix.mul_assoc _ _ _).symm
      _ ≤ X * M * M∗ := mul_mono_left h _
      _ = X * (M * M∗) := Matrix.mul_assoc _ _ _
      _ ≤ X * M∗ := mul_mono_right _root_.mul_kstar_le_kstar X

/-- **Rectangular bisimulation.**  A rectangular matrix intertwining two square matrices
intertwines their stars.  This is the typed bisimulation rule of Pous' `kleene.v`. -/
theorem mul_kstar_eq_kstar_mul_of_eq {X : Matrix p n K} {M : Matrix n n K} {M' : Matrix p p K}
    (h : X * M = M' * X) : X * M∗ = M'∗ * X :=
  le_antisymm (mul_kstar_le_kstar_mul_of_rect h.le) (kstar_mul_le_mul_kstar_of_rect h.ge)

end Rectangular

/-! ### Block-triangular matrices

All three statements are read off Kozen's block formula `Matrix.kstar_fromBlocks`. -/

section Block

variable [KleeneAlgebra K] {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- The star of a block-diagonal matrix is block-diagonal. -/
theorem kstar_fromBlocks_diag (A : Matrix m m K) (D : Matrix n n K) :
    (fromBlocks A 0 0 D)∗ = fromBlocks A∗ 0 0 D∗ := by
  rw [kstar_fromBlocks]
  simp

/-- The star of a block-upper-triangular matrix. -/
theorem kstar_fromBlocks_upper (A : Matrix m m K) (B : Matrix m n K) (D : Matrix n n K) :
    (fromBlocks A B 0 D)∗ = fromBlocks A∗ (A∗ * B * D∗) 0 D∗ := by
  rw [kstar_fromBlocks]
  simp

/-- The star of a block-lower-triangular matrix. -/
theorem kstar_fromBlocks_lower (A : Matrix m m K) (C : Matrix n m K) (D : Matrix n n K) :
    (fromBlocks A 0 C D)∗ = fromBlocks A∗ 0 (D∗ * C * A∗) D∗ := by
  rw [kstar_fromBlocks]
  simp

end Block

/-! ### Matrices over a complete Kleene algebra

Matrices over a complete lattice form a complete lattice, entrywise; when the entries form a
complete Kleene algebra, matrix multiplication distributes over arbitrary joins, because a
finite sum is itself a join.  We build the `CompleteKleeneAlgebra` structure *on top of*
`Matrix.instKleeneAlgebra`, so that the two Kleene stars are the same operation and no second,
conflicting Kleene algebra structure appears.  In particular the uniqueness of the star
(`Matrix.KleeneStar.kstar_eq`) is not even needed here, and `Matrix.kstar_eq_iSup_pow` is a
direct consequence of `CompleteKleeneAlgebra.kstar_eq_iSup_pow`. -/

section CompleteLattice

variable {m n : Type*}

/-- The entrywise complete lattice structure on `m → n → K`, transported to `Matrix m n K`.
Only used to build `Matrix.instCompleteLattice`, whose `sSup` is stated entrywise. -/
abbrev piCompleteLattice (m n : Type*) (K : Type*) [CompleteLattice K] :
    CompleteLattice (Matrix m n K) :=
  inferInstanceAs (CompleteLattice (m → n → K))

/-- Matrices over a complete lattice form a complete lattice, entrywise.  This is
definitionally compatible with the `SemilatticeSup` and `OrderBot` structures used by
`Matrix.instIdemSemiring`. -/
instance instCompleteLattice [CompleteLattice K] : CompleteLattice (Matrix m n K) where
  __ := piCompleteLattice m n K
  sSup s := of fun i j ↦ ⨆ M ∈ s, M i j
  isLUB_sSup s := ⟨fun M hM i j ↦ le_iSup₂ (f := fun N (_ : N ∈ s) ↦ N i j) M hM,
    fun _ hb i j ↦ iSup₂_le fun _ hM ↦ hb hM i j⟩

@[simp] theorem sSup_apply [CompleteLattice K] (s : Set (Matrix m n K)) (i : m) (j : n) :
    sSup s i j = ⨆ M ∈ s, M i j := rfl

end CompleteLattice

section Complete

variable [CompleteKleeneAlgebra K] {n : Type*} [Fintype n]

theorem mul_sSup_distrib (X : Matrix n n K) (s : Set (Matrix n n K)) :
    X * sSup s = ⨆ y ∈ s, X * y := by
  refine le_antisymm ?_ (iSup₂_le fun y hy ↦ mul_mono_right (le_sSup hy) X)
  have hC : ∀ y ∈ s, X * y ≤ ⨆ z ∈ s, X * z :=
    fun y hy ↦ le_iSup₂ (f := fun z (_ : z ∈ s) ↦ X * z) y hy
  intro i j
  rw [mul_apply]
  refine sum_le_of_forall_le fun k _ ↦ ?_
  rw [sSup_apply]
  simp only [CompleteKleeneAlgebra.mul_iSup]
  refine iSup₂_le fun y hy ↦ ?_
  calc X i k * y k j ≤ ∑ k' : n, X i k' * y k' j :=
        Finset.single_le_sum (f := fun k' ↦ X i k' * y k' j) (fun _ _ ↦ zero_le)
          (Finset.mem_univ k)
    _ = (X * y) i j := mul_apply.symm
    _ ≤ _ := hC y hy i j

theorem sSup_mul_distrib (s : Set (Matrix n n K)) (Y : Matrix n n K) :
    sSup s * Y = ⨆ x ∈ s, x * Y := by
  refine le_antisymm ?_ (iSup₂_le fun x hx ↦ mul_mono_left (le_sSup hx) Y)
  have hC : ∀ x ∈ s, x * Y ≤ ⨆ z ∈ s, z * Y :=
    fun x hx ↦ le_iSup₂ (f := fun z (_ : z ∈ s) ↦ z * Y) x hx
  intro i j
  rw [mul_apply]
  refine sum_le_of_forall_le fun k _ ↦ ?_
  rw [sSup_apply]
  simp only [CompleteKleeneAlgebra.iSup_mul]
  refine iSup₂_le fun x hx ↦ ?_
  calc x i k * Y k j ≤ ∑ k' : n, x i k' * Y k' j :=
        Finset.single_le_sum (f := fun k' ↦ x i k' * Y k' j) (fun _ _ ↦ zero_le)
          (Finset.mem_univ k)
    _ = (x * Y) i j := mul_apply.symm
    _ ≤ _ := hC x hx i j

variable [DecidableEq n]

/-- Square matrices over a complete Kleene algebra form a complete Kleene algebra, with the
same Kleene star as `Matrix.instKleeneAlgebra`. -/
noncomputable instance instCompleteKleeneAlgebra : CompleteKleeneAlgebra (Matrix n n K) where
  __ := instKleeneAlgebra
  __ := instCompleteLattice
  mul_sSup_distrib := mul_sSup_distrib
  sSup_mul_distrib := sSup_mul_distrib

/-- Matrices over a complete Kleene algebra are star-continuous: the star is the join of the
powers. -/
theorem kstar_eq_iSup_pow (M : Matrix n n K) : M∗ = ⨆ i : ℕ, M ^ i :=
  CompleteKleeneAlgebra.kstar_eq_iSup_pow M

end Complete

/-! ### A computable star on `Fin n` matrices

`Matrix.instKleeneAlgebra` is noncomputable because it transports the `Fin`-indexed
construction along `Fintype.equivFin`.  For `Fin n` itself the block recursion
`Matrix.KleeneStar.fin` is already structural, hence computable; we expose it and identify it
with the star of the instance using uniqueness of the star. -/

section Fin

variable [KleeneAlgebra K] {k : ℕ}

/-- The Kleene star of a `Fin k` matrix, computed by Kozen's block recursion on `k`.  Unlike
`Matrix.instKleeneAlgebra`, this is computable. -/
def kstarFin (M : Matrix (Fin k) (Fin k) K) : Matrix (Fin k) (Fin k) K :=
  (KleeneStar.fin k).kstar M

@[simp] theorem kstarFin_eq (M : Matrix (Fin k) (Fin k) K) : kstarFin M = M∗ :=
  (KleeneStar.fin k).kstar_eq M

end Fin

/-! ### Matrices over a Kleene algebra with tests

Following Pous' `matrix.v`, the tests of `Matrix n n K` are the diagonal matrices whose
diagonal entries are tests of `K`; they form the Boolean algebra `n → T`. -/

section KAT

open scoped KAT

variable [KleeneAlgebra K] {T : Type*} [BooleanAlgebra T] [KAT T K] {n : Type*} [DecidableEq n]

/-- The diagonal matrix of tests associated with a family of tests. -/
def diagTest (f : n → T) : Matrix n n K := diagonal fun i ↦ ⌜f i⌝

theorem diagTest_apply (f : n → T) (i j : n) :
    diagTest f i j = if i = j then (⌜f i⌝ : K) else 0 := rfl

variable [Fintype n]

/-- Matrices over a Kleene algebra with tests form a Kleene algebra with tests, the tests being
the diagonal matrices of tests. -/
instance instKAT : KleeneAlgebraWithTests (n → T) (Matrix n n K) where
  test := diagTest
  test_bot := by
    rw [diagTest]
    simp only [Pi.bot_apply, KAT.test_bot]
    exact diagonal_zero
  test_top := by
    rw [diagTest]
    simp only [Pi.top_apply, KAT.test_top]
    exact diagonal_one
  test_sup a b := by
    simp only [diagTest, Pi.sup_apply, KAT.test_sup]
    rw [← diagonal_add]
  test_inf a b := by
    simp only [diagTest, Pi.inf_apply, KAT.test_inf]
    rw [diagonal_mul_diagonal]

theorem test_eq_diagTest (f : n → T) :
    (KleeneAlgebraWithTests.test f : Matrix n n K) = diagTest f := rfl

end KAT

/-! ### Rectangular matrices as a typed Kleene algebra

Pous' `matrix.v` builds a *typed* structure `MX n m`, not merely a family of Kleene algebras of
square matrices.  We reproduce this with `RelationAlgebra.Typed.KleeneCategory`.

Mathlib's `Matrix` is indexed by arbitrary types, so the "category of all finite index types"
would be a large category whose objects live in an arbitrary universe and would have to be
`Σ`-bundled together with their `Fintype` and `DecidableEq` instances; the resulting object
type is not a set and the bundling adds nothing mathematically, since every finite type is
equivalent to some `Fin k`.  We therefore take the concrete skeleton: objects are natural
numbers (wrapped in the one-field structure `Matrix.Mat K`, so as not to put a category
structure on `ℕ` itself, which already carries the preorder category instance), and
`X ⟶ Y` is `Matrix (Fin X.dim) (Fin Y.dim) K`. -/

section Category

open CategoryTheory

/-- An object of the category of rectangular matrices over `K`: a dimension `dim : ℕ`,
standing for the index type `Fin dim`. -/
structure Mat (K : Type*) where
  /-- The dimension of the object; the corresponding index type is `Fin dim`. -/
  dim : ℕ

namespace Mat

variable [KleeneAlgebra K]

/-- Rectangular matrices over `K` form a category: `X ⟶ Y` is `Matrix (Fin X.dim) (Fin Y.dim) K`,
the identity is the identity matrix and composition is matrix multiplication. -/
instance instCategory : Category (Mat K) where
  Hom X Y := Matrix (Fin X.dim) (Fin Y.dim) K
  id _ := 1
  comp f g := f * g
  id_comp := Matrix.one_mul
  comp_id := Matrix.mul_one
  assoc f g h := Matrix.mul_assoc f g h

theorem hom_def (X Y : Mat K) : (X ⟶ Y) = Matrix (Fin X.dim) (Fin Y.dim) K := rfl

/-- Rectangular matrices over a Kleene algebra form a Kleene category: this is the typed
structure `MX n m` of Pous' `matrix.v`.  The rectangular star induction rules are exactly
`Matrix.mul_kstar_le_of_rect` and `Matrix.kstar_mul_le_of_rect`. -/
noncomputable instance instKleeneCategory : KleeneCategory (Mat K) where
  homSemilatticeSup _ _ := Matrix.instSemilatticeSup
  homOrderBot _ _ := Matrix.instOrderBot
  sup_comp f g h := Matrix.sup_mul f g h
  comp_sup f g h := Matrix.mul_sup f g h
  bot_comp f := Matrix.bot_mul f
  comp_bot f := Matrix.mul_bot f
  kstar {X} f := KStar.kstar (α := Matrix (Fin X.dim) (Fin X.dim) K) f
  id_le_kstar {X} f := _root_.one_le_kstar (α := Matrix (Fin X.dim) (Fin X.dim) K) (a := f)
  comp_kstar_le_kstar {X} f :=
    _root_.mul_kstar_le_kstar (α := Matrix (Fin X.dim) (Fin X.dim) K) (a := f)
  kstar_comp_le_kstar {X} f :=
    _root_.kstar_mul_le_kstar (α := Matrix (Fin X.dim) (Fin X.dim) K) (a := f)
  comp_kstar_le_self _ _ h := Matrix.mul_kstar_le_of_rect le_rfl h
  kstar_comp_le_self _ _ h := Matrix.kstar_mul_le_of_rect le_rfl h

end Mat

end Category

end Matrix

/-! ### Regression tests: the `ka` tactic on matrices

Since `Matrix n n K` is a `CompleteKleeneAlgebra` whenever `K` is, the reflexive decision
procedure of `RelationAlgebra.Decide.Tactic` applies to matrices over languages and over
relations. -/

section Tests

open scoped SetRel
open CategoryTheory

/-- Denesting, for `2 × 2` matrices over the Kleene algebra of languages. -/
example (M N : Matrix (Fin 2) (Fin 2) (Language ℕ)) : (M + N)∗ = M∗ * (N * M∗)∗ := by ka

/-- Idempotence of the star, for `2 × 2` matrices over languages. -/
example (M : Matrix (Fin 2) (Fin 2) (Language ℕ)) : M∗ * M∗ = M∗ := by ka

/-- Sliding, for `2 × 2` matrices over the Kleene algebra of relations. -/
example (M N : Matrix (Fin 2) (Fin 2) (SetRel ℕ ℕ)) : M * (N * M)∗ = (M * N)∗ * M := by ka

/-- An inequality, for `2 × 2` matrices over relations. -/
example (M : Matrix (Fin 2) (Fin 2) (SetRel ℕ ℕ)) : 1 + M * M∗ ≤ M∗ := by ka

/-- The typed sliding rule is available for rectangular matrices. -/
example {K : Type*} [KleeneAlgebra K] {X Y : Matrix.Mat K} (f : X ⟶ Y) (g : Y ⟶ X) :
    f ≫ (g ≫ f)∗ = (f ≫ g)∗ ≫ f :=
  KleeneCategory.comp_kstar_eq_kstar_comp f g

/-- Typed bisimulation is available for rectangular matrices. -/
example {K : Type*} [KleeneAlgebra K] {X Y : Matrix.Mat K} (f : X ⟶ X) (g : Y ⟶ Y)
    (h : X ⟶ Y) (hfg : f ≫ h = h ≫ g) : f∗ ≫ h = h ≫ g∗ :=
  KleeneCategory.kstar_comp_eq_comp_kstar_of_eq hfg

end Tests
