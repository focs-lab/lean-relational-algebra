import RelationAlgebra.TypedResiduated
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Rectangular matrix residuals

Over a `ResiduatedKleeneLattice`, residual entries are finite meets of scalar residuals.
The construction needs no Boolean operations, converse, or complete lattice. Empty
index types give empty meets, hence top entries. This is the factors construction of
Damien Pous' `theories/matrix.v`.

We also provide the pointwise Boolean and Dedekind structure for matrices over a relation
algebra, and connect the rectangular operations to `Matrix.Mat` and square-matrix algebra.
-/

open CategoryTheory
open scoped Computability RelationAlgebra

universe u

namespace Matrix

variable {K : Type u}

/-- Finite sums in an idempotent semiring are finite joins. -/
theorem sum_eq_sup [IdemSemiring K] {ι : Type*} (s : Finset ι) (f : ι → K) :
    s.sum f = s.sup f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [_root_.bot_eq_zero]
  | @insert i s hi ih => rw [Finset.sum_insert hi, Finset.sup_insert, ih, _root_.add_eq_sup]

section Residual
variable [ResiduatedKleeneLattice K] {l m n : Type*}

/-- A rectangular left residual meets constraints over the common source dimension. -/
def lres [Fintype l] (A : Matrix l m K) (H : Matrix l n K) : Matrix m n K :=
  fun j k ↦ Finset.univ.inf fun i ↦ A i j ⇘ H i k

/-- A rectangular right residual meets constraints over the common target dimension. -/
def rres [Fintype n] (H : Matrix l n K) (B : Matrix m n K) : Matrix l m K :=
  fun i j ↦ Finset.univ.inf fun k ↦ H i k ⇙ B j k

/-- Left matrix residuation is right adjoint to rectangular multiplication. -/
theorem le_lres_iff [Fintype l] [Fintype m] (A : Matrix l m K) (B : Matrix m n K)
    (H : Matrix l n K) : B ≤ lres A H ↔ A * B ≤ H := by
  simp only [le_def, lres, Finset.le_inf_iff, Finset.mem_univ, forall_const,
    ResiduatedIdemSemiring.ldiv_spec, mul_apply, sum_eq_sup, Finset.sup_le_iff]
  constructor
  · intro h i k j; exact h j k i
  · intro h j k i; exact h i k j

/-- Right matrix residuation is right adjoint to rectangular multiplication. -/
theorem le_rres_iff [Fintype m] [Fintype n] (A : Matrix l m K) (B : Matrix m n K)
    (H : Matrix l n K) : A ≤ rres H B ↔ A * B ≤ H := by
  simp only [le_def, rres, Finset.le_inf_iff, Finset.mem_univ, forall_const,
    ResiduatedIdemSemiring.rdiv_spec, mul_apply, sum_eq_sup, Finset.sup_le_iff]
  constructor
  · intro h i k j; exact h i j k
  · intro h i j k; exact h i k j

/-- Square matrices inherit both scalar residuals and the existing Kleene star. -/
noncomputable instance instResiduatedKleeneLattice [Fintype n] [DecidableEq n] :
    ResiduatedKleeneLattice (Matrix n n K) where
  __ := Matrix.instKleeneAlgebra
  __ := (inferInstance : Lattice (n → n → K))
  top := fun _ _ ↦ ⊤
  le_top _ _ _ := le_top
  ldiv := lres
  rdiv := rres
  ldiv_spec := le_lres_iff
  rdiv_spec := le_rres_iff

noncomputable instance Mat.instResiduatedKleeneCategory :
    ResiduatedKleeneCategory (Mat K) where
  ldiv := lres
  rdiv := rres
  ldiv_spec := le_lres_iff
  rdiv_spec := le_rres_iff

end Residual

section Boolean
variable [RelationAlgebra K] {l m n : Type*}

noncomputable instance instBooleanAlgebra : BooleanAlgebra (Matrix m n K) :=
  inferInstanceAs (BooleanAlgebra (m → n → K))

noncomputable instance Mat.instBooleanKleeneCategory : BooleanKleeneCategory (Mat K) where
  inf f g := fun i j ↦ f i j ⊓ g i j
  top := fun _ _ ↦ ⊤
  compl f := fun i j ↦ (f i j)ᶜ
  inf_le_left _ _ _ _ := inf_le_left
  inf_le_right _ _ _ _ := inf_le_right
  le_inf _ _ _ hf hg i j := le_inf (hf i j) (hg i j)
  le_sup_inf _ _ _ _ _ := le_sup_inf
  le_top _ _ _ := le_top
  inf_compl_le_bot _ _ _ := by simp
  top_le_sup_compl f i j := by
    change ⊤ ≤ f i j ⊔ (f i j)ᶜ
    simp

/-- One summand is below a matrix product, for arbitrary rectangular dimensions. -/
theorem entry_mul_le [Fintype m] (A : Matrix l m K) (B : Matrix m n K) (i j k) :
    A i j * B j k ≤ (A * B) i k := by
  rw [mul_apply, sum_eq_sup]
  exact Finset.le_sup (f := fun j ↦ A i j * B j k) (Finset.mem_univ j)

/-- Dedekind's law survives finite matrix multiplication. -/
theorem dedekind [Fintype l] [Fintype m] [Fintype n]
    (A : Matrix l m K) (B : Matrix m n K) (H : Matrix l n K) :
    (A * B) ⊓ H ≤ (A ⊓ H * B.conjTranspose) * (B ⊓ A.conjTranspose * H) := by
  intro i k
  change (A * B) i k ⊓ H i k ≤ _
  rw [mul_apply, sum_eq_sup, Finset.sup_inf_distrib_right]
  apply Finset.sup_le
  intro j _
  calc (A i j * B j k) ⊓ H i k ≤
      (A i j ⊓ H i k * star (B j k)) * (B j k ⊓ star (A i j) * H i k) :=
      RelationAlgebra.dedekind _ _ _
    _ ≤ (A i j ⊓ (H * B.conjTranspose) i j) *
        (B j k ⊓ (A.conjTranspose * H) j k) :=
      mul_le_mul' (inf_le_inf_left _ (entry_mul_le H B.conjTranspose i k j))
        (inf_le_inf_left _ (entry_mul_le A.conjTranspose H j i k))
    _ ≤ ((A ⊓ H * B.conjTranspose) * (B ⊓ A.conjTranspose * H)) i k :=
      entry_mul_le (A ⊓ H * B.conjTranspose) (B ⊓ A.conjTranspose * H) i j k

noncomputable instance Mat.instRelationCategory : RelationCategory (Mat K) where
  dedekind := Matrix.dedekind

/-- Square matrices over a relation algebra form a relation algebra. -/
noncomputable instance instRelationAlgebra [Fintype n] [DecidableEq n] :
    RelationAlgebra (Matrix n n K) where
  __ := Matrix.instKleeneAlgebra
  __ := Matrix.instBooleanAlgebra
  star := Matrix.conjTranspose
  star_involutive := Matrix.conjTranspose_conjTranspose
  star_mul := Matrix.conjTranspose_mul
  star_add := Matrix.conjTranspose_add
  dedekind := Matrix.dedekind

/-- Compatibility with Mathlib's existing matrix converse instance. -/
@[simp] theorem star_inf [Fintype n] [DecidableEq n] (A B : Matrix n n K) :
    star (A ⊓ B) = star A ⊓ star B := RelationAlgebra.star_inf _ _

@[simp] theorem star_compl (A : Matrix m n K) :
    Aᶜ.conjTranspose = A.conjTransposeᶜ := by
  ext i j
  exact RelationAlgebra.star_compl _

@[simp] theorem star_top [Fintype n] [DecidableEq n] : star (⊤ : Matrix n n K) = ⊤ :=
  RelationAlgebra.star_top

end Boolean
end Matrix
