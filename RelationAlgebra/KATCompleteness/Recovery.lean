import RelationAlgebra.KATCompleteness.Encode

/-!
# The matrix interpretation computes the value of a KAT term

Fix a Kleene algebra with tests and `k` test variables.  Interpreting the action `p` as the
matrix `⌜α⌝ * ρ p * ⌜β⌝` at the entry `(α, β)` gives, for each KAT term `e`, a matrix
`valMat e` over `K`, and the value of `e` is recovered by sandwiching that matrix between the
row and column vectors of atoms:

  `eval τ ρ e = U * valMat e * V`,   `U i = ⌜α_i⌝`,  `V i = ⌜α_i⌝`.

The two vectors satisfy `U * V = 1` and `V * U = D`, where `D` is the diagonal matrix of atoms,
and every matrix in the image of the interpretation satisfies the invariant `D * X = D * X * D`.
This says that right multiplication by `D` leaves `D * X` unchanged; it does not require
`D * X = X` or `X * D = X`.  For `X = 1`, the invariant reduces to `D = D * D`, which holds
even when `D ≠ 1`.
Those three facts drive the whole induction, the star case included; nothing here assumes
completeness, star-continuity or finiteness of `K` or `T`.

## References

* Damien Pous, `relation-algebra`, `theories/kat_completeness.v`, after D. Kozen and F. Smith,
  *Kleene algebra with tests: completeness and decidability*, CSL'96.
-/

open scoped Computability KAT

namespace KAT.Completeness

variable {T K : Type*} [BooleanAlgebra T] [KleeneAlgebra K] [KAT T K] (τ : ℕ → T) (ρ : ℕ → K)
  (k : ℕ)

/-! ### The vectors of atoms -/

/-- The row vector of atoms. -/
def rowVec : Matrix Unit (Idx k) K := fun _ i => atomVal τ k i

/-- The column vector of atoms. -/
def colVec : Matrix (Idx k) Unit K := fun i _ => atomVal τ k i

/-- The diagonal matrix of atoms. -/
def diagVec : Matrix (Idx k) (Idx k) K := fun i j => if i = j then atomVal τ k i else 0

/-- The interpretation of an action: `⌜α⌝ * ρ p * ⌜β⌝` at the entry `(α, β)`. -/
def actMat : ℕ → Matrix (Idx k) (Idx k) K :=
  fun p i j => atomVal τ k i * ρ p * atomVal τ k j

/-- The matrix interpretation of a KAT term in `K`. -/
noncomputable def valMat : KTerm → Matrix (Idx k) (Idx k) K := evalMat (actMat τ ρ k)

/-! ### The basic identities -/

theorem row_mul_col : rowVec τ k * colVec τ k = (1 : Matrix Unit Unit K) := by
  ext u v
  obtain rfl : u = v := Subsingleton.elim u v
  rw [Matrix.mul_apply, Matrix.one_apply_eq]
  simp only [rowVec, colVec]
  rw [Finset.sum_congr rfl fun i _ ↦ atomVal_mul_self τ k i, sum_atomVal]

theorem col_mul_row :
    colVec τ k * rowVec τ k = (diagVec τ k : Matrix (Idx k) (Idx k) K) := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [colVec, rowVec, diagVec, Finset.sum_const, Finset.card_univ, Fintype.card_unit,
    one_smul]
  exact atomVal_mul τ k i j

theorem diag_le_one : (diagVec τ k : Matrix (Idx k) (Idx k) K) ≤ 1 := by
  intro i j
  simp only [diagVec, Matrix.one_apply]
  split_ifs
  · exact atomVal_le_one τ k i
  · exact le_rfl

theorem row_mul_diag :
    rowVec τ k * diagVec τ k = (rowVec τ k : Matrix Unit (Idx k) K) := by
  ext u j
  rw [Matrix.mul_apply]
  simp only [rowVec, diagVec]
  rw [Finset.sum_eq_single j (fun b _ hb ↦ by rw [if_neg hb, mul_zero])
    (fun hb ↦ absurd (Finset.mem_univ _) hb), if_pos rfl]
  exact atomVal_mul_self τ k j

theorem diag_mul_col :
    diagVec τ k * colVec τ k = (colVec τ k : Matrix (Idx k) Unit K) := by
  ext i u
  rw [Matrix.mul_apply]
  simp only [diagVec, colVec]
  rw [Finset.sum_eq_single i (fun b _ hb ↦ by rw [if_neg (Ne.symm hb), zero_mul])
    (fun hb ↦ absurd (Finset.mem_univ _) hb), if_pos rfl]
  exact atomVal_mul_self τ k i

theorem diag_mul_diag :
    diagVec τ k * diagVec τ k = (diagVec τ k : Matrix (Idx k) (Idx k) K) := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [diagVec]
  rw [Finset.sum_eq_single i (fun b _ hb ↦ by rw [if_neg (Ne.symm hb), zero_mul])
    (fun hb ↦ absurd (Finset.mem_univ _) hb), if_pos rfl]
  split_ifs with h
  · subst h
    exact atomVal_mul_self τ k i
  · rw [mul_zero]

theorem diag_mul_apply (X : Matrix (Idx k) (Idx k) K) (i j : Idx k) :
    ((diagVec τ k * X : Matrix (Idx k) (Idx k) K)) i j = atomVal τ k i * X i j := by
  rw [Matrix.mul_apply]
  simp only [diagVec]
  rw [Finset.sum_eq_single i (fun b _ hb ↦ by rw [if_neg (Ne.symm hb), zero_mul])
    (fun hb ↦ absurd (Finset.mem_univ _) hb), if_pos rfl]

theorem mul_diag_apply {m : Type*} (X : Matrix m (Idx k) K) (i : m) (j : Idx k) :
    ((X * diagVec τ k : Matrix m (Idx k) K)) i j = X i j * atomVal τ k j := by
  rw [Matrix.mul_apply]
  simp only [diagVec]
  rw [Finset.sum_eq_single j (fun b _ hb ↦ by rw [if_neg hb, mul_zero])
    (fun hb ↦ absurd (Finset.mem_univ _) hb), if_pos rfl]

/-! ### The invariant -/

/-- The invariant satisfied by every matrix in the image of the interpretation:
`D * X = D * X * D`, where `D` is the diagonal of atoms.  It asserts that right multiplication
by `D` leaves `D * X` unchanged, without requiring `D * X = X` or `X * D = X`. -/
def Good (X : Matrix (Idx k) (Idx k) K) : Prop := diagVec τ k * X = diagVec τ k * X * diagVec τ k

theorem good_iff (X : Matrix (Idx k) (Idx k) K) :
    Good τ k X ↔ ∀ i j, atomVal τ k i * X i j = atomVal τ k i * X i j * atomVal τ k j := by
  rw [Good]
  constructor
  · intro h i j
    have hij := Matrix.ext_iff.mpr h i j
    rwa [mul_diag_apply, diag_mul_apply] at hij
  · intro h
    ext i j
    rw [mul_diag_apply, diag_mul_apply]
    exact h i j

theorem good_zero : Good τ k (0 : Matrix (Idx k) (Idx k) K) :=
  (good_iff τ k (0 : Matrix (Idx k) (Idx k) K)).2 fun i j ↦ by simp

theorem good_one : Good τ k (1 : Matrix (Idx k) (Idx k) K) := by
  refine (good_iff τ k (1 : Matrix (Idx k) (Idx k) K)).2 fun i j ↦ ?_
  rw [Matrix.one_apply]
  split_ifs with h
  · subst h
    simpa using (atomVal_mul_self (K := K) τ k i).symm
  · rw [mul_zero, zero_mul]

theorem good_testMat (b : BTerm) : Good τ k (testMat k K b) := by
  refine (good_iff τ k (testMat k K b)).2 fun i j ↦ ?_
  simp only [testMat]
  split_ifs with h
  · obtain ⟨rfl, -⟩ := h
    simpa using (atomVal_mul_self (K := K) τ k i).symm
  · rw [mul_zero, zero_mul]

theorem good_actMat (p : ℕ) : Good τ k (actMat τ ρ k p) := by
  refine (good_iff τ k (actMat τ ρ k p)).2 fun i j ↦ ?_
  simp only [actMat]
  conv_rhs => rw [mul_assoc, mul_assoc (atomVal τ k i * ρ p), atomVal_mul_self]

theorem good_add {X Y : Matrix (Idx k) (Idx k) K} (hX : Good τ k X) (hY : Good τ k Y) :
    Good τ k (X + Y) := by
  rw [Good, Matrix.mul_add, Matrix.add_mul, ← hX, ← hY]

theorem good_mul {X Y : Matrix (Idx k) (Idx k) K} (hX : Good τ k X) (hY : Good τ k Y) :
    Good τ k (X * Y) := by
  rw [Good]
  calc diagVec τ k * (X * Y) = diagVec τ k * X * diagVec τ k * Y := by
        rw [← hX]
        simp only [Matrix.mul_assoc]
    _ = diagVec τ k * X * (diagVec τ k * Y * diagVec τ k) := by
        rw [← hY]
        simp only [Matrix.mul_assoc]
    _ = diagVec τ k * X * diagVec τ k * Y * diagVec τ k := by simp only [Matrix.mul_assoc]
    _ = diagVec τ k * (X * Y) * diagVec τ k := by
        rw [← hX]
        simp only [Matrix.mul_assoc]

theorem good_kstar {X : Matrix (Idx k) (Idx k) K} (hX : Good τ k X) : Good τ k (X∗) := by
  have hDX : diagVec τ k * X ≤ X := by
    have h := Matrix.mul_mono_left (diag_le_one τ k) X
    rwa [Matrix.one_mul] at h
  refine le_antisymm ?_ ?_
  · refine mul_kstar_le ?_ ?_
    · have h1 : diagVec τ k * (1 : Matrix (Idx k) (Idx k) K) * diagVec τ k
          ≤ diagVec τ k * X∗ * diagVec τ k :=
        Matrix.mul_mono_left (Matrix.mul_mono_right one_le_kstar _) _
      rwa [Matrix.mul_one, diag_mul_diag τ k] at h1
    · calc diagVec τ k * X∗ * diagVec τ k * X
          = diagVec τ k * X∗ * (diagVec τ k * X) := Matrix.mul_assoc _ _ _
        _ = diagVec τ k * X∗ * (diagVec τ k * X * diagVec τ k) := by rw [← hX]
        _ ≤ diagVec τ k * X∗ * (X * diagVec τ k) :=
            Matrix.mul_mono_right (Matrix.mul_mono_left hDX _) _
        _ = diagVec τ k * (X∗ * X) * diagVec τ k := by simp only [Matrix.mul_assoc]
        _ ≤ diagVec τ k * X∗ * diagVec τ k :=
            Matrix.mul_mono_left (Matrix.mul_mono_right kstar_mul_le_kstar _) _
  · have h2 : diagVec τ k * X∗ * diagVec τ k ≤ diagVec τ k * X∗ * 1 :=
      Matrix.mul_mono_right (diag_le_one τ k) _
    rwa [Matrix.mul_one] at h2

theorem good_valMat (e : KTerm) : Good τ k (valMat τ ρ k e) := by
  induction e with
  | zero => exact good_zero τ k
  | one => exact good_one τ k
  | test b => exact good_testMat τ k b
  | act p => exact good_actMat τ ρ k p
  | add e f ihe ihf => exact good_add τ k ihe ihf
  | mul e f ihe ihf => exact good_mul τ k ihe ihf
  | star e ih => exact good_kstar τ k ih

/-! ### Scalars as `Unit`-indexed matrices -/

/-- A scalar viewed as a `1 × 1` matrix. -/
def scalarMat (x : K) : Matrix Unit Unit K := fun _ _ => x

omit [KleeneAlgebra K] in
@[simp] theorem scalarMat_apply (x : K) (u v : Unit) : scalarMat x u v = x := rfl

@[simp] theorem scalarMat_zero : scalarMat (0 : K) = 0 := rfl

theorem scalarMat_one : scalarMat (1 : K) = 1 := by
  ext u v
  obtain rfl : u = v := Subsingleton.elim u v
  rw [scalarMat_apply, Matrix.one_apply_eq]

theorem scalarMat_add (x y : K) : scalarMat (x + y) = scalarMat x + scalarMat y := rfl

theorem scalarMat_mul (x y : K) : scalarMat (x * y) = scalarMat x * scalarMat y := by
  ext u v
  rw [Matrix.mul_apply]
  simp only [scalarMat_apply, Finset.sum_const, Finset.card_univ, Fintype.card_unit, one_smul]

theorem scalarMat_kstar (x : K) : scalarMat (x∗) = (scalarMat x)∗ := by
  rw [Matrix.kstar_unique]
  rfl

omit [KleeneAlgebra K] in
theorem scalarMat_injective : Function.Injective (scalarMat (K := K)) :=
  fun _ _ h => congrFun (congrFun h ()) ()

/-! ### Sandwiching -/

theorem row_mul_good {X : Matrix (Idx k) (Idx k) K} (hX : Good τ k X) :
    rowVec τ k * X * diagVec τ k = rowVec τ k * X := by
  ext u j
  rw [mul_diag_apply, Matrix.mul_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ ↦ ((good_iff τ k X).1 hX i j).symm

theorem row_mul_sandwich {X : Matrix (Idx k) (Idx k) K} (hX : Good τ k X) :
    rowVec τ k * X * colVec τ k * rowVec τ k = rowVec τ k * X := by
  calc rowVec τ k * X * colVec τ k * rowVec τ k
      = rowVec τ k * X * (colVec τ k * rowVec τ k) := Matrix.mul_assoc _ _ _
    _ = rowVec τ k * X * diagVec τ k := by rw [col_mul_row τ k]
    _ = rowVec τ k * X := row_mul_good τ k hX

theorem sandwich_mul {X Y : Matrix (Idx k) (Idx k) K} (hX : Good τ k X) :
    rowVec τ k * (X * Y) * colVec τ k
      = rowVec τ k * X * colVec τ k * (rowVec τ k * Y * colVec τ k) := by
  set U : Matrix Unit (Idx k) K := rowVec τ k with hUdef
  set V : Matrix (Idx k) Unit K := colVec τ k with hVdef
  have hU : U * X * V * U = U * X := row_mul_sandwich τ k hX
  calc U * (X * Y) * V = U * X * Y * V := by rw [Matrix.mul_assoc U X Y]
    _ = U * X * V * U * Y * V := by rw [hU]
    _ = U * X * V * (U * Y * V) := by
        rw [Matrix.mul_assoc (U * X * V) U Y, Matrix.mul_assoc (U * X * V) (U * Y) V]

theorem sandwich_kstar {X : Matrix (Idx k) (Idx k) K} (hX : Good τ k X) :
    rowVec τ k * X∗ * colVec τ k = (rowVec τ k * X * colVec τ k)∗ := by
  set U : Matrix Unit (Idx k) K := rowVec τ k with hUdef
  set V : Matrix (Idx k) Unit K := colVec τ k with hVdef
  have hUV : U * V = (1 : Matrix Unit Unit K) := row_mul_col τ k
  have hU : U * X * V * U = U * X := row_mul_sandwich τ k hX
  set x : Matrix Unit Unit K := U * X * V with hx
  refine le_antisymm ?_ ?_
  · have hstep : x∗ * U * X ≤ x∗ * U := by
      calc x∗ * U * X = x∗ * (U * X) := Matrix.mul_assoc _ _ _
        _ = x∗ * (x * U) := by rw [hx, hU]
        _ = x∗ * x * U := (Matrix.mul_assoc _ _ _).symm
        _ ≤ x∗ * U := Matrix.mul_mono_left kstar_mul_le_kstar _
    have hbase : U ≤ x∗ * U := by
      have h := Matrix.mul_mono_left (one_le_kstar (a := x)) U
      rwa [Matrix.one_mul] at h
    have hmain : U * X∗ ≤ x∗ * U := Matrix.mul_kstar_le_of_rect hbase hstep
    calc U * X∗ * V ≤ x∗ * U * V := Matrix.mul_mono_left hmain _
      _ = x∗ * (U * V) := Matrix.mul_assoc _ _ _
      _ = x∗ := by rw [hUV, Matrix.mul_one]
  · refine kstar_le_of_mul_le_right ?_ ?_
    · calc (1 : Matrix Unit Unit K) = U * V := hUV.symm
        _ = U * (1 : Matrix (Idx k) (Idx k) K) * V := by rw [Matrix.mul_one]
        _ ≤ U * X∗ * V := Matrix.mul_mono_left (Matrix.mul_mono_right one_le_kstar _) _
    · calc x * (U * X∗ * V) = U * (X * X∗) * V := by rw [hx, sandwich_mul τ k hX]
        _ ≤ U * X∗ * V := Matrix.mul_mono_left (Matrix.mul_mono_right mul_kstar_le_kstar _) _

/-! ### The recovery theorem -/

theorem sandwich_test (b : BTerm) (hb : ∀ i ∈ b.tvars, i < k) :
    rowVec τ k * testMat k K b * colVec τ k = scalarMat (⌜b.eval τ⌝ : K) := by
  have hrow : ∀ j : Idx k, (rowVec τ k * testMat k K b : Matrix Unit (Idx k) K) () j
      = if (atomOf k j).sat b then atomVal τ k j else 0 := by
    intro j
    rw [Matrix.mul_apply,
      Finset.sum_eq_single j (fun i _ hi ↦ by simp [rowVec, testMat, hi])
        (fun hi ↦ absurd (Finset.mem_univ _) hi)]
    by_cases hj : (atomOf k j).sat b <;> simp [rowVec, testMat, hj]
  ext u v
  rw [Matrix.mul_apply, scalarMat_apply]
  have hcol : ∀ j : Idx k,
      (rowVec τ k * testMat k K b : Matrix Unit (Idx k) K) u j * colVec τ k j v
        = if (atomOf k j).sat b then atomVal τ k j else 0 := by
    intro j
    obtain rfl : u = () := Subsingleton.elim u ()
    rw [hrow j]
    simp only [colVec]
    by_cases hj : (atomOf k j).sat b
    · rw [if_pos hj]
      exact atomVal_mul_self τ k j
    · rw [if_neg hj]
      exact zero_mul _
  rw [Finset.sum_congr rfl fun j _ ↦ hcol j]
  have hb' : (⌜b.eval τ⌝ : K)
      = lsup (fun α ↦ if α.sat b then (⌜atomT τ α⌝ : K) else 0) (allAtoms k) := by
    rw [BTerm.eval_eq_lsup τ k b hb, test_lsup']
    refine congrArg (fun g ↦ lsup g (allAtoms k)) (funext fun α ↦ ?_)
    by_cases hα : α.sat b
    · rw [if_pos hα, if_pos hα]
    · rw [if_neg hα, if_neg hα]
      exact test_bot
  rw [hb', ← sum_atomOf k (fun α ↦ if α.sat b then (⌜atomT τ α⌝ : K) else 0)]
  rfl

theorem sandwich_act (p : ℕ) :
    rowVec τ k * actMat τ ρ k p * colVec τ k = scalarMat (ρ p) := by
  have hrow : ∀ j : Idx k, (rowVec τ k * actMat τ ρ k p : Matrix Unit (Idx k) K) () j
      = ρ p * atomVal τ k j := by
    intro j
    rw [Matrix.mul_apply]
    have hterm : ∀ i : Idx k, rowVec τ k () i * actMat τ ρ k p i j
        = atomVal τ k i * (ρ p * atomVal τ k j) := by
      intro i
      simp only [rowVec, actMat]
      rw [← mul_assoc, ← mul_assoc, atomVal_mul_self, mul_assoc]
    rw [Finset.sum_congr rfl fun i _ ↦ hterm i, ← Finset.sum_mul, sum_atomVal, one_mul]
  ext u v
  rw [Matrix.mul_apply, scalarMat_apply]
  have hterm : ∀ j : Idx k,
      (rowVec τ k * actMat τ ρ k p : Matrix Unit (Idx k) K) u j * colVec τ k j v
        = ρ p * atomVal τ k j := by
    intro j
    obtain rfl : u = () := Subsingleton.elim u ()
    rw [hrow j]
    simp only [colVec]
    rw [mul_assoc, atomVal_mul_self]
  rw [Finset.sum_congr rfl fun j _ ↦ hterm j, ← Finset.mul_sum, sum_atomVal, mul_one]

theorem valMat_zero : valMat τ ρ k .zero = 0 := rfl

theorem valMat_one : valMat τ ρ k .one = 1 := rfl

theorem valMat_test (b : BTerm) : valMat τ ρ k (.test b) = testMat k K b := rfl

theorem valMat_act (p : ℕ) : valMat τ ρ k (.act p) = actMat τ ρ k p := rfl

theorem valMat_add (e f : KTerm) :
    valMat τ ρ k (e.add f) = valMat τ ρ k e + valMat τ ρ k f := rfl

theorem valMat_mul (e f : KTerm) :
    valMat τ ρ k (e.mul f) = valMat τ ρ k e * valMat τ ρ k f := rfl

theorem valMat_star (e : KTerm) : valMat τ ρ k e.star = (valMat τ ρ k e)∗ := rfl

/-- **The matrix interpretation computes the value of the term**, in any Kleene algebra with
tests: no completeness, star-continuity or finiteness assumption is used. -/
theorem sandwich_valMat : ∀ (e : KTerm), (∀ i ∈ e.tvars, i < k) →
    rowVec τ k * valMat τ ρ k e * colVec τ k = scalarMat (e.eval τ ρ)
  | .zero, _ => by
    rw [valMat_zero, Matrix.mul_zero, Matrix.zero_mul]
    exact (scalarMat_zero (K := K)).symm
  | .one, _ => by
    rw [valMat_one, Matrix.mul_one, row_mul_col τ k]
    exact (scalarMat_one (K := K)).symm
  | .test b, h => by rw [valMat_test]; exact sandwich_test τ k b h
  | .act p, _ => by rw [valMat_act]; exact sandwich_act τ ρ k p
  | .add e f, h => by
    have he := fun i hi ↦ h i (List.mem_append.2 (Or.inl hi))
    have hf := fun i hi ↦ h i (List.mem_append.2 (Or.inr hi))
    rw [valMat_add, Matrix.mul_add, Matrix.add_mul, sandwich_valMat e he,
      sandwich_valMat f hf, ← scalarMat_add]
    rfl
  | .mul e f, h => by
    have he := fun i hi ↦ h i (List.mem_append.2 (Or.inl hi))
    have hf := fun i hi ↦ h i (List.mem_append.2 (Or.inr hi))
    rw [valMat_mul, sandwich_mul τ k (good_valMat τ ρ k e), sandwich_valMat e he,
      sandwich_valMat f hf, ← scalarMat_mul]
    rfl
  | .star e, h => by
    rw [valMat_star, sandwich_kstar τ k (good_valMat τ ρ k e), sandwich_valMat e h,
      ← scalarMat_kstar]
    rfl

/-- The value of a KAT term, read off from its matrix interpretation. -/
theorem eval_eq_sandwich (e : KTerm) (he : ∀ i ∈ e.tvars, i < k) :
    e.eval τ ρ = (rowVec τ k * valMat τ ρ k e * colVec τ k : Matrix Unit Unit K) () () := by
  rw [sandwich_valMat τ ρ k e he, scalarMat_apply]

end KAT.Completeness
