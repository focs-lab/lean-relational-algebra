import RelationAlgebra.Decide.KATSound
import RelationAlgebra.KATCompleteness.RegLang
import RelationAlgebra.KATCompleteness.MapStar

/-!
# Atom-indexed matrices for Kleene algebra with tests

Fix `k` test variables.  The atoms of the free Boolean algebra on them are enumerated by
`KAT.Completeness.atomOf`, and matrices indexed by atoms carry the whole guarded-string
structure: a guarded string from `α` to `β` becomes an entry of the matrix at `(α, β)`, and the
fusion product of guarded strings becomes matrix multiplication, with the single-atom strings
supplying the *identity* matrix rather than a proper sub-identity.

`KAT.Completeness.evalMat` interprets a KAT term as such a matrix, given an interpretation of
the primitive actions.  Because the interpretation is built only from `0`, `1`, `+`, `*` and the
matrix Kleene star, it commutes with any Kleene algebra homomorphism
(`KAT.Completeness.evalMat_map`), which is what lets an identity established over regular
languages be transported into an arbitrary Kleene algebra.

## References

* Damien Pous, `relation-algebra`, `theories/kat_completeness.v`, after D. Kozen and F. Smith,
  *Kleene algebra with tests: completeness and decidability*, CSL'96.
-/

open scoped Computability KAT

namespace KAT.Completeness

/-! ### Enumerating the atoms -/

/-- The index type of the atoms on `k` test variables. -/
abbrev Idx (k : ℕ) : Type := Fin (allAtoms k).length

/-- The atom with a given index. -/
def atomOf (k : ℕ) (i : Idx k) : Atom := (allAtoms k).get i

theorem atomOf_mem (k : ℕ) (i : Idx k) : atomOf k i ∈ allAtoms k := List.get_mem _ _

theorem length_atomOf (k : ℕ) (i : Idx k) : (atomOf k i).length = k :=
  mem_allAtoms.1 (atomOf_mem k i)

theorem nodup_allAtoms (k : ℕ) : (allAtoms k).Nodup := by
  induction k with
  | zero => simp [allAtoms]
  | succ k ih =>
    rw [allAtoms]
    refine List.Nodup.append (ih.map ?_) (ih.map ?_) ?_
    · intro a b h
      exact (List.cons_eq_cons.1 h).2
    · intro a b h
      exact (List.cons_eq_cons.1 h).2
    · intro x hx hx'
      obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
      obtain ⟨b, -, hb⟩ := List.mem_map.1 hx'
      exact absurd (List.cons_eq_cons.1 hb).1 (by simp)

theorem atomOf_injective (k : ℕ) : Function.Injective (atomOf k) := by
  intro i j h
  exact (List.nodup_iff_injective_get.1 (nodup_allAtoms k)) h

theorem exists_atomOf {k : ℕ} {α : Atom} (h : α ∈ allAtoms k) : ∃ i, atomOf k i = α := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.1 h
  exact ⟨i, hi⟩

/-! ### Sums over the atoms -/

section Sum
variable {L : Type*} [IdemSemiring L]

theorem bot_eq_zero' : (⊥ : L) = 0 := le_antisymm bot_le zero_le

theorem sum_get_eq_lsup (g : Atom → L) :
    ∀ l : List Atom, (∑ i : Fin l.length, g (l.get i)) = lsup g l := by
  intro l
  induction l with
  | nil => simpa [lsup] using bot_eq_zero'.symm
  | cons a l ih =>
    change (∑ i : Fin (l.length + 1), g ((a :: l).get i)) = lsup g (a :: l)
    rw [Fin.sum_univ_succ, lsup_cons, ← add_eq_sup]
    exact congrArg (g a + ·) ih

theorem sum_atomOf (k : ℕ) (g : Atom → L) :
    (∑ i : Idx k, g (atomOf k i)) = lsup g (allAtoms k) := sum_get_eq_lsup g _

end Sum

/-! ### Atoms as elements of a Kleene algebra with tests -/

section Atoms

variable {T K : Type*} [BooleanAlgebra T] [KleeneAlgebra K] [KAT T K] (τ : ℕ → T) (k : ℕ)

/-- Tests commute with finite joins, in any Kleene algebra with tests. -/
theorem test_lsup' {ι : Type*} (f : ι → T) (l : List ι) :
    (⌜lsup f l⌝ : K) = lsup (fun x ↦ ⌜f x⌝) l := by
  induction l with
  | nil =>
    rw [lsup, lsup, test_bot]
    exact (le_antisymm bot_le zero_le).symm
  | cons x l ih => rw [lsup_cons, lsup_cons, test_sup, ih, add_eq_sup]

/-- The element of `K` corresponding to the atom of index `i`. -/
def atomVal (i : Idx k) : K := ⌜atomT τ (atomOf k i)⌝

theorem sum_atomVal : (∑ i : Idx k, atomVal (K := K) τ k i) = 1 := by
  change (∑ i : Idx k, (⌜atomT τ (atomOf k i)⌝ : K)) = 1
  rw [sum_atomOf k (fun α ↦ (⌜atomT τ α⌝ : K)), ← test_lsup', lsup_atomT_eq_top, test_top]

theorem atomVal_mul_self (i : Idx k) :
    atomVal (K := K) τ k i * atomVal τ k i = atomVal τ k i :=
  test_mul_self _

theorem atomVal_mul_of_ne {i j : Idx k} (h : i ≠ j) :
    atomVal (K := K) τ k i * atomVal τ k j = 0 := by
  change (⌜atomT τ (atomOf k i)⌝ : K) * ⌜atomT τ (atomOf k j)⌝ = 0
  rw [← test_inf, atomT, atomT,
    atomAux_inf_atomAux_eq_bot τ _ _ 0 (fun hc ↦ h (atomOf_injective k hc))
      ((length_atomOf k i).trans (length_atomOf k j).symm), test_bot]

theorem atomVal_mul (i j : Idx k) :
    atomVal (K := K) τ k i * atomVal τ k j = if i = j then atomVal τ k i else 0 := by
  split_ifs with h
  · subst h
    exact atomVal_mul_self τ k i
  · exact atomVal_mul_of_ne τ k h

theorem atomVal_le_one (i : Idx k) : atomVal (K := K) τ k i ≤ 1 := test_le_one

end Atoms

/-! ### The matrix interpretation of a KAT term -/

/-- The zero-one diagonal matrix of the atoms satisfying a Boolean term. -/
def testMat (k : ℕ) (K : Type*) [KleeneAlgebra K] (b : BTerm) : Matrix (Idx k) (Idx k) K :=
  fun i j => if i = j ∧ (atomOf k i).sat b then 1 else 0

/-- The matrix interpretation of a KAT term, given an interpretation `P` of the actions. -/
noncomputable def evalMat {k : ℕ} {K : Type*} [KleeneAlgebra K]
    (P : ℕ → Matrix (Idx k) (Idx k) K) :
    KTerm → Matrix (Idx k) (Idx k) K
  | .zero => 0
  | .one => 1
  | .test b => testMat k K b
  | .act p => P p
  | .add e f => evalMat P e + evalMat P f
  | .mul e f => evalMat P e * evalMat P f
  | .star e => (evalMat P e)∗

@[simp] theorem evalMat_zero {k : ℕ} {K : Type*} [KleeneAlgebra K]
    (P : ℕ → Matrix (Idx k) (Idx k) K) : evalMat P .zero = 0 := rfl
@[simp] theorem evalMat_one {k : ℕ} {K : Type*} [KleeneAlgebra K]
    (P : ℕ → Matrix (Idx k) (Idx k) K) : evalMat P .one = 1 := rfl
@[simp] theorem evalMat_test {k : ℕ} {K : Type*} [KleeneAlgebra K]
    (P : ℕ → Matrix (Idx k) (Idx k) K) (b : BTerm) : evalMat P (.test b) = testMat k K b := rfl
@[simp] theorem evalMat_act {k : ℕ} {K : Type*} [KleeneAlgebra K]
    (P : ℕ → Matrix (Idx k) (Idx k) K) (p : ℕ) : evalMat P (.act p) = P p := rfl
@[simp] theorem evalMat_add {k : ℕ} {K : Type*} [KleeneAlgebra K]
    (P : ℕ → Matrix (Idx k) (Idx k) K) (e f : KTerm) :
    evalMat P (.add e f) = evalMat P e + evalMat P f := rfl
@[simp] theorem evalMat_mul {k : ℕ} {K : Type*} [KleeneAlgebra K]
    (P : ℕ → Matrix (Idx k) (Idx k) K) (e f : KTerm) :
    evalMat P (.mul e f) = evalMat P e * evalMat P f := rfl
@[simp] theorem evalMat_star {k : ℕ} {K : Type*} [KleeneAlgebra K]
    (P : ℕ → Matrix (Idx k) (Idx k) K) (e : KTerm) :
    evalMat P (.star e) = (evalMat P e)∗ := rfl

/-- The matrix interpretation is built from `0`, `1`, `+`, `*` and the matrix star only, so it
commutes with every Kleene algebra homomorphism. -/
theorem evalMat_map {k : ℕ} {K₁ K₂ : Type*} [KleeneAlgebra K₁] [KleeneAlgebra K₂]
    {φ : K₁ → K₂} (h : Matrix.IsKAHom φ) (P : ℕ → Matrix (Idx k) (Idx k) K₁) (e : KTerm) :
    (evalMat P e).map φ = evalMat (fun p ↦ (P p).map φ) e := by
  induction e with
  | zero => simpa using h.matrix_map_zero
  | one => simpa using h.matrix_map_one
  | test b =>
    simp only [evalMat_test]
    ext i j
    simp only [Matrix.map_apply, testMat]
    split_ifs
    · exact h.map_one
    · exact h.map_zero
  | act p => rfl
  | add e f ihe ihf => simp only [evalMat_add, h.matrix_map_add, ihe, ihf]
  | mul e f ihe ihf => simp only [evalMat_mul, h.matrix_map_mul, ihe, ihf]
  | star e ih => simp only [evalMat_star, Matrix.map_kstar h, ih]

end KAT.Completeness
