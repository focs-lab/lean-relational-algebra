import RelationAlgebra.TypedKATCompleteness.Matrix
import RelationAlgebra.TypedKAT.GuardedString
import RelationAlgebra.KATCompleteness.Main

/-!
# Typed completeness for a finite set of syntactic objects

Interpret an action as a matrix with a single nonzero entry, and a test variable as the
diagonal of its values at all objects. The erased expression can then be interpreted using
ordinary KAT evaluation. Its row at the declared source has exactly one possible nonzero
entry, at the declared target, and that entry is its typed value (`eval_row`).

Stars of loops may have identity entries at other objects. The proof retains those entries:
only the row at the loop's source is constrained. This is why the construction respects the
global matrix identity without identifying it with a single object's identity.

The untyped completeness theorem now proves the typed theorem for finite object alphabets.
No finiteness or continuity is required of the semantic category or its test algebras.
-/

open CategoryTheory KleeneCategory
open scoped Computability

universe u v w z

namespace KleeneCategory.HomMatrix

variable {C : Type u} [Category.{v} C] [KleeneCategory C]
  {ι : Type w} [Fintype ι] [DecidableEq ι] {o : ι → C}

/-- A row supported at one target index. -/
def row {X : C} (y : ι) (a : X ⟶ o y) : ∀ j, X ⟶ o j :=
  fun j ↦ if h : y = j then a ≫ eqToHom (congrArg o h) else ⊥

omit [Fintype ι] in
@[simp] theorem row_self {X : C} (y : ι) (a : X ⟶ o y) : row y a y = a := by simp [row]

omit [Fintype ι] in
@[simp] theorem row_ne {X : C} (y : ι) (a : X ⟶ o y) {j : ι} (h : y ≠ j) :
    row y a j = ⊥ := by simp [row, h]

omit [Fintype ι] in
@[simp] theorem row_bot {X : C} (y j : ι) : row y (⊥ : X ⟶ o y) j = ⊥ := by
  by_cases h : y = j <;> simp [row, h]

omit [Fintype ι] in
theorem comp_row {X Y : C} (a : X ⟶ Y) (z : ι) (b : Y ⟶ o z) (j : ι) :
    a ≫ row z b j = row z (a ≫ b) j := by
  by_cases h : z = j
  · subst j; simp
  · simp [h]

/-- Place a morphism in a single matrix entry. -/
def single (x y : ι) (a : o x ⟶ o y) : HomMatrix o :=
  fun i j ↦ if h : i = x then eqToHom (congrArg o h) ≫ row y a j else ⊥

omit [Fintype ι] in
@[simp] theorem single_row (x y : ι) (a : o x ⟶ o y) (j : ι) : single x y a x j = row y a j := by
  simp [single]

theorem mul_of_row {A : HomMatrix o} {x y : ι} {a : o x ⟶ o y}
    (hA : ∀ j, A x j = row y a j) (B : HomMatrix o) (j : ι) :
    (A * B) x j = a ≫ B y j := by
  apply le_antisymm
  · apply Finset.sup_le
    intro k _
    rw [hA]
    by_cases h : y = k
    · subst k; simp
    · simp [h]
  · simpa only [hA, row_self] using le_mul A B x y j

theorem row_kstar {A : HomMatrix o} {x : ι} {a : o x ⟶ o x}
    (hA : ∀ j, A x j = row x a j) : ∀ j, A∗ x j = row x a∗ j := by
  have hv : ∀ i j, row x a∗ i ≫ A i j ≤ row x a∗ j := by
    intro i j
    by_cases hxi : x = i
    · subst i
      rw [row_self, hA]
      by_cases hxj : x = j
      · subst j
        simpa using KleeneCategory.kstar_comp_le_kstar a
      · simp [hxj]
    · simp [hxi]
  have hu (j : ι) : A∗ x j ≤ row x a∗ j := by
    calc A∗ x j = 𝟙 (o x) ≫ A∗ x j := (Category.id_comp _).symm
      _ ≤ a∗ ≫ A∗ x j := comp_le_comp_left (id_le_kstar a) _
      _ ≤ row x a∗ j := by simpa using kstar_right A (row x a∗) hv x j
  intro j
  apply le_antisymm (hu j)
  by_cases hxj : x = j
  · subst j
    rw [row_self]
    apply kstar_le_of_comp_le_right
    · simpa using one_le_kstar A x x
    · have ha : A x x = a := by simpa using hA x
      rw [← ha]
      exact (comp_le_comp_left (le_kstar A x x) _).trans (kstar_trans A x x x)
  · simp [hxj]

variable {T : C → Type z} [∀ X, BooleanAlgebra (T X)] [TypedKAT C T]

/-- Tests of the matrix algebra are families of tests, one at each object. -/
noncomputable instance : KAT (∀ i, T (o i)) (HomMatrix o) where
  test b := diagonal (fun i ↦ TypedKAT.test (b i))
  test_bot := ext fun i j ↦ by
    by_cases h : i = j
    · subst j; simp
    · simp [h]
  test_top := ext fun i j ↦ by
    by_cases h : i = j
    · subst j; simp
    · simp [h]
  test_sup b c := ext fun i j ↦ by
    by_cases h : i = j
    · subst j; simp
    · simp [h]
  test_inf b c := ext fun i j ↦ by
    rw [diagonal_mul]
    by_cases h : i = j
    · subst j; simp
    · simp [h]

end KleeneCategory.HomMatrix

namespace TypedKAT.Completeness

variable {I : Type u} [Fintype I] [DecidableEq I] {src tgt : ℕ → I}
  {C : Type v} [Category.{w} C] [KleeneCategory C]
  {T : C → Type z} [∀ X, BooleanAlgebra (T X)] [TypedKAT C T]
  (o : I → C) (τ : ∀ X, ℕ → T (o X)) (ρ : ∀ a, o (src a) ⟶ o (tgt a))

open KleeneCategory.HomMatrix

omit [Fintype I] [DecidableEq I] [Category C] [KleeneCategory C] [TypedKAT C T] in
theorem eval_testFamily (b : KAT.BTerm) (i : I) :
    (b.eval (fun a j ↦ τ j a)) i = b.eval (τ i) := by
  induction b <;> simp_all [KAT.BTerm.eval]

/-- Interpret an erased expression in the algebra of heterogeneous matrices. -/
noncomputable def evalMatrix {X Y : I} (e : Term src tgt X Y) : HomMatrix o :=
  e.erase.eval (fun a i ↦ τ i a) (fun a ↦ single (src a) (tgt a) (ρ a))

/-- The source row of a typed expression contains its value only at the target. -/
theorem eval_row {X Y : I} (e : Term src tgt X Y) :
    ∀ j, evalMatrix o τ ρ e X j = row Y (e.eval o τ ρ) j := by
  induction e with
  | zero => intro j; simp [evalMatrix, Term.erase, KAT.KTerm.eval, Term.eval]
  | one =>
    intro j
    change (1 : HomMatrix o) _ j = _
    rfl
  | @test X b =>
    intro j
    change diagonal (fun i ↦ TypedKAT.test ((b.eval (fun a i ↦ τ i a)) i)) X j =
      row X (TypedKAT.test (b.eval (τ X))) j
    by_cases h : X = j
    · subst j
      simp [eval_testFamily]
    · simp [h]
  | act a => intro j; exact single_row _ _ _ _
  | @add X Y e f he hf =>
    intro j
    change evalMatrix o τ ρ e X j ⊔ evalMatrix o τ ρ f X j = _
    rw [he, hf]
    by_cases h : Y = j
    · subst j; simp [Term.eval]
    · simp [Term.eval, h]
  | @comp X Y Z e f he hf =>
    intro j
    change (evalMatrix o τ ρ e * evalMatrix o τ ρ f) X j = _
    rw [mul_of_row he, hf, comp_row]
    rfl
  | star e he => exact row_kstar he

@[simp] theorem eval_entry {X Y : I} (e : Term src tgt X Y) :
    evalMatrix o τ ρ e X Y = e.eval o τ ρ := by
  simpa using eval_row o τ ρ e Y

omit [Fintype I] [DecidableEq I] in
/-- Typed completeness for finite syntactic object alphabets. The semantic category and
all its hom-sets and test algebras remain arbitrary. -/
theorem eval_eq_of_lang_eq_finite [Finite I] {X Y : I} {e f : Term src tgt X Y} (k : ℕ)
    (he : ∀ a ∈ e.tvars, a < k) (hf : ∀ a ∈ f.tvars, a < k)
    (h : e.lang k = f.lang k) : e.eval o τ ρ = f.eval o τ ρ := by
  classical
  letI := Fintype.ofFinite I
  have hm : evalMatrix o τ ρ e = evalMatrix o τ ρ f :=
    KAT.Completeness.KTerm.eval_eq_of_gs_eq (fun a i ↦ τ i a)
      (fun a ↦ single (src a) (tgt a) (ρ a)) k he hf ((Term.lang_eq_iff e f k).1 h)
  simpa using congrArg (fun M : HomMatrix o ↦ M X Y) hm

end TypedKAT.Completeness
