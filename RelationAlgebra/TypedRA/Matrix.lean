import RelationAlgebra.TypedRA.Syntax
import RelationAlgebra.TypedKATCompleteness.Finite

/-!
# Matrices with converse and recovery of typed values

Transpose and entrywise converse make the finite heterogeneous matrix algebra a
`StarRing`. Recovery tracks both the source row and the target column: converse swaps
these invariants. Stars retain identity entries at every object, including objects other
than the loop's endpoint. No completeness or continuity of hom lattices is required.
-/

open CategoryTheory KleeneCategory KleeneCategoryWithConverse
open scoped Computability

universe u v w

namespace KleeneCategory.HomMatrix

variable {C : Type u} [Category.{v} C] [KleeneCategory C]
  [KleeneCategoryWithConverse C] {ι : Type w} {o : ι → C}

instance : Star (HomMatrix o) := ⟨fun A i j ↦ converse (A j i)⟩

@[simp] theorem star_apply (A : HomMatrix o) (i j : ι) :
    Star.star A i j = converse (A j i) := rfl

instance [Fintype ι] [DecidableEq ι] : StarRing (HomMatrix o) where
  star_involutive A := ext fun i j ↦ converse_converse (A i j)
  star_add A B := ext fun i j ↦ converse_sup (A j i) (B j i)
  star_mul A B := ext fun i j ↦ by
    change converse (Finset.univ.sup (fun k ↦ A j k ≫ B k i)) = _
    rw [Finset.comp_sup_eq_sup_comp converse converse_sup converse_bot]
    simp only [Function.comp_def, converse_comp, mul_apply, star_apply]

variable [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
@[simp] theorem star_single (x y : ι) (a : o x ⟶ o y) :
    Star.star (single x y a) = single y x (converse a) := by
  ext i j
  by_cases hi : i = y <;> by_cases hj : j = x
  · subst i; subst j; simp
  · subst i; simp [single, row, hj, Ne.symm hj]
  · subst j; simp [single, row, hi, Ne.symm hi]
  · simp [single, hi, hj]

omit [KleeneCategoryWithConverse C] [Fintype ι] in
/-- Add two rows supported at the same target. -/
theorem row_sup {X : C} (y j : ι) (a b : X ⟶ o y) :
    row y a j ⊔ row y b j = row y (a ⊔ b) j := by
  by_cases h : y = j
  · subst j; simp
  · simp [h]

end KleeneCategory.HomMatrix

namespace TypedRA.Term

open KleeneCategory.HomMatrix

variable {I : Type u} [Fintype I] [DecidableEq I] {src tgt : ℕ → I}
  {C : Type v} [Category.{w} C] [KleeneCategory C] [KleeneCategoryWithConverse C]
  (o : I → C) (ρ : ∀ a, o (src a) ⟶ o (tgt a))

/-- Evaluate erasure in the algebra of heterogeneous matrices. -/
noncomputable def evalMatrix {X Y : I} (e : Term src tgt X Y) : HomMatrix o :=
  e.erase.eval (fun a ↦ single (src a) (tgt a) (ρ a))

/-- The declared source row and the converse of the declared target column recover
exactly the typed value and its converse. -/
theorem eval_rows {X Y : I} (e : Term src tgt X Y) :
    (∀ j, evalMatrix o ρ e X j = row Y (e.eval o ρ) j) ∧
    (∀ i, Star.star (evalMatrix o ρ e) Y i = row X (converse (e.eval o ρ)) i) := by
  induction e with
  | zero => constructor <;> intro j <;> simp [evalMatrix, erase, eval]
  | @one X =>
    constructor
    · intro j; rfl
    · intro j
      change Star.star (1 : HomMatrix o) X j = row X (converse (𝟙 (o X))) j
      rw [star_one, converse_id]
      rfl
  | act a =>
    constructor
    · intro j; exact single_row _ _ _ _
    · intro j
      change Star.star (single (src a) (tgt a) (ρ a)) (tgt a) j = _
      rw [star_single, single_row]
      rfl
  | @add X Y e f he hf =>
    constructor
    · intro j
      change evalMatrix o ρ e X j ⊔ evalMatrix o ρ f X j = _
      rw [he.1, hf.1, row_sup]
      rfl
    · intro j
      change Star.star (evalMatrix o ρ e + evalMatrix o ρ f) Y j = _
      rw [star_add, add_apply, he.2, hf.2, row_sup]
      simp only [eval, converse_sup]
  | @comp X Y Z e f he hf =>
    constructor
    · intro j
      change (evalMatrix o ρ e * evalMatrix o ρ f) X j = _
      rw [mul_of_row he.1, hf.1, comp_row]
      rfl
    · intro j
      change Star.star (evalMatrix o ρ e * evalMatrix o ρ f) Z j = _
      rw [star_mul, mul_of_row hf.2, he.2, comp_row]
      simp only [eval, converse_comp]
  | @star X e he =>
    constructor
    · exact row_kstar he.1
    · intro j
      change Star.star (evalMatrix o ρ e)∗ X j = _
      rw [KleeneAlgebra.star_kstar, row_kstar he.2]
      simp only [eval, converse_kstar]
  | @conv X Y e he =>
    constructor
    · exact he.2
    · intro j
      change Star.star (Star.star (evalMatrix o ρ e)) X j = _
      rw [star_star, he.1]
      simp only [eval, converse_converse]

@[simp] theorem eval_entry {X Y : I} (e : Term src tgt X Y) :
    evalMatrix o ρ e X Y = e.eval o ρ := by
  simpa using (eval_rows o ρ e).1 Y

end TypedRA.Term
