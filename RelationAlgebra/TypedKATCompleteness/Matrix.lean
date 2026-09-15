import RelationAlgebra.TypedKAT
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Finite matrices of morphisms in a Kleene category

For a finite family of objects `o`, a matrix entry `(i,j)` is a morphism `o i ⟶ o j`.
Composition takes finite joins over intermediate objects. State elimination constructs
the matrix star using only the stars already present in the category. In particular, this
construction does not require complete hom lattices or star-continuity.

This is the finite additive completion used to reduce typed KAT identities to the untyped
completeness theorem. The elimination step is the usual Kleene/Floyd–Warshall step with
`R i k ≫ (R k k)∗ ≫ R k j` accounting for arbitrarily many visits to a pivot.
-/

open CategoryTheory
open scoped Computability

universe u v w

namespace KleeneCategory

variable {C : Type u} [Category.{v} C] [KleeneCategory C]

theorem finsetSup_comp {ι : Type*} {X Y Z : C} (s : Finset ι)
    (f : ι → (X ⟶ Y)) (g : Y ⟶ Z) : s.sup f ≫ g = s.sup (fun i ↦ f i ≫ g) :=
  Finset.comp_sup_eq_sup_comp (fun h ↦ h ≫ g) (fun _ _ ↦ sup_comp _ _ _) (bot_comp _)

theorem comp_finsetSup {ι : Type*} {X Y Z : C} (f : X ⟶ Y)
    (s : Finset ι) (g : ι → (Y ⟶ Z)) : f ≫ s.sup g = s.sup (fun i ↦ f ≫ g i) :=
  Finset.comp_sup_eq_sup_comp (fun h ↦ f ≫ h) (fun _ _ ↦ comp_sup _ _ _) (comp_bot _)

/-- A finite square matrix whose entries may belong to different hom-sets. -/
def HomMatrix {ι : Type w} (o : ι → C) := ∀ i j, o i ⟶ o j

namespace HomMatrix

variable {ι : Type w} {o : ι → C}

instance : CoeFun (HomMatrix o) (fun _ ↦ ∀ i j, o i ⟶ o j) := ⟨id⟩
instance : SemilatticeSup (HomMatrix o) := inferInstanceAs (SemilatticeSup (∀ i j, o i ⟶ o j))
instance : OrderBot (HomMatrix o) := inferInstanceAs (OrderBot (∀ i j, o i ⟶ o j))
instance : Add (HomMatrix o) := ⟨(· ⊔ ·)⟩
instance : Zero (HomMatrix o) := ⟨⊥⟩

omit [KleeneCategory C] in
@[ext] theorem ext {A B : HomMatrix o} (h : ∀ i j, A i j = B i j) : A = B :=
  funext fun i ↦ funext (h i)

@[simp] theorem add_apply (A B : HomMatrix o) (i j : ι) : (A + B) i j = A i j ⊔ B i j := rfl
@[simp] theorem zero_apply (i j : ι) : (0 : HomMatrix o) i j = ⊥ := rfl

section Finite

variable [Fintype ι] [DecidableEq ι]

/-- Place endomorphisms on the diagonal; transport the target along equality of indices. -/
def diagonal (d : ∀ i, o i ⟶ o i) : HomMatrix o :=
  fun i j ↦ if h : i = j then d i ≫ eqToHom (congrArg o h) else ⊥

omit [Fintype ι] in
@[simp] theorem diagonal_self (d : ∀ i, o i ⟶ o i) (i : ι) : diagonal d i i = d i := by
  simp [diagonal]

omit [Fintype ι] in
@[simp] theorem diagonal_ne (d : ∀ i, o i ⟶ o i) {i j : ι} (h : i ≠ j) :
    diagonal d i j = ⊥ := by simp [diagonal, h]

instance : One (HomMatrix o) := ⟨diagonal fun i ↦ 𝟙 (o i)⟩
instance : Mul (HomMatrix o) := ⟨fun A B i j ↦ Finset.univ.sup (fun k ↦ A i k ≫ B k j)⟩

omit [Fintype ι] in
@[simp] theorem one_self (i : ι) : (1 : HomMatrix o) i i = 𝟙 (o i) := diagonal_self _ _
omit [Fintype ι] in
@[simp] theorem one_ne {i j : ι} (h : i ≠ j) : (1 : HomMatrix o) i j = ⊥ := diagonal_ne _ h

omit [DecidableEq ι] in
theorem mul_apply (A B : HomMatrix o) (i j : ι) :
    (A * B) i j = Finset.univ.sup (fun k ↦ A i k ≫ B k j) := rfl

omit [DecidableEq ι] in
theorem le_mul (A B : HomMatrix o) (i k j : ι) : A i k ≫ B k j ≤ (A * B) i j :=
  Finset.le_sup (f := fun k ↦ A i k ≫ B k j) (Finset.mem_univ k)

omit [DecidableEq ι] in
theorem mul_le_iff {A B D : HomMatrix o} :
    A * B ≤ D ↔ ∀ i k j, A i k ≫ B k j ≤ D i j := by
  constructor
  · intro h i k j; exact (le_mul A B i k j).trans (h i j)
  · intro h i j; exact Finset.sup_le fun k _ ↦ h i k j

theorem diagonal_mul (d : ∀ i, o i ⟶ o i) (A : HomMatrix o) (i j : ι) :
    (diagonal d * A) i j = d i ≫ A i j := by
  apply le_antisymm
  · apply Finset.sup_le
    intro k _
    by_cases h : i = k
    · subst k; simp
    · simp [h]
  · simpa using le_mul (diagonal d) A i i j

theorem mul_diagonal (A : HomMatrix o) (d : ∀ i, o i ⟶ o i) (i j : ι) :
    (A * diagonal d) i j = A i j ≫ d j := by
  apply le_antisymm
  · apply Finset.sup_le
    intro k _
    by_cases h : k = j
    · subst k; simp
    · simp [h]
  · simpa using le_mul A (diagonal d) i j j

instance : Monoid (HomMatrix o) where
  one_mul A := ext fun i j ↦ by
    change (diagonal (fun i ↦ 𝟙 (o i)) * A) i j = A i j
    rw [diagonal_mul, Category.id_comp]
  mul_one A := ext fun i j ↦ by
    change (A * diagonal (fun i ↦ 𝟙 (o i))) i j = A i j
    rw [mul_diagonal, Category.comp_id]
  mul_assoc A B D := ext fun i j ↦ by
    simp only [mul_apply, finsetSup_comp, comp_finsetSup, Category.assoc]
    exact Finset.sup_comm _ _ _

instance : IdemSemiring (HomMatrix o) where
  add_assoc := sup_assoc
  zero_add := bot_sup_eq
  add_zero := sup_bot_eq
  add_comm := sup_comm
  nsmul := nsmulRec
  left_distrib A B D := ext fun i j ↦ by
    simp only [mul_apply, add_apply, comp_sup]
    exact Finset.sup_sup
  right_distrib A B D := ext fun i j ↦ by
    simp only [mul_apply, add_apply, sup_comp]
    exact Finset.sup_sup
  zero_mul A := ext fun i j ↦ by simp [mul_apply]
  mul_zero A := ext fun i j ↦ by simp [mul_apply]
  add_eq_sup _ _ := rfl

end Finite

/-! ### State elimination -/

/-- Eliminate a pivot, retaining the old paths and adding paths through the pivot. -/
def pivot (R : HomMatrix o) (k : ι) : HomMatrix o :=
  fun i j ↦ R i j ⊔ R i k ≫ (R k k)∗ ≫ R k j

theorem le_pivot (R : HomMatrix o) (k : ι) : R ≤ pivot R k := fun _ _ ↦ le_sup_left

/-- All paths through a given intermediate object are absorbed by the matrix. -/
def TransAt (R : HomMatrix o) (k : ι) : Prop := ∀ i j, R i k ≫ R k j ≤ R i j

theorem pivot_trans (R : HomMatrix o) (k : ι) : TransAt (pivot R k) k := by
  intro i j
  have hi : pivot R k i k ≤ R i k ≫ (R k k)∗ := by
    apply sup_le (le_comp_kstar _ _)
    exact comp_le_comp_right (kstar_comp_le_kstar _) _
  have hj : pivot R k k j ≤ (R k k)∗ ≫ R k j := by
    apply sup_le (le_kstar_comp _ _)
    rw [← Category.assoc]
    exact comp_le_comp_left (comp_kstar_le_kstar _) _
  calc pivot R k i k ≫ pivot R k k j ≤ (R i k ≫ (R k k)∗) ≫ ((R k k)∗ ≫ R k j) :=
        comp_le_comp hi hj
    _ = R i k ≫ (R k k)∗ ≫ R k j := by
        simp only [Category.assoc, ← Category.assoc (R k k)∗ (R k k)∗, kstar_comp_kstar]
    _ ≤ pivot R k i j := le_sup_right

theorem pivot_preserves {R : HomMatrix o} {l : ι} (h : TransAt R l) (k : ι) :
    TransAt (pivot R k) l := by
  intro i j
  simp only [pivot, sup_comp, comp_sup]
  refine sup_le (sup_le ((h i j).trans le_sup_left) ?_) (sup_le ?_ ?_)
  · calc (R i k ≫ (R k k)∗ ≫ R k l) ≫ R l j =
          R i k ≫ (R k k)∗ ≫ (R k l ≫ R l j) := by simp only [Category.assoc]
      _ ≤ R i k ≫ (R k k)∗ ≫ R k j := comp_le_comp_right (comp_le_comp_right (h k j) _) _
      _ ≤ _ := le_sup_right
  · calc R i l ≫ (R l k ≫ (R k k)∗ ≫ R k j) =
          (R i l ≫ R l k) ≫ (R k k)∗ ≫ R k j := by simp only [Category.assoc]
      _ ≤ R i k ≫ (R k k)∗ ≫ R k j := comp_le_comp_left (h i k) _
      _ ≤ _ := le_sup_right
  · calc (R i k ≫ (R k k)∗ ≫ R k l) ≫ (R l k ≫ (R k k)∗ ≫ R k j) =
          R i k ≫ ((R k k)∗ ≫ (R k l ≫ R l k) ≫ (R k k)∗) ≫ R k j := by
            simp only [Category.assoc]
      _ ≤ R i k ≫ ((R k k)∗ ≫ R k k ≫ (R k k)∗) ≫ R k j := by
        gcongr
        exact h k k
      _ ≤ R i k ≫ ((R k k)∗ ≫ (R k k)∗) ≫ R k j := by
        gcongr
        exact comp_kstar_le_kstar _
      _ = R i k ≫ (R k k)∗ ≫ R k j := by rw [kstar_comp_kstar]
      _ ≤ _ := le_sup_right

/-- Eliminate every pivot in a list. Repetition is harmless for the proved closure laws. -/
def close (R : HomMatrix o) : List ι → HomMatrix o
  | [] => R
  | k :: ks => close (pivot R k) ks

theorem le_close (R : HomMatrix o) (ks : List ι) : R ≤ close R ks := by
  induction ks generalizing R with
  | nil => exact le_rfl
  | cons k ks ih => exact (le_pivot R k).trans (ih _)

theorem close_preserves {R : HomMatrix o} {k : ι} (h : TransAt R k) (ks : List ι) :
    TransAt (close R ks) k := by
  induction ks generalizing R with
  | nil => exact h
  | cons l ls ih => exact ih (pivot_preserves h l)

theorem close_trans (R : HomMatrix o) {ks : List ι} {k : ι} (hk : k ∈ ks) :
    TransAt (close R ks) k := by
  induction ks generalizing R with
  | nil => simp at hk
  | cons l ls ih =>
    rcases List.mem_cons.1 hk with rfl | hk
    · exact close_preserves (pivot_trans R k) ls
    · exact ih _ hk

/-- Elimination preserves every left invariant, with an arbitrary target object. -/
theorem pivot_left {R : HomMatrix o} {Z : C} (x : ∀ i, o i ⟶ Z)
    (h : ∀ i j, R i j ≫ x j ≤ x i) (k : ι) : ∀ i j, pivot R k i j ≫ x j ≤ x i := by
  intro i j
  rw [pivot, sup_comp]
  refine sup_le (h i j) ?_
  calc (R i k ≫ (R k k)∗ ≫ R k j) ≫ x j = R i k ≫ (R k k)∗ ≫ (R k j ≫ x j) := by
        simp only [Category.assoc]
    _ ≤ R i k ≫ (R k k)∗ ≫ x k := by gcongr; exact h k j
    _ ≤ R i k ≫ x k := comp_le_comp_right (kstar_comp_le_self _ _ (h k k)) _
    _ ≤ x i := h i k

/-- Elimination preserves every right invariant, with an arbitrary source object. -/
theorem pivot_right {R : HomMatrix o} {Z : C} (x : ∀ i, Z ⟶ o i)
    (h : ∀ i j, x i ≫ R i j ≤ x j) (k : ι) : ∀ i j, x i ≫ pivot R k i j ≤ x j := by
  intro i j
  rw [pivot, comp_sup]
  refine sup_le (h i j) ?_
  calc x i ≫ (R i k ≫ (R k k)∗ ≫ R k j) = ((x i ≫ R i k) ≫ (R k k)∗) ≫ R k j := by
        simp only [Category.assoc]
    _ ≤ (x k ≫ (R k k)∗) ≫ R k j := by gcongr; exact h i k
    _ ≤ x k ≫ R k j := comp_le_comp_left (comp_kstar_le_self _ _ (h k k)) _
    _ ≤ x j := h k j

theorem close_left {R : HomMatrix o} {Z : C} (x : ∀ i, o i ⟶ Z)
    (h : ∀ i j, R i j ≫ x j ≤ x i) (ks : List ι) : ∀ i j, close R ks i j ≫ x j ≤ x i := by
  induction ks generalizing R with
  | nil => exact h
  | cons k ks ih => exact ih (pivot_left x h k)

theorem close_right {R : HomMatrix o} {Z : C} (x : ∀ i, Z ⟶ o i)
    (h : ∀ i j, x i ≫ R i j ≤ x j) (ks : List ι) : ∀ i j, x i ≫ close R ks i j ≤ x j := by
  induction ks generalizing R with
  | nil => exact h
  | cons k ks ih => exact ih (pivot_right x h k)

section Finite

variable [Fintype ι] [DecidableEq ι]

noncomputable instance : KStar (HomMatrix o) := ⟨fun A ↦ close (1 + A) Finset.univ.toList⟩

theorem le_kstar (A : HomMatrix o) : A ≤ A∗ := le_add_self.trans (le_close _ _)
theorem one_le_kstar (A : HomMatrix o) : 1 ≤ A∗ := le_self_add.trans (le_close _ _)

theorem kstar_trans (A : HomMatrix o) (k : ι) : TransAt A∗ k :=
  close_trans _ (by simp)

theorem kstar_left (A : HomMatrix o) {Z : C} (x : ∀ i, o i ⟶ Z)
    (h : ∀ i j, A i j ≫ x j ≤ x i) : ∀ i j, A∗ i j ≫ x j ≤ x i := by
  apply close_left x
  intro i j
  rw [add_apply, sup_comp]
  refine sup_le ?_ (h i j)
  by_cases hij : i = j
  · subst j; simp
  · simp [hij]

theorem kstar_right (A : HomMatrix o) {Z : C} (x : ∀ i, Z ⟶ o i)
    (h : ∀ i j, x i ≫ A i j ≤ x j) : ∀ i j, x i ≫ A∗ i j ≤ x j := by
  apply close_right x
  intro i j
  rw [add_apply, comp_sup]
  refine sup_le ?_ (h i j)
  by_cases hij : i = j
  · subst j; simp
  · simp [hij]

noncomputable instance : KleeneAlgebra (HomMatrix o) where
  one_le_kstar := one_le_kstar
  mul_kstar_le_kstar A := mul_le_iff.2 fun i k j ↦
    (comp_le_comp_left (le_kstar A i k) _).trans (kstar_trans A k i j)
  kstar_mul_le_kstar A := mul_le_iff.2 fun i k j ↦
    (comp_le_comp_right (le_kstar A k j) _).trans (kstar_trans A k i j)
  kstar_mul_le_self A B h := mul_le_iff.2 fun i k j ↦
    kstar_left A (fun l ↦ B l j) (fun l m ↦ mul_le_iff.1 h l m j) i k
  mul_kstar_le_self A B h := mul_le_iff.2 fun i k j ↦
    kstar_right A (fun l ↦ B i l) (fun l m ↦ mul_le_iff.1 h i l m) k j

end Finite
end HomMatrix
end KleeneCategory
