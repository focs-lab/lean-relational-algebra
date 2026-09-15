import RelationAlgebra.Models.Matrix
import Mathlib.Logic.Relation

/-!
# Zero-one matrices over a Kleene algebra

This file is the Lean counterpart of upstream `theories/bmx.v` (Boolean matrices and the
characterisation of reflexive-transitive closure) in Damien Pous' `relation-algebra` library.

A *labelled zero-one matrix* `ofRelLab r c` sends the pairs related by `r` to `c` and all
others to `0`; `ofRel K r = ofRelLab r 1` is the plain zero-one matrix of `r`.  Together these
let one describe a finite automaton over a Kleene algebra by purely relational data:

* `ofRel_one`, `ofRel_false`, `ofRel_sup`, `ofRel_comp` : the operations correspond;
* `ofRel_mul_ofRelLab`, `ofRelLab_mul_ofRel` : composing with a zero-one matrix composes the
  underlying relations, leaving the label untouched;
* `ofRel_kstar : (ofRel K r)∗ = ofRel K (Relation.ReflTransGen r)` : the Kleene star of a
  zero-one matrix is the zero-one matrix of the reflexive-transitive closure.

The last statement is proved **from the Kleene algebra axioms alone**, for an arbitrary `K`.  It
is what makes it possible to eliminate epsilon-transitions algebraically in
`RelationAlgebra.Automata.Defs`, which in turn feeds the completeness proof of Kleene algebra.

Everything here is classical and noncomputable: these matrices occur only inside proofs, never
inside the decision procedures of `RelationAlgebra.Decide`.
-/

open scoped Computability

namespace Matrix

/-! ### Finite sums of a constant and zero -/

section Sum
variable {K : Type*} [IdemSemiring K] {ι : Type*} {s : Finset ι} {f : ι → K} {c : K}

/-- In an idempotent semiring a finite sum is below `c` as soon as each summand is. -/
theorem sum_le_of_forall_le (h : ∀ i ∈ s, f i ≤ c) : ∑ i ∈ s, f i ≤ c := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.sum_insert ha]
    exact add_le (h a (Finset.mem_insert_self _ _))
      (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

variable (p : ι → Prop) [DecidablePred p]

/-- A finite sum of copies of `c` and of `0` is `c` when one of the summands is `c`. -/
theorem sum_ite_const_of_exists (c : K) (h : ∃ j ∈ s, p j) :
    (∑ j ∈ s, if p j then c else 0) = c := by
  classical
  obtain ⟨j, hj, hpj⟩ := h
  rw [← Finset.add_sum_erase _ _ hj, if_pos hpj]
  refine add_eq_left_iff_le.2 (sum_le_of_forall_le fun i _ ↦ ?_)
  split_ifs
  · exact le_rfl
  · exact zero_le

/-- A finite sum of copies of `c` and of `0` is `0` when no summand is `c`. -/
theorem sum_ite_const_of_forall_not (c : K) (h : ∀ j ∈ s, ¬ p j) :
    (∑ j ∈ s, if p j then c else 0) = 0 :=
  Finset.sum_eq_zero fun j hj ↦ if_neg (h j hj)

end Sum

/-! ### Labelled zero-one matrices -/

section Defs
variable {K : Type*} [IdemSemiring K] {m n : Type*}

open Classical in
/-- A relation labelled by a constant: `c` at related pairs, `0` elsewhere.  Rectangular, so
that it also describes the initial and final vectors of an automaton. -/
noncomputable def ofRelLab (r : m → n → Prop) (c : K) : Matrix m n K :=
  fun i j => if r i j then c else 0

variable (K) in
/-- The zero-one matrix of a relation: `1` at related pairs, `0` elsewhere. -/
noncomputable def ofRel (r : m → n → Prop) : Matrix m n K := ofRelLab r 1

end Defs

section Basic
variable {K : Type*} [IdemSemiring K] {m n : Type*} {c : K} {r s : m → n → Prop}

open Classical in
@[simp] theorem ofRelLab_apply (i : m) (j : n) :
    ofRelLab r c i j = if r i j then c else 0 := rfl

open Classical in
@[simp] theorem ofRel_apply (i : m) (j : n) :
    ofRel K r i j = if r i j then 1 else 0 := rfl

theorem ofRel_eq_ofRelLab_one : ofRel K r = ofRelLab r (1 : K) := rfl

theorem ofRelLab_mono (h : ∀ i j, r i j → s i j) : ofRelLab r c ≤ ofRelLab s c := by
  classical
  intro i j
  simp only [ofRelLab_apply]
  split_ifs with h₁ h₂
  · exact le_rfl
  · exact absurd (h i j h₁) h₂
  · exact zero_le
  · exact le_rfl

theorem ofRel_mono (h : ∀ i j, r i j → s i j) : ofRel K r ≤ ofRel K s := ofRelLab_mono h

theorem ofRelLab_congr (h : ∀ i j, r i j ↔ s i j) : ofRelLab r c = ofRelLab s c := by
  classical
  ext i j
  simp only [ofRelLab_apply]
  exact if_congr (h i j) rfl rfl

theorem ofRel_congr (h : ∀ i j, r i j ↔ s i j) : ofRel K r = ofRel K s := ofRelLab_congr h

theorem ofRel_sup : ofRel K r + ofRel K s = ofRel K (fun i j => r i j ∨ s i j) := by
  classical
  ext i j
  simp only [Matrix.add_apply, ofRel_apply]
  by_cases h₁ : r i j <;> by_cases h₂ : s i j <;> simp [h₁, h₂]

@[simp] theorem ofRel_false : ofRel K (fun (_ : m) (_ : n) => False) = 0 := by
  classical
  ext i j
  simp

end Basic

section Square
variable {K : Type*} [IdemSemiring K] {n : Type*} [DecidableEq n] {r : n → n → Prop}

@[simp] theorem ofRel_eq_one : ofRel K (· = · : n → n → Prop) = 1 := by
  classical
  ext i j
  simp [Matrix.one_apply]

theorem one_le_ofRel (h : ∀ i, r i i) : (1 : Matrix n n K) ≤ ofRel K r := by
  classical
  intro i j
  rw [Matrix.one_apply]
  split_ifs with hij
  · subst hij
    simp [h i]
  · exact zero_le

end Square

/-! ### Products -/

section Comp
variable {K : Type*} [IdemSemiring K] {l m n : Type*} [Fintype m] {c : K}

/-- Composing a zero-one matrix on the left of a labelled one composes the relations. -/
theorem ofRel_mul_ofRelLab (h : l → m → Prop) (r : m → n → Prop) :
    ofRel K h * ofRelLab r c = ofRelLab (fun i k => ∃ j, h i j ∧ r j k) c := by
  classical
  ext i k
  rw [Matrix.mul_apply]
  simp only [ofRel_apply, ofRelLab_apply]
  have hj : ∀ j : m, ((if h i j then (1 : K) else 0) * if r j k then c else 0) =
      if h i j ∧ r j k then c else 0 := by
    intro j
    by_cases h₁ : h i j <;> by_cases h₂ : r j k <;> simp [h₁, h₂]
  rw [Finset.sum_congr rfl fun j _ ↦ hj j]
  split_ifs with hex
  · obtain ⟨j, hj'⟩ := hex
    exact sum_ite_const_of_exists _ _ ⟨j, Finset.mem_univ j, hj'⟩
  · exact sum_ite_const_of_forall_not _ _ fun j _ hj' ↦ hex ⟨j, hj'⟩

/-- Composing a zero-one matrix on the right of a labelled one composes the relations. -/
theorem ofRelLab_mul_ofRel (r : l → m → Prop) (h : m → n → Prop) :
    ofRelLab r c * ofRel K h = ofRelLab (fun i k => ∃ j, r i j ∧ h j k) c := by
  classical
  ext i k
  rw [Matrix.mul_apply]
  simp only [ofRel_apply, ofRelLab_apply]
  have hj : ∀ j : m, ((if r i j then c else 0) * if h j k then (1 : K) else 0) =
      if r i j ∧ h j k then c else 0 := by
    intro j
    by_cases h₁ : r i j <;> by_cases h₂ : h j k <;> simp [h₁, h₂]
  rw [Finset.sum_congr rfl fun j _ ↦ hj j]
  split_ifs with hex
  · obtain ⟨j, hj'⟩ := hex
    exact sum_ite_const_of_exists _ _ ⟨j, Finset.mem_univ j, hj'⟩
  · exact sum_ite_const_of_forall_not _ _ fun j _ hj' ↦ hex ⟨j, hj'⟩

/-- Composition of zero-one matrices computes the relational composition. -/
theorem ofRel_comp (h : l → m → Prop) (r : m → n → Prop) :
    ofRel K h * ofRel K r = ofRel K (fun i k => ∃ j, h i j ∧ r j k) :=
  ofRel_mul_ofRelLab h r

end Comp

/-! ### The star of a zero-one matrix -/

section Star
variable {K : Type*} [KleeneAlgebra K] {n : Type*} [Fintype n] [DecidableEq n]

/-- **The Kleene star of a zero-one matrix is the zero-one matrix of the reflexive-transitive
closure.**  This is upstream's `bmx.v` characterisation, proved here from the Kleene algebra
axioms for an arbitrary `K`. -/
theorem ofRel_kstar (r : n → n → Prop) :
    (ofRel K r)∗ = ofRel K (Relation.ReflTransGen r) := by
  classical
  apply le_antisymm
  · refine kstar_le_of_mul_le_right (one_le_ofRel fun _ ↦ Relation.ReflTransGen.refl) ?_
    rw [ofRel_comp]
    exact ofRel_mono fun _ _ ⟨_, h₁, h₂⟩ ↦ Relation.ReflTransGen.head h₁ h₂
  · intro i k
    simp only [ofRel_apply]
    split_ifs with h
    · induction h with
      | refl =>
        have h1 : (1 : Matrix n n K) ≤ (ofRel K r)∗ := one_le_kstar
        have h2 := h1 i i
        rwa [Matrix.one_apply_eq] at h2
      | tail hij hjk ih =>
        rename_i j l
        refine le_trans ?_ (kstar_mul_le_kstar (a := ofRel K r) i l)
        rw [Matrix.mul_apply]
        refine le_trans ?_ (Finset.single_le_sum
          (f := fun j ↦ ((ofRel K r)∗) i j * ofRel K r j l)
          (fun _ _ ↦ zero_le) (Finset.mem_univ j))
        calc (1 : K) = 1 * 1 := (one_mul 1).symm
          _ ≤ ((ofRel K r)∗) i j * ofRel K r j l := mul_le_mul' ih (by simp [hjk])
    · exact zero_le

end Star

end Matrix
