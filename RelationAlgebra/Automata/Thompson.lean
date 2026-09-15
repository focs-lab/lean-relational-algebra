import Mathlib.Data.Matrix.ColumnRowPartitioned
import RelationAlgebra.Automata.Defs
import RelationAlgebra.Decide.Antimirov

/-!
# Thompson's construction

This file is the Lean counterpart of the automaton-building half of upstream
`theories/ka_completeness.v` in Damien Pous' `relation-algebra` library, which formalises
Kozen's completeness proof for Kleene algebra.

To every regular expression `e : KleeneAlgebra.Term` we associate, by Thompson's construction,
a finite automaton with epsilon-transitions `thompson e` whose value **in an arbitrary Kleene
algebra** is the evaluation of `e`:

  `value_thompson : (thompson e).aut.value Γ ρ = KleeneAlgebra.Term.eval ρ e`

(under the hypothesis that every variable of `e` belongs to the finite alphabet `Γ`, which is
needed because `EpsNFA.letterMat` only sums over `Γ`).

The construction is the usual one:

* `zero` has no state at all, `one` a single initial and accepting state with no transition,
  and `var a` two states linked by a single `a`-transition;
* `sumNFA` is the disjoint union, whose transition matrix is block diagonal;
* `mulNFA` is the disjoint union with epsilon-links from the accepting states of the first
  automaton to the initial states of the second, whose transition matrix is block upper
  triangular;
* `starNFA` adds a fresh initial and accepting state with epsilon-links to and from the given
  automaton.

All the computations are carried out with the block formula `Matrix.kstar_fromBlocks` for the
Kleene star of a matrix; the two special cases needed here are `kstarBlockDiag` and
`kstarBlockTri`.  No completeness, star-continuity or finiteness assumption is made on the
Kleene algebra `K`.

## References

* [D. Kozen, *A completeness theorem for Kleene algebras and the algebra of regular events*,
  Information and Computation 110(2):366-390, 1994][kozen1994]
* D. Pous, `relation-algebra`, `theories/ka_completeness.v`.
-/

open scoped Computability

namespace RelationAlgebra.Automata

/-! ### An auxiliary law of Kleene algebra -/

/-- In a Kleene algebra, an element whose square vanishes has star `1 + x`. -/
theorem kstar_eq_one_add_of_mul_self {A : Type*} [KleeneAlgebra A] {x : A} (h : x * x = 0) :
    x∗ = 1 + x := by
  refine le_antisymm (kstar_le_of_mul_le_right le_self_add ?_) (add_le one_le_kstar le_kstar)
  rw [mul_add, mul_one, h, add_zero]
  exact le_add_self

/-! ### Relations and matrices in block form -/

section Blocks

variable {m p : Type*}

/-- Assemble four relations into a relation on a disjoint union of index types. -/
def blockRel (r : m → m → Prop) (b : m → p → Prop) (c : p → m → Prop) (s : p → p → Prop) :
    m ⊕ p → m ⊕ p → Prop
  | Sum.inl i, Sum.inl j => r i j
  | Sum.inl i, Sum.inr j => b i j
  | Sum.inr i, Sum.inl j => c i j
  | Sum.inr i, Sum.inr j => s i j

variable {K : Type*} [KleeneAlgebra K]

/-- The labelled zero-one matrix of a block relation is the matching block matrix. -/
theorem ofRelLab_blockRel (r : m → m → Prop) (b : m → p → Prop) (c : p → m → Prop)
    (s : p → p → Prop) (k : K) :
    Matrix.ofRelLab (blockRel r b c s) k =
      Matrix.fromBlocks (Matrix.ofRelLab r k) (Matrix.ofRelLab b k) (Matrix.ofRelLab c k)
        (Matrix.ofRelLab s k) := by
  ext (i | i) (j | j) <;> rfl

/-- The labelled zero-one matrix of the empty relation vanishes. -/
theorem ofRelLab_false (k : K) : Matrix.ofRelLab (fun (_ : m) (_ : p) ↦ False) k = 0 := by
  classical
  ext i j
  simp

/-- Finite sums of block matrices are computed blockwise. -/
theorem sum_fromBlocks {ι : Type*} (s : Finset ι) (A : ι → Matrix m m K) (B : ι → Matrix m p K)
    (C : ι → Matrix p m K) (D : ι → Matrix p p K) :
    (∑ i ∈ s, Matrix.fromBlocks (A i) (B i) (C i) (D i)) =
      Matrix.fromBlocks (∑ i ∈ s, A i) (∑ i ∈ s, B i) (∑ i ∈ s, C i) (∑ i ∈ s, D i) := by
  ext (i | i) (j | j) <;> simp [Matrix.sum_apply]

variable [Fintype m] [DecidableEq m] [Fintype p] [DecidableEq p]

/-- The star of a block diagonal matrix is block diagonal. -/
theorem kstarBlockDiag (A : Matrix m m K) (D : Matrix p p K) :
    (Matrix.fromBlocks A 0 0 D)∗ = Matrix.fromBlocks A∗ 0 0 D∗ := by
  rw [Matrix.kstar_fromBlocks]
  simp

/-- The star of a block upper triangular matrix. -/
theorem kstarBlockTri (A : Matrix m m K) (B : Matrix m p K) (D : Matrix p p K) :
    (Matrix.fromBlocks A B 0 D)∗ = Matrix.fromBlocks A∗ (A∗ * B * D∗) 0 D∗ := by
  rw [Matrix.kstar_fromBlocks]
  simp

/-- The unique entry of a product of `1 × 1` matrices. -/
theorem mul_unit_apply (X Y : Matrix Unit Unit K) : (X * Y) () () = X () () * Y () () := by
  simp [Matrix.mul_apply]

/-- The value of an automaton on a disjoint union of state types, from its block data. -/
theorem value_eq_of_blocks {A : EpsNFA (m ⊕ p)} {Γ : Finset ℕ} {ρ : ℕ → K}
    {u₁ : Matrix Unit m K} {u₂ : Matrix Unit p K} {v₁ : Matrix m Unit K} {v₂ : Matrix p Unit K}
    {P : Matrix m m K} {Q : Matrix m p K} {R : Matrix p m K} {S : Matrix p p K}
    (hu : A.startVec = Matrix.fromCols u₁ u₂) (hv : A.acceptVec = Matrix.fromRows v₁ v₂)
    (hM : (A.transMat Γ ρ)∗ = Matrix.fromBlocks P Q R S) :
    A.value Γ ρ = ((u₁ * P + u₂ * R) * v₁ + (u₁ * Q + u₂ * S) * v₂) () () := by
  unfold EpsNFA.value
  rw [hu, hv, hM, Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows]

end Blocks

/-! ### The automata of Thompson's construction -/

section Construction

variable {K : Type*} [KleeneAlgebra K] {m p : Type*}

/-- Assemble two automata into one on the disjoint union of their state types, with extra
epsilon-transitions given by `b` (from the left to the right component) and `c` (from the right
to the left component), and with prescribed initial and accepting states. -/
def blockNFA (A : EpsNFA m) (B : EpsNFA p) (st ac : m ⊕ p → Prop) (b : m → p → Prop)
    (c : p → m → Prop) : EpsNFA (m ⊕ p) where
  start := st
  accept := ac
  eps := blockRel A.eps b c B.eps
  step a := blockRel (A.step a) (fun _ _ ↦ False) (fun _ _ ↦ False) (B.step a)

theorem transMat_blockNFA (A : EpsNFA m) (B : EpsNFA p)
    (st ac : m ⊕ p → Prop) (b : m → p → Prop) (c : p → m → Prop) (Γ : Finset ℕ) (ρ : ℕ → K) :
    (blockNFA A B st ac b c).transMat Γ ρ =
      Matrix.fromBlocks (A.transMat Γ ρ) (Matrix.ofRel K b) (Matrix.ofRel K c)
        (B.transMat Γ ρ) := by
  classical
  have h1 : Matrix.ofRel K (blockNFA A B st ac b c).eps =
      Matrix.fromBlocks (Matrix.ofRel K A.eps) (Matrix.ofRel K b) (Matrix.ofRel K c)
        (Matrix.ofRel K B.eps) := ofRelLab_blockRel _ _ _ _ 1
  have h2 : (blockNFA A B st ac b c).letterMat Γ ρ =
      Matrix.fromBlocks (A.letterMat Γ ρ) 0 0 (B.letterMat Γ ρ) := by
    have h3 : ∀ a : ℕ, Matrix.ofRelLab ((blockNFA A B st ac b c).step a) (ρ a) =
        Matrix.fromBlocks (Matrix.ofRelLab (A.step a) (ρ a)) 0 0
          (Matrix.ofRelLab (B.step a) (ρ a)) := by
      intro a
      have h4 : (blockNFA A B st ac b c).step a =
          blockRel (A.step a) (fun _ _ ↦ False) (fun _ _ ↦ False) (B.step a) := rfl
      rw [h4, ofRelLab_blockRel, ofRelLab_false, ofRelLab_false]
    simp only [EpsNFA.letterMat]
    rw [Finset.sum_congr rfl fun a _ ↦ h3 a, sum_fromBlocks, Finset.sum_const_zero,
      Finset.sum_const_zero]
  simp only [EpsNFA.transMat]
  rw [h1, h2, Matrix.fromBlocks_add, add_zero, add_zero]

/-- The automaton with no state, denoting `0`. -/
def zeroNFA : EpsNFA Empty where
  start _ := False
  accept _ := False
  eps _ _ := False
  step _ _ _ := False

/-- The automaton with a single initial and accepting state, denoting `1`. -/
def oneNFA : EpsNFA Unit where
  start _ := True
  accept _ := True
  eps _ _ := False
  step _ _ _ := False

/-- The two-state automaton with a single `a`-transition, denoting the variable `a`. -/
def varNFA (a : ℕ) : EpsNFA Bool where
  start i := i = false
  accept i := i = true
  eps _ _ := False
  step b i j := b = a ∧ i = false ∧ j = true

/-- The disjoint union of two automata: an automaton for the sum. -/
def sumNFA (A : EpsNFA m) (B : EpsNFA p) : EpsNFA (m ⊕ p) :=
  blockNFA A B (Sum.elim A.start B.start) (Sum.elim A.accept B.accept) (fun _ _ ↦ False)
    (fun _ _ ↦ False)

/-- The disjoint union of two automata with epsilon-links from the accepting states of the
first to the initial states of the second: an automaton for the product. -/
def mulNFA (A : EpsNFA m) (B : EpsNFA p) : EpsNFA (m ⊕ p) :=
  blockNFA A B (Sum.elim A.start fun _ ↦ False) (Sum.elim (fun _ ↦ False) B.accept)
    (fun i j ↦ A.accept i ∧ B.start j) (fun _ _ ↦ False)

/-- An automaton with a fresh initial and accepting state linked by epsilon-transitions to the
given one: an automaton for the star. -/
def starNFA (A : EpsNFA m) : EpsNFA (Unit ⊕ m) :=
  blockNFA oneNFA A (Sum.elim (fun _ ↦ True) fun _ ↦ False)
    (Sum.elim (fun _ ↦ True) fun _ ↦ False) (fun _ j ↦ A.start j) fun i _ ↦ A.accept i

end Construction

/-! ### The values of the automata -/

section Values

variable {K : Type*} [KleeneAlgebra K] {m p : Type*} (Γ : Finset ℕ) (ρ : ℕ → K)

theorem value_zeroNFA : (zeroNFA.value Γ ρ : K) = 0 := by
  simp [EpsNFA.value, Matrix.mul_apply]

theorem transMat_oneNFA : (oneNFA.transMat Γ ρ : Matrix Unit Unit K) = 0 := by
  classical
  have h1 : Matrix.ofRel K oneNFA.eps = 0 := Matrix.ofRel_false
  have h2 : oneNFA.letterMat Γ ρ = (0 : Matrix Unit Unit K) := by
    simp only [EpsNFA.letterMat]
    exact Finset.sum_eq_zero fun a _ ↦ ofRelLab_false (ρ a)
  rw [EpsNFA.transMat, h1, h2, add_zero]

theorem value_oneNFA : (oneNFA.value Γ ρ : K) = 1 := by
  classical
  unfold EpsNFA.value
  rw [transMat_oneNFA, kstar_zero, Matrix.mul_one]
  simp [EpsNFA.startVec, EpsNFA.acceptVec, Matrix.mul_apply, oneNFA]

theorem transMat_varNFA {a : ℕ} (ha : a ∈ Γ) :
    (varNFA a).transMat Γ ρ = Matrix.ofRelLab (fun i j ↦ i = false ∧ j = true) (ρ a) := by
  classical
  have h1 : Matrix.ofRel K (varNFA a).eps = 0 := Matrix.ofRel_false
  rw [EpsNFA.transMat, h1, zero_add, EpsNFA.letterMat, Finset.sum_eq_single a]
  · exact Matrix.ofRelLab_congr fun i j ↦ by simp [varNFA]
  · intro b _ hb
    rw [show Matrix.ofRelLab ((varNFA a).step b) (ρ b) =
      Matrix.ofRelLab (fun (_ : Bool) (_ : Bool) ↦ False) (ρ b) from
        Matrix.ofRelLab_congr fun i j ↦ by simp [varNFA, hb]]
    exact ofRelLab_false (ρ b)
  · intro h
    exact absurd ha h

theorem value_varNFA {a : ℕ} (ha : a ∈ Γ) : ((varNFA a).value Γ ρ : K) = ρ a := by
  classical
  have hsq : (Matrix.ofRelLab (fun i j ↦ i = false ∧ j = true) (ρ a) : Matrix Bool Bool K) *
      Matrix.ofRelLab (fun i j ↦ i = false ∧ j = true) (ρ a) = 0 := by
    ext i k
    simp only [Matrix.mul_apply, Matrix.zero_apply, Fintype.sum_bool, Matrix.ofRelLab_apply]
    cases i <;> cases k <;> simp
  unfold EpsNFA.value
  rw [transMat_varNFA Γ ρ ha, kstar_eq_one_add_of_mul_self hsq]
  simp [EpsNFA.startVec, EpsNFA.acceptVec, Matrix.mul_apply, varNFA, Matrix.one_apply]

variable [Fintype m] [DecidableEq m] [Fintype p] [DecidableEq p]

theorem value_sumNFA (A : EpsNFA m) (B : EpsNFA p) :
    (sumNFA A B).value Γ ρ = A.value Γ ρ + B.value Γ ρ := by
  classical
  have hu : (sumNFA A B).startVec =
      (Matrix.fromCols A.startVec B.startVec : Matrix Unit (m ⊕ p) K) := by
    ext i (j | j) <;> rfl
  have hv : (sumNFA A B).acceptVec =
      (Matrix.fromRows A.acceptVec B.acceptVec : Matrix (m ⊕ p) Unit K) := by
    ext (i | i) j <;> rfl
  have hM : ((sumNFA A B).transMat Γ ρ)∗ =
      Matrix.fromBlocks ((A.transMat Γ ρ)∗) 0 0 ((B.transMat Γ ρ)∗) := by
    rw [sumNFA, transMat_blockNFA]
    simp only [Matrix.ofRel_false]
    exact kstarBlockDiag _ _
  rw [value_eq_of_blocks hu hv hM]
  simp only [Matrix.mul_zero, add_zero, zero_add, Matrix.add_apply]
  rfl

theorem value_mulNFA (A : EpsNFA m) (B : EpsNFA p) :
    (mulNFA A B).value Γ ρ = A.value Γ ρ * B.value Γ ρ := by
  classical
  have hu : (mulNFA A B).startVec =
      (Matrix.fromCols A.startVec 0 : Matrix Unit (m ⊕ p) K) := by
    ext i (j | j)
    · rfl
    · simp [EpsNFA.startVec, mulNFA, blockNFA]
  have hv : (mulNFA A B).acceptVec =
      (Matrix.fromRows 0 B.acceptVec : Matrix (m ⊕ p) Unit K) := by
    ext (i | i) j
    · simp [EpsNFA.acceptVec, mulNFA, blockNFA]
    · rfl
  have hlink : Matrix.ofRel K (fun i j ↦ A.accept i ∧ B.start j) =
      (A.acceptVec * B.startVec : Matrix m p K) := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [EpsNFA.acceptVec, EpsNFA.startVec, Matrix.ofRel_apply, Finset.univ_unique,
      Finset.sum_singleton]
    by_cases h₁ : A.accept i <;> by_cases h₂ : B.start j <;> simp [h₁, h₂]
  have hM : ((mulNFA A B).transMat Γ ρ)∗ =
      Matrix.fromBlocks ((A.transMat Γ ρ)∗)
        ((A.transMat Γ ρ)∗ * (A.acceptVec * B.startVec : Matrix m p K) * (B.transMat Γ ρ)∗) 0
        ((B.transMat Γ ρ)∗) := by
    rw [mulNFA, transMat_blockNFA, Matrix.ofRel_false, hlink, kstarBlockTri]
  have hassoc : (A.startVec * ((A.transMat Γ ρ)∗ * (A.acceptVec * B.startVec : Matrix m p K) *
        (B.transMat Γ ρ)∗) * B.acceptVec : Matrix Unit Unit K) =
      (A.startVec * (A.transMat Γ ρ)∗ * A.acceptVec) *
        (B.startVec * (B.transMat Γ ρ)∗ * B.acceptVec) := by
    simp only [Matrix.mul_assoc]
  rw [value_eq_of_blocks hu hv hM]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  rw [hassoc, mul_unit_apply]
  rfl

theorem value_starNFA (A : EpsNFA m) : (starNFA A).value Γ ρ = (A.value Γ ρ)∗ := by
  classical
  have hu : (starNFA A).startVec = Matrix.fromCols (1 : Matrix Unit Unit K) 0 := by
    ext i (j | j)
    · simp [EpsNFA.startVec, starNFA, blockNFA]
    · simp [EpsNFA.startVec, starNFA, blockNFA]
  have hv : (starNFA A).acceptVec = Matrix.fromRows (1 : Matrix Unit Unit K) 0 := by
    ext (i | i) j
    · simp [EpsNFA.acceptVec, starNFA, blockNFA]
    · simp [EpsNFA.acceptVec, starNFA, blockNFA]
  have hT : (starNFA A).transMat Γ ρ =
      Matrix.fromBlocks 0 A.startVec A.acceptVec (A.transMat Γ ρ) := by
    rw [starNFA, transMat_blockNFA, transMat_oneNFA]
    rfl
  unfold EpsNFA.value
  rw [hu, hv, hT, Matrix.kstar_fromBlocks, zero_add, Matrix.fromCols_mul_fromBlocks,
    Matrix.fromCols_mul_fromRows]
  simp only [Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero, Matrix.mul_one, add_zero]
  rw [Matrix.kstar_unique]
  rfl

end Values

/-! ### Thompson's construction -/

/-- A finite automaton together with the finiteness data for its state type. -/
structure Aut where
  /-- The state type. -/
  States : Type
  /-- The state type is finite. -/
  fintypeStates : Fintype States
  /-- The state type has decidable equality. -/
  decEqStates : DecidableEq States
  /-- The underlying automaton. -/
  aut : EpsNFA States

attribute [instance] Aut.fintypeStates Aut.decEqStates

/-- Thompson's construction: an automaton for each regular expression. -/
def thompson : KleeneAlgebra.Term → Aut
  | .zero => ⟨Empty, inferInstance, inferInstance, zeroNFA⟩
  | .one => ⟨Unit, inferInstance, inferInstance, oneNFA⟩
  | .var a => ⟨Bool, inferInstance, inferInstance, varNFA a⟩
  | .add e f =>
      ⟨(thompson e).States ⊕ (thompson f).States, inferInstance, inferInstance,
        sumNFA (thompson e).aut (thompson f).aut⟩
  | .mul e f =>
      ⟨(thompson e).States ⊕ (thompson f).States, inferInstance, inferInstance,
        mulNFA (thompson e).aut (thompson f).aut⟩
  | .star e =>
      ⟨Unit ⊕ (thompson e).States, inferInstance, inferInstance, starNFA (thompson e).aut⟩

/-- The transitions of `thompson e` are labelled only by variables occurring in `e`. -/
theorem thompson_step_subset : ∀ (e : KleeneAlgebra.Term) {a : ℕ} {i j : (thompson e).States},
    (thompson e).aut.step a i j → a ∈ e.vars := by
  intro e
  induction e with
  | zero => intro a i j h; exact h.elim
  | one => intro a i j h; exact h.elim
  | var b => intro a i j h; simp [KleeneAlgebra.Term.vars, h.1]
  | add e f ihe ihf =>
    intro a i j h
    simp only [KleeneAlgebra.Term.vars, List.mem_append]
    obtain (i | i) := i <;> obtain (j | j) := j
    · exact Or.inl (ihe h)
    · exact h.elim
    · exact h.elim
    · exact Or.inr (ihf h)
  | mul e f ihe ihf =>
    intro a i j h
    simp only [KleeneAlgebra.Term.vars, List.mem_append]
    obtain (i | i) := i <;> obtain (j | j) := j
    · exact Or.inl (ihe h)
    · exact h.elim
    · exact h.elim
    · exact Or.inr (ihf h)
  | star e ihe =>
    intro a i j h
    obtain (i | i) := i <;> obtain (j | j) := j
    · exact h.elim
    · exact h.elim
    · exact h.elim
    · exact ihe h

/-- **Thompson's construction is correct**: the value of the automaton `thompson e` in an
arbitrary Kleene algebra is the evaluation of the regular expression `e`. -/
theorem value_thompson {K : Type*} [KleeneAlgebra K] (Γ : Finset ℕ) (ρ : ℕ → K)
    (e : KleeneAlgebra.Term) (he : ∀ a ∈ e.vars, a ∈ Γ) :
    (thompson e).aut.value Γ ρ = KleeneAlgebra.Term.eval ρ e := by
  induction e with
  | zero => exact value_zeroNFA Γ ρ
  | one => exact value_oneNFA Γ ρ
  | var a => exact value_varNFA Γ ρ (he a (by simp [KleeneAlgebra.Term.vars]))
  | add e f ihe ihf =>
    have h1 : ∀ a ∈ e.vars, a ∈ Γ := fun a ha ↦ he a (by
      simp only [KleeneAlgebra.Term.vars, List.mem_append]; exact Or.inl ha)
    have h2 : ∀ a ∈ f.vars, a ∈ Γ := fun a ha ↦ he a (by
      simp only [KleeneAlgebra.Term.vars, List.mem_append]; exact Or.inr ha)
    change (sumNFA (thompson e).aut (thompson f).aut).value Γ ρ = _
    rw [value_sumNFA, ihe h1, ihf h2]
    rfl
  | mul e f ihe ihf =>
    have h1 : ∀ a ∈ e.vars, a ∈ Γ := fun a ha ↦ he a (by
      simp only [KleeneAlgebra.Term.vars, List.mem_append]; exact Or.inl ha)
    have h2 : ∀ a ∈ f.vars, a ∈ Γ := fun a ha ↦ he a (by
      simp only [KleeneAlgebra.Term.vars, List.mem_append]; exact Or.inr ha)
    change (mulNFA (thompson e).aut (thompson f).aut).value Γ ρ = _
    rw [value_mulNFA, ihe h1, ihf h2]
    rfl
  | star e ihe =>
    change (starNFA (thompson e).aut).value Γ ρ = _
    rw [value_starNFA, ihe he]
    rfl

end RelationAlgebra.Automata
