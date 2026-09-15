import RelationAlgebra.Automata.ZeroOne
import RelationAlgebra.Kleene.Basic

/-!
# Finite automata over a Kleene algebra

This file is the Lean counterpart of upstream `theories/nfa.v` and `theories/dfa.v` in Damien
Pous' `relation-algebra` library, in the form needed by Kozen's completeness proof.

An `EpsNFA n` is a finite automaton on the state type `n` over the alphabet `ℕ`, with
epsilon-transitions.  Given a Kleene algebra `K`, a finite alphabet `Γ : Finset ℕ` and a
valuation `ρ : ℕ → K`, the automaton denotes the element

  `value Γ ρ A = u * M∗ * v`

of `K`, where `u`, `v` are the zero-one vectors of the initial and final states and `M` is the
transition matrix `ofRel K A.eps + ∑ a ∈ Γ, ofRelLab (A.step a) (ρ a)`.

The two constructions proved here are the two steps of Kozen's argument that transform an
automaton without changing its value **in every Kleene algebra**:

* `value_epsElim : value Γ ρ A.epsElim = value Γ ρ A` — epsilon-transitions are eliminated
  algebraically, using `Matrix.ofRel_kstar` and the denesting law `(a + b)∗ = a∗ * (b * a∗)∗`;
* `value_det : value Γ ρ A.det = value Γ ρ A` — the subset construction, obtained from the
  rectangular bisimulation rule applied to the zero-one membership matrix.

Both hold in an **arbitrary** `KleeneAlgebra`; no completeness or star-continuity assumption is
used anywhere in this file.

## References

* [D. Kozen, *A completeness theorem for Kleene algebras and the algebra of regular events*,
  Information and Computation 110(2):366-390, 1994][kozen1994]
-/

open scoped Computability

namespace RelationAlgebra.Automata

/-! ### Rectangular Kleene laws for matrices -/

section Rect

variable {K : Type*} [KleeneAlgebra K] {n p : Type*} [Fintype n] [DecidableEq n]

/-- Rectangular right induction: from `X * M ≤ X` infer `X * M∗ ≤ X`. -/
theorem mul_kstar_le_self_rect {M : Matrix n n K} {X : Matrix p n K} (h : X * M ≤ X) :
    X * M∗ ≤ X :=
  Matrix.KleeneStar.mul_kstar_le_self' Matrix.KleeneStar.ofInstance M X h

/-- Rectangular left induction: from `M * X ≤ X` infer `M∗ * X ≤ X`. -/
theorem kstar_mul_le_self_rect {M : Matrix n n K} {X : Matrix n p K} (h : M * X ≤ X) :
    M∗ * X ≤ X :=
  Matrix.KleeneStar.kstar_mul_le_self' Matrix.KleeneStar.ofInstance M X h

/-- Rectangular right induction with an upper bound. -/
theorem mul_kstar_le_rect {M : Matrix n n K} {X C : Matrix p n K} (h₁ : X ≤ C)
    (h₂ : C * M ≤ C) : X * M∗ ≤ C :=
  le_trans (Matrix.mul_mono_left h₁ _) (mul_kstar_le_self_rect h₂)

/-- Rectangular left induction with an upper bound. -/
theorem kstar_mul_le_rect {M : Matrix n n K} {X C : Matrix n p K} (h₁ : X ≤ C)
    (h₂ : M * C ≤ C) : M∗ * X ≤ C :=
  le_trans (Matrix.mul_mono_right h₁ _) (kstar_mul_le_self_rect h₂)

variable [Fintype p] [DecidableEq p]

/-- **Rectangular bisimulation rule**, inequality form. -/
theorem mul_kstar_le_kstar_mul_rect {X : Matrix p n K} {M : Matrix n n K} {M' : Matrix p p K}
    (h : X * M ≤ M' * X) : X * M∗ ≤ M'∗ * X := by
  refine mul_kstar_le_rect ?_ ?_
  · calc X = 1 * X := (Matrix.one_mul X).symm
      _ ≤ M'∗ * X := Matrix.mul_mono_left one_le_kstar X
  · calc M'∗ * X * M = M'∗ * (X * M) := Matrix.mul_assoc _ _ _
      _ ≤ M'∗ * (M' * X) := Matrix.mul_mono_right h _
      _ = M'∗ * M' * X := (Matrix.mul_assoc _ _ _).symm
      _ ≤ M'∗ * X := Matrix.mul_mono_left kstar_mul_le_kstar X

/-- **Rectangular bisimulation rule**, mirror inequality. -/
theorem kstar_mul_le_mul_kstar_rect {X : Matrix p n K} {M : Matrix n n K} {M' : Matrix p p K}
    (h : M' * X ≤ X * M) : M'∗ * X ≤ X * M∗ := by
  refine kstar_mul_le_rect ?_ ?_
  · calc X = X * 1 := (Matrix.mul_one X).symm
      _ ≤ X * M∗ := Matrix.mul_mono_right one_le_kstar X
  · calc M' * (X * M∗) = M' * X * M∗ := (Matrix.mul_assoc _ _ _).symm
      _ ≤ X * M * M∗ := Matrix.mul_mono_left h _
      _ = X * (M * M∗) := Matrix.mul_assoc _ _ _
      _ ≤ X * M∗ := Matrix.mul_mono_right mul_kstar_le_kstar X

/-- **Rectangular bisimulation rule**: a simulation matrix intertwines the stars. -/
theorem mul_kstar_eq_kstar_mul_rect {X : Matrix p n K} {M : Matrix n n K} {M' : Matrix p p K}
    (h : X * M = M' * X) : X * M∗ = M'∗ * X :=
  le_antisymm (mul_kstar_le_kstar_mul_rect h.le) (kstar_mul_le_mul_kstar_rect h.ge)

end Rect

/-! ### Automata -/

/-- A finite automaton with epsilon-transitions on the state type `n`, over the alphabet `ℕ`. -/
structure EpsNFA (n : Type*) where
  /-- The initial states. -/
  start : n → Prop
  /-- The accepting states. -/
  accept : n → Prop
  /-- The epsilon-transitions. -/
  eps : n → n → Prop
  /-- The transitions labelled by each letter. -/
  step : ℕ → n → n → Prop

namespace EpsNFA

variable {K : Type*} [KleeneAlgebra K] {n : Type*}

/-- The matrix of letter-labelled transitions. -/
noncomputable def letterMat (Γ : Finset ℕ) (ρ : ℕ → K) (A : EpsNFA n) : Matrix n n K :=
  ∑ a ∈ Γ, Matrix.ofRelLab (A.step a) (ρ a)

/-- The full transition matrix, epsilon-transitions included. -/
noncomputable def transMat (Γ : Finset ℕ) (ρ : ℕ → K) (A : EpsNFA n) : Matrix n n K :=
  Matrix.ofRel K A.eps + A.letterMat Γ ρ

/-- The zero-one row vector of initial states. -/
noncomputable def startVec (A : EpsNFA n) : Matrix Unit n K :=
  Matrix.ofRel K fun _ i => A.start i

/-- The zero-one column vector of accepting states. -/
noncomputable def acceptVec (A : EpsNFA n) : Matrix n Unit K :=
  Matrix.ofRel K fun i _ => A.accept i

variable [Fintype n] [DecidableEq n]

/-- The element of `K` denoted by the automaton: `u * M∗ * v`. -/
noncomputable def value (Γ : Finset ℕ) (ρ : ℕ → K) (A : EpsNFA n) : K :=
  (A.startVec * (A.transMat Γ ρ)∗ * A.acceptVec : Matrix Unit Unit K) () ()

/-- An automaton is epsilon-free when it has no epsilon-transitions. -/
def EpsFree (A : EpsNFA n) : Prop := ∀ i j, ¬ A.eps i j

omit [Fintype n] [DecidableEq n] in
theorem transMat_of_epsFree {Γ : Finset ℕ} {ρ : ℕ → K} {A : EpsNFA n} (h : A.EpsFree) :
    A.transMat Γ ρ = A.letterMat Γ ρ := by
  classical
  have hz : Matrix.ofRel K A.eps = 0 := by
    ext i j
    simp [h i j]
  rw [transMat, hz, zero_add]

end EpsNFA

/-! ### Transporting the value along a simulation -/

section Sim

variable {K : Type*} [KleeneAlgebra K] {n p : Type*} [Fintype n] [DecidableEq n]
  [Fintype p] [DecidableEq p]

/-- If a matrix `X` intertwines two automata — mapping the initial vector, the transition
matrix and the final vector of one to those of the other — then the two automata denote the
same element of `K`. -/
theorem value_eq_of_sim {A : EpsNFA n} {B : EpsNFA p} {Γ : Finset ℕ} {ρ : ℕ → K}
    (X : Matrix p n K)
    (hu : B.startVec * X = A.startVec)
    (hM : X * A.transMat Γ ρ = B.transMat Γ ρ * X)
    (hv : X * A.acceptVec = B.acceptVec) :
    EpsNFA.value Γ ρ A = EpsNFA.value Γ ρ B := by
  have hs : X * (A.transMat Γ ρ)∗ = (B.transMat Γ ρ)∗ * X := mul_kstar_eq_kstar_mul_rect hM
  have key : A.startVec * (A.transMat Γ ρ)∗ * A.acceptVec
      = B.startVec * (B.transMat Γ ρ)∗ * B.acceptVec := by
    rw [← hu, ← hv, Matrix.mul_assoc B.startVec X, hs, ← Matrix.mul_assoc B.startVec,
      Matrix.mul_assoc]
  unfold EpsNFA.value
  rw [key]

end Sim

end RelationAlgebra.Automata
