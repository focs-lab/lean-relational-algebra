import RelationAlgebra.Automata.Defs

/-!
# Epsilon-elimination and determinisation

Two transformations of automata that preserve the denoted element of **every** Kleene algebra:

* `EpsNFA.epsElim` removes epsilon-transitions, by saturating the initial states and
  post-composing every letter transition with the reflexive-transitive closure of the
  epsilon-transitions.  Correctness (`EpsNFA.value_epsElim`) is the denesting law
  `(a + b)∗ = a∗ * (b * a∗)∗` together with `Matrix.ofRel_kstar`.
* `EpsNFA.det` is the subset construction.  Correctness (`EpsNFA.value_det`) follows from the
  rectangular bisimulation rule applied to the zero-one membership matrix `EpsNFA.memMat`,
  exactly as in Kozen's proof.

`EpsNFA.IsDet` records that an automaton is deterministic with a given initial state and
transition function; `EpsNFA.det_isDet` shows the subset construction produces one.

## References

* [D. Kozen, *A completeness theorem for Kleene algebras and the algebra of regular events*,
  Information and Computation 110(2):366-390, 1994][kozen1994]
* Damien Pous, `relation-algebra`, `theories/nfa.v` and `theories/ka_completeness.v`.
-/

open scoped Computability

namespace RelationAlgebra.Automata

namespace EpsNFA

variable {K : Type*} [KleeneAlgebra K] {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Epsilon-elimination -/

/-- Epsilon-elimination: saturate the initial states along epsilon-transitions and
post-compose each letter transition with the epsilon-closure. -/
def epsElim (A : EpsNFA n) : EpsNFA n where
  start i := ∃ j, A.start j ∧ Relation.ReflTransGen A.eps j i
  accept := A.accept
  eps _ _ := False
  step a i k := ∃ j, A.step a i j ∧ Relation.ReflTransGen A.eps j k

omit [Fintype n] [DecidableEq n] in
theorem epsElim_epsFree (A : EpsNFA n) : A.epsElim.EpsFree := fun _ _ h ↦ h

omit [Fintype n] [DecidableEq n] in
@[simp] theorem epsElim_acceptVec (A : EpsNFA n) :
    (A.epsElim.acceptVec : Matrix n Unit K) = A.acceptVec := rfl

theorem startVec_epsElim (A : EpsNFA n) :
    (A.epsElim.startVec : Matrix Unit n K) = A.startVec * (Matrix.ofRel K A.eps)∗ := by
  classical
  rw [Matrix.ofRel_kstar, startVec, startVec, Matrix.ofRel_comp]
  rfl

theorem letterMat_epsElim (Γ : Finset ℕ) (ρ : ℕ → K) (A : EpsNFA n) :
    A.epsElim.letterMat Γ ρ = A.letterMat Γ ρ * (Matrix.ofRel K A.eps)∗ := by
  classical
  rw [Matrix.ofRel_kstar, letterMat, letterMat, Matrix.sum_mul]
  exact Finset.sum_congr rfl fun a _ ↦ (Matrix.ofRelLab_mul_ofRel _ _).symm

/-- **Epsilon-elimination preserves the value**, in every Kleene algebra. -/
theorem value_epsElim (Γ : Finset ℕ) (ρ : ℕ → K) (A : EpsNFA n) :
    A.epsElim.value Γ ρ = A.value Γ ρ := by
  classical
  have h1 : A.epsElim.transMat Γ ρ = A.letterMat Γ ρ * (Matrix.ofRel K A.eps)∗ := by
    rw [transMat_of_epsFree (epsElim_epsFree A), letterMat_epsElim]
  have h2 : (A.transMat Γ ρ)∗
      = (Matrix.ofRel K A.eps)∗ * (A.letterMat Γ ρ * (Matrix.ofRel K A.eps)∗)∗ := by
    rw [transMat, KleeneAlgebra.kstar_add]
  have key : A.epsElim.startVec * (A.epsElim.transMat Γ ρ)∗ * A.epsElim.acceptVec
      = A.startVec * (A.transMat Γ ρ)∗ * A.acceptVec := by
    calc A.epsElim.startVec * (A.epsElim.transMat Γ ρ)∗ * A.epsElim.acceptVec
        = A.startVec * (Matrix.ofRel K A.eps)∗
            * (A.letterMat Γ ρ * (Matrix.ofRel K A.eps)∗)∗ * A.acceptVec := by
          rw [startVec_epsElim, h1, epsElim_acceptVec]
      _ = A.startVec * ((Matrix.ofRel K A.eps)∗
            * (A.letterMat Γ ρ * (Matrix.ofRel K A.eps)∗)∗) * A.acceptVec :=
          congrArg (· * A.acceptVec) (Matrix.mul_assoc A.startVec (Matrix.ofRel K A.eps)∗
            (A.letterMat Γ ρ * (Matrix.ofRel K A.eps)∗)∗)
      _ = A.startVec * (A.transMat Γ ρ)∗ * A.acceptVec := by rw [h2]
  unfold value
  rw [key]

/-! ### Determinisation -/

open Classical in
/-- The subset construction. -/
def det (A : EpsNFA n) : EpsNFA (Finset n) where
  start S := S = Finset.univ.filter A.start
  accept S := ∃ i ∈ S, A.accept i
  eps _ _ := False
  step a S T := T = Finset.univ.filter fun j => ∃ i ∈ S, A.step a i j

omit [DecidableEq n] in
theorem det_epsFree (A : EpsNFA n) : (det A).EpsFree := fun _ _ h ↦ h

variable (K) in
open Classical in
/-- The zero-one matrix relating a subset to its elements. -/
noncomputable def memMat : Matrix (Finset n) n K := Matrix.ofRel K fun S i => i ∈ S

omit [DecidableEq n] in
theorem startVec_det_mul_memMat (A : EpsNFA n) :
    (det A).startVec * memMat K = (A.startVec : Matrix Unit n K) := by
  classical
  rw [startVec, startVec, memMat, Matrix.ofRel_comp]
  refine Matrix.ofRel_congr fun _ i ↦ ?_
  constructor
  · rintro ⟨S, rfl, hi⟩
    simpa using hi
  · intro hi
    exact ⟨_, rfl, by simpa using hi⟩

omit [DecidableEq n] in
theorem memMat_mul_acceptVec (A : EpsNFA n) :
    memMat K * (A.acceptVec : Matrix n Unit K) = (det A).acceptVec := by
  classical
  rw [acceptVec, acceptVec, memMat, Matrix.ofRel_comp]
  exact Matrix.ofRel_congr fun S _ ↦ ⟨fun ⟨i, hi, ha⟩ ↦ ⟨i, hi, ha⟩,
    fun ⟨i, hi, ha⟩ ↦ ⟨i, hi, ha⟩⟩

omit [DecidableEq n] in
theorem memMat_mul_letterMat (Γ : Finset ℕ) (ρ : ℕ → K) (A : EpsNFA n) :
    memMat K * A.letterMat Γ ρ = (det A).letterMat Γ ρ * memMat K := by
  classical
  rw [letterMat, letterMat, Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [memMat, Matrix.ofRel_mul_ofRelLab, Matrix.ofRelLab_mul_ofRel]
  refine Matrix.ofRelLab_congr fun S j ↦ ?_
  constructor
  · rintro ⟨i, hi, hstep⟩
    refine ⟨_, rfl, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨i, hi, hstep⟩
  · rintro ⟨T, rfl, hj⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    obtain ⟨i, hi, hstep⟩ := hj
    exact ⟨i, hi, hstep⟩

/-- **The subset construction preserves the value**, in every Kleene algebra. -/
theorem value_det (Γ : Finset ℕ) (ρ : ℕ → K) (A : EpsNFA n) (hA : A.EpsFree) :
    A.value Γ ρ = (det A).value Γ ρ := by
  classical
  refine value_eq_of_sim (memMat K) (startVec_det_mul_memMat A) ?_ (memMat_mul_acceptVec A)
  rw [transMat_of_epsFree hA, transMat_of_epsFree (det_epsFree A)]
  exact memMat_mul_letterMat Γ ρ A

/-! ### Deterministic automata -/

/-- A witness that an automaton is deterministic, with initial state `init` and transition
function `nxt`. -/
structure IsDet (A : EpsNFA n) (init : n) (nxt : ℕ → n → n) : Prop where
  /-- `init` is the unique initial state. -/
  start_iff : ∀ i, A.start i ↔ i = init
  /-- There are no epsilon-transitions. -/
  epsFree : A.EpsFree
  /-- Transitions are given by the function `nxt`. -/
  step_iff : ∀ a i j, A.step a i j ↔ j = nxt a i

omit [DecidableEq n] in
open Classical in
/-- The subset construction is deterministic. -/
theorem det_isDet (A : EpsNFA n) :
    IsDet (det A) (Finset.univ.filter A.start)
      (fun a S => Finset.univ.filter fun j => ∃ i ∈ S, A.step a i j) where
  start_iff _ := Iff.rfl
  epsFree := det_epsFree A
  step_iff _ _ _ := Iff.rfl

end EpsNFA

end RelationAlgebra.Automata
