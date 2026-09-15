import RelationAlgebra.Automata.Det
import Mathlib.Computability.Language

/-!
# The language of a deterministic automaton

Instantiating the value of an automaton at the Kleene algebra `Language ℕ` with the valuation
`a ↦ {[a]}` computes the language it accepts.  For a **deterministic** automaton this language
has the expected concrete description: `w` is accepted from `i` exactly when all its letters lie
in the alphabet `Γ` and the run of `w` from `i` ends in an accepting state.

This is the bridge between the algebraic value of an automaton, which is what Kozen's argument
manipulates, and the language semantics, which is what the hypothesis of the completeness
theorem talks about.

## References

* Damien Pous, `relation-algebra`, `theories/dfa.v`.
-/

open scoped Computability

namespace RelationAlgebra.Automata

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Sums of languages -/

theorem mem_finset_sum {α ι : Type*} (s : Finset ι) (f : ι → Language α) (w : List α) :
    w ∈ (∑ j ∈ s, f j) ↔ ∃ j ∈ s, w ∈ f j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.sum_insert ha]
    simp only [Language.mem_add, ih, Finset.mem_insert]
    constructor
    · rintro (h | ⟨j, hj, hw⟩)
      · exact ⟨a, Or.inl rfl, h⟩
      · exact ⟨j, Or.inr hj, hw⟩
    · rintro ⟨j, rfl | hj, hw⟩
      · exact Or.inl hw
      · exact Or.inr ⟨j, hj, hw⟩

/-! ### Runs -/

/-- The state reached from `i` by reading the word `w`. -/
def run (nxt : ℕ → n → n) : n → List ℕ → n
  | i, [] => i
  | i, a :: w => run nxt (nxt a i) w

omit [Fintype n] [DecidableEq n] in
@[simp] theorem run_nil (nxt : ℕ → n → n) (i : n) : run nxt i [] = i := rfl

omit [Fintype n] [DecidableEq n] in
@[simp] theorem run_cons (nxt : ℕ → n → n) (i : n) (a : ℕ) (w : List ℕ) :
    run nxt i (a :: w) = run nxt (nxt a i) w := rfl

/-- The language accepted from the state `i`, over the alphabet `Γ`. -/
def langOf (A : EpsNFA n) (nxt : ℕ → n → n) (Γ : Finset ℕ) (i : n) : Language ℕ :=
  {w | (∀ x ∈ w, x ∈ Γ) ∧ A.accept (run nxt i w)}

omit [Fintype n] [DecidableEq n] in
theorem mem_langOf {A : EpsNFA n} {nxt : ℕ → n → n} {Γ : Finset ℕ} {i : n} {w : List ℕ} :
    w ∈ langOf A nxt Γ i ↔ (∀ x ∈ w, x ∈ Γ) ∧ A.accept (run nxt i w) := Iff.rfl

omit [Fintype n] [DecidableEq n] in
theorem nil_mem_langOf_iff {A : EpsNFA n} {nxt : ℕ → n → n} {Γ : Finset ℕ} {i : n} :
    [] ∈ langOf A nxt Γ i ↔ A.accept i := by
  simp [mem_langOf]

omit [Fintype n] [DecidableEq n] in
theorem cons_mem_langOf_iff {A : EpsNFA n} {nxt : ℕ → n → n} {Γ : Finset ℕ} {i : n} {a : ℕ}
    {w : List ℕ} :
    a :: w ∈ langOf A nxt Γ i ↔ a ∈ Γ ∧ w ∈ langOf A nxt Γ (nxt a i) := by
  simp only [mem_langOf, run_cons, List.mem_cons, forall_eq_or_imp]
  tauto

omit [Fintype n] [DecidableEq n] in
/-- The derivative of the language of a state is the language of its successor. -/
theorem langOf_deriv {A : EpsNFA n} {nxt : ℕ → n → n} {Γ : Finset ℕ} {i : n} {a : ℕ}
    (ha : a ∈ Γ) :
    langOf A nxt Γ (nxt a i) = {w | a :: w ∈ langOf A nxt Γ i} := by
  ext w
  exact ⟨fun hw ↦ cons_mem_langOf_iff.2 ⟨ha, hw⟩, fun hw ↦ (cons_mem_langOf_iff.1 hw).2⟩

/-! ### The value of a deterministic automaton -/

section Value

variable (A : EpsNFA n) {init : n} {nxt : ℕ → n → n} (Γ : Finset ℕ)

/-- The valuation sending a letter to the corresponding one-letter language. -/
def letterVal : ℕ → Language ℕ := fun a => {[a]}

omit [Fintype n] [DecidableEq n] in
theorem mem_transMat_apply (h : A.IsDet init nxt) (i j : n) (w : List ℕ) :
    w ∈ A.transMat Γ letterVal i j ↔ ∃ a ∈ Γ, w = [a] ∧ j = nxt a i := by
  classical
  rw [EpsNFA.transMat_of_epsFree h.epsFree, EpsNFA.letterMat, Matrix.sum_apply, mem_finset_sum]
  constructor
  · rintro ⟨a, haΓ, hw⟩
    simp only [Matrix.ofRelLab_apply] at hw
    by_cases hstep : A.step a i j
    · rw [if_pos hstep] at hw
      exact ⟨a, haΓ, hw, (h.step_iff a i j).1 hstep⟩
    · rw [if_neg hstep, Language.zero_def] at hw
      exact absurd hw (Set.notMem_empty w)
  · rintro ⟨a, haΓ, rfl, hj⟩
    refine ⟨a, haΓ, ?_⟩
    simp only [Matrix.ofRelLab_apply, if_pos ((h.step_iff a i j).2 hj)]
    rfl

omit [DecidableEq n] in
theorem startVec_mul_apply (h : ∀ i, A.start i ↔ i = init) (Z : Matrix n Unit (Language ℕ)) :
    (A.startVec * Z : Matrix Unit Unit (Language ℕ)) () () = Z init () := by
  classical
  rw [Matrix.mul_apply, Finset.sum_eq_single_of_mem init (Finset.mem_univ init)]
  · rw [EpsNFA.startVec, Matrix.ofRel_apply, if_pos ((h init).2 rfl), one_mul]
  · intro b _ hb
    rw [EpsNFA.startVec, Matrix.ofRel_apply, if_neg, zero_mul]
    exact fun hs ↦ hb ((h b).1 hs)

/-- **The value of a deterministic automaton in the language model is the language it
accepts.** -/
theorem value_eq_langOf (h : A.IsDet init nxt) :
    A.value Γ letterVal = langOf A nxt Γ init := by
  classical
  set M := A.transMat Γ letterVal with hM
  set Z : Matrix n Unit (Language ℕ) := M∗ * A.acceptVec with hZ
  set C : Matrix n Unit (Language ℕ) := fun i _ => langOf A nxt Γ i with hC
  -- the fixpoint equation satisfied by `Z`
  have h1 : (1 : Matrix n n (Language ℕ)) + M * M∗ = M∗ := one_add_mul_kstar
  have hZfix : Z = M * Z + A.acceptVec := by
    rw [hZ]
    conv_lhs => rw [← h1]
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc,
      add_comm A.acceptVec (M * (M∗ * A.acceptVec))]
  -- `C` is a pre-fixpoint, hence `Z ≤ C`
  have hvC : A.acceptVec ≤ C := by
    intro i u
    rw [EpsNFA.acceptVec, Matrix.ofRel_apply]
    split_ifs with hacc
    · intro w hw
      have hw' : w = [] := hw
      subst hw'
      exact nil_mem_langOf_iff.2 hacc
    · exact Set.empty_subset _
  have hMC : M * C ≤ C := by
    intro i u
    rw [Matrix.mul_apply]
    intro w hw
    obtain ⟨j, -, hj⟩ :=
      (mem_finset_sum Finset.univ (fun j ↦ M i j * C j u) w).1 hw
    obtain ⟨x, hx, y, hy, rfl⟩ := Language.mem_mul.1 hj
    obtain ⟨a, haΓ, rfl, rfl⟩ := (mem_transMat_apply A Γ h i j x).1 hx
    exact cons_mem_langOf_iff.2 ⟨haΓ, hy⟩
  have hZC : Z ≤ C := by
    rw [hZ]
    exact kstar_mul_le_rect hvC hMC
  -- conversely `C ≤ Z`, by induction on the length of the word
  have hCZ : ∀ (w : List ℕ) (i : n), w ∈ langOf A nxt Γ i → w ∈ Z i () := by
    intro w
    induction w with
    | nil =>
      intro i hw
      have hacc : [] ∈ (A.acceptVec : Matrix n Unit (Language ℕ)) i () := by
        rw [EpsNFA.acceptVec, Matrix.ofRel_apply, if_pos (nil_mem_langOf_iff.1 hw)]
        exact rfl
      rw [hZfix]
      exact Or.inr hacc
    | cons a w ih =>
      intro i hw
      obtain ⟨haΓ, hw'⟩ := cons_mem_langOf_iff.1 hw
      have hmem : a :: w ∈ (M * Z) i () := by
        rw [Matrix.mul_apply]
        refine (mem_finset_sum Finset.univ (fun j ↦ M i j * Z j ()) (a :: w)).2
          ⟨nxt a i, Finset.mem_univ _, Language.mem_mul.2 ⟨[a], ?_, w, ih _ hw', rfl⟩⟩
        exact (mem_transMat_apply A Γ h i (nxt a i) [a]).2 ⟨a, haΓ, rfl, rfl⟩
      rw [hZfix]
      exact Or.inl hmem
  have hZeq : Z init () = langOf A nxt Γ init :=
    le_antisymm (hZC init ()) (fun w hw ↦ hCZ w init hw)
  rw [EpsNFA.value, Matrix.mul_assoc, startVec_mul_apply A h.start_iff, ← hM, ← hZ, hZeq]

end Value

end RelationAlgebra.Automata
