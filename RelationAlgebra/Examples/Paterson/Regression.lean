import RelationAlgebra.Examples.Paterson

/-! # Regression checks for Paterson's flowcharts

Besides the universal equality, check its partial-execution meaning with constantly false
and true predicates, and the necessity of the unread-variable condition in dead-store elimination.
-/
open scoped Computability SetRel KAT
namespace Paterson.Regression

/-- The public theorem has no assumptions on its three interpretations. -/
theorem arbitrary_interpretation (f : ℕ → ℕ) (g : ℕ → ℕ → ℕ) (p : ℕ → Bool) :
    Programs.s6a.denote ⟨f, g, p⟩ = Programs.s6e.denote ⟨f, g, p⟩ := paterson _

/-- With the predicate always false, the simple scheme has no terminating executions. -/
theorem false_predicate_rhs (f : ℕ → ℕ) (g : ℕ → ℕ → ℕ) :
    Programs.s6e.denote ⟨f, g, fun _ => false⟩ = 0 := by
  let M : Interpretation := ⟨f, g, fun _ => false⟩
  have hb : Programs.a2.denote M = ⊥ := by ext s; simp [M, BExpr.denote, BExpr.eval]
  have ht : (⌜Programs.a2.denote M⌝ : SetRel State State) = 0 := by rw [hb, KAT.test_bot]
  change Programs.s6e.denote M = 0
  simp only [Programs.s6e, Prog.denote, ht, mul_zero, zero_mul]

/-- The large scheme also has no terminating executions for the constantly false predicate. -/
theorem false_predicate_lhs (f : ℕ → ℕ) (g : ℕ → ℕ → ℕ) :
    Programs.s6a.denote ⟨f, g, fun _ => false⟩ = 0 := by
  rw [paterson, false_predicate_rhs]

/-- The final store has the result in `io` and zero in every temporary. -/
def output (n : ℕ) : State
  | .io => n
  | _ => 0

/-- For an always-true predicate the simple scheme returns `g (f input) (f input)`
without iterating, and clears every temporary cell. -/
theorem true_predicate_rhs (f : ℕ → ℕ) (g : ℕ → ℕ → ℕ) :
    Programs.s6e.denote ⟨f, g, fun _ => true⟩ =
      graph (fun s => output (g (f (s .io)) (f (s .io)))) := by
  let M : Interpretation := ⟨f, g, fun _ => true⟩
  have hb : Programs.a2.denote M = ⊤ := by ext s; simp [M, BExpr.denote, BExpr.eval]
  change Programs.s6e.denote M = _
  simp only [Programs.s6e, Prog.denote, BExpr.denote_not, hb, compl_top,
    KAT.test_top, KAT.test_bot, zero_mul, kstar_zero, mul_one]
  simp only [assign, graph_mul]
  congr 1
  funext s x
  cases x <;> simp [update, AExpr.eval, Function.comp_def, output, M]

/-- The large scheme returns the same value and clears the same cells. -/
theorem true_predicate_lhs (f : ℕ → ℕ) (g : ℕ → ℕ → ℕ) :
    Programs.s6a.denote ⟨f, g, fun _ => true⟩ =
      graph (fun s => output (g (f (s .io)) (f (s .io)))) := by
  rw [paterson, true_predicate_rhs]

/-- A loop that tests `y1` is correctly excluded from the unread-variable rule. -/
example : (Prog.star (.seq (.assign .y1 .zero)
    (.test (.pred (.var .y1))))).dontRead .y1 = false := by decide

/-- Erasing a write without clearing the cell afterwards changes the state relation. -/
theorem clearing_is_necessary : assign ⟨id, Nat.add, fun _ => true⟩ .y1 .zero ≠ 1 := by
  intro h
  have hs : ((fun _ => 1), (fun _ => 1)) ∈
      assign ⟨id, Nat.add, fun _ => true⟩ .y1 .zero := by
    rw [h]
    rfl
  change (fun _ : Loc => 1) = update ⟨id, Nat.add, fun _ => true⟩ .y1 .zero (fun _ => 1) at hs
  have hh := congrFun hs .y1
  simp [update, AExpr.eval] at hh

/-- An interpretation whose execution takes one iteration of the simple scheme's loop:
`1 → 2 → 4 → 8`, with only `2` failing the predicate. -/
def oneLoop : Interpretation :=
  ⟨Nat.succ, Nat.add, fun n => n == 1 || n == 4 || n == 8⟩

private def onePass : Prog :=
  Programs.s2 * .test Programs.a2 * Programs.q222 *
    (.test (.not Programs.a2) * Programs.r22 * .test Programs.a2 * Programs.q222) *
    .test Programs.a2 * Programs.z2

/-- A concrete execution exercising the star, as well as the final cleanup. -/
theorem rhs_one_iteration : (output 0, output 8) ∈ Programs.s6e.denote oneLoop := by
  have hle : onePass.denote oneLoop ≤ Programs.s6e.denote oneLoop := by
    simp only [onePass, Programs.s6e, Prog.denote, BExpr.denote_not]
    kat
  apply hle
  suffices h : output 8 =
      Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (output 0) .y2 8) .io 8) .y1 0) .y2 0) .y3 0) .y4 0 by
    simpa [onePass, Prog.denote, assign, graph, SetRel.mem_mul, SetRel.test_def,
      BExpr.denote, BExpr.eval, AExpr.eval, update, oneLoop, output] using h
  funext x
  cases x <;> simp [output]

/-- The large scheme admits the same concrete terminating execution. -/
theorem lhs_one_iteration : (output 0, output 8) ∈ Programs.s6a.denote oneLoop := by
  rw [paterson]
  exact rhs_one_iteration

end Paterson.Regression
