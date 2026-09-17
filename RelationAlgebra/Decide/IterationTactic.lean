import RelationAlgebra.TypedIteration
import Lean.Elab.Tactic.Simp

/-!
# Proved preprocessing for strict iteration

The existing reifiers consume multiplication/composition and star. Strict iteration is
expanded through proved equations before reification; no checker syntax or soundness
assumption changes. Only `hkat` expands hypotheses. The `ra` commands additionally apply
basic strict-iteration and converse simplifications before expansion.
-/

open Lean Elab Tactic

namespace RelationAlgebra.IterationTactic

/-- Expand strict iteration in the goal, and optionally in `hkat`'s hypotheses. -/
def expand (hypotheses : Bool := false) : TacticM Unit := do
  if hypotheses then
    evalTactic (← `(tactic| simp (config := { failIfUnchanged := false }) only
      [KleeneAlgebra.kplus_eq_mul_kstar, KleeneCategory.kplus_eq_comp_kstar] at *))
  else
    evalTactic (← `(tactic| simp (config := { failIfUnchanged := false }) only
      [KleeneAlgebra.kplus_eq_mul_kstar, KleeneCategory.kplus_eq_comp_kstar]))

/-- Structural cleanup for `ra`, before expanding the remaining strict iterations. -/
def simplify : TacticM Unit := do
  evalTactic (← `(tactic| simp (config := { failIfUnchanged := false }) only
    [KleeneAlgebra.kplus_zero, KleeneAlgebra.kplus_one, KleeneAlgebra.kplus_top,
      KleeneAlgebra.kplus_idem, KleeneAlgebra.kstar_kplus, KleeneAlgebra.kplus_kstar,
      KleeneAlgebra.star_kplus, KleeneCategory.kplus_bot, KleeneCategory.kplus_id,
      KleeneCategory.kplus_top, KleeneCategory.kplus_idem, KleeneCategory.kstar_kplus,
      KleeneCategory.kplus_kstar, KleeneCategoryWithConverse.converse_kplus]))
  unless (← getGoals).isEmpty do expand

end RelationAlgebra.IterationTactic
