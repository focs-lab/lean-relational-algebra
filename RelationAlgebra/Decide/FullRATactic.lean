import RelationAlgebra.Decide.FullRALaws
import Lean.Elab.Tactic.Simp

/-!
# Boolean and residual support for `ra`

The extension recursively normalizes Boolean operations and residuals using proved
rewrites. It also normalizes KA operations inside those expressions, then applies a
bounded structural inclusion check (lattice rules, variance, residuation, cancellation,
and Dedekind). This follows the scope of Pous' `normalisation.v`, without asserting
canonicity, completeness, or equivalence of the two implementations.

Proofs use theorem applications and the ordinary kernel-checked simplifier. Local
hypotheses are not supplied as rules. The existing Kleene-only reifier and its untyping
theorem remain unchanged; neither is applied to Boolean or residual syntax.
-/

open Lean Meta Elab Tactic

namespace RelationAlgebra.FullRA

/-- Recognize extra operations; scalar lattice notation also needs the rewrite path. -/
def hasOperations (e : Expr) (includeJoinBot : Bool := false) : Bool := (e.find? fun t ↦
  match t.getAppFn with
  | .const name _ => t.isApp &&
    ([``Min.min, ``Compl.compl, ``Top.top, ``SDiff.sdiff, ``HImp.himp,
      ``ResiduatedIdemSemiring.ldiv, ``ResiduatedIdemSemiring.rdiv,
      ``ResiduatedKleeneCategory.ldiv, ``ResiduatedKleeneCategory.rdiv].contains name ||
        (includeJoinBot && [``Max.max, ``Bot.bot].contains name))
  | _ => false).isSome

/-- Normalize under every operation; light mode omits distribution and AC sorting. -/
private def normalizePass (light : Bool) : TacticM Unit := do
  evalTactic (← `(tactic| simp (config := { failIfUnchanged := false }) only [
    add_eq_sup, ← bot_eq_zero, sdiff_eq, himp_eq,
    compl_sup, compl_inf, compl_compl, compl_bot, compl_top,
    inf_top_eq, top_inf_eq, inf_bot_eq, bot_inf_eq, sup_top_eq, top_sup_eq,
    sup_bot_eq, bot_sup_eq, inf_idem, sup_idem,
    inf_compl_eq_bot, compl_inf_eq_bot, sup_compl_eq_top, compl_sup_eq_top,
    inf_sup_self, sup_inf_self, le_refl, bot_le, le_top,
    one_mul, mul_one, FullRALaws.bot_mul, FullRALaws.mul_bot, FullRALaws.kstar_bot,
    kstar_one, kstar_idem, ResiduatedKleeneLattice.kstar_top,
    CategoryTheory.Category.id_comp, CategoryTheory.Category.comp_id,
    KleeneCategory.bot_comp, KleeneCategory.comp_bot, FullRALaws.typed_kstar_bot,
    KleeneCategory.kstar_id, KleeneCategory.kstar_idem, KleeneCategory.kstar_top,
    star_star, star_one, KleeneAlgebra.star_bot, KleeneAlgebra.star_sup,
    RelationAlgebra.star_inf, RelationAlgebra.star_compl, RelationAlgebra.star_top,
    Matrix.star_inf, Matrix.star_compl, Matrix.star_top,
    star_mul, KleeneAlgebra.star_kstar,
    KleeneCategoryWithConverse.converse_converse, KleeneCategoryWithConverse.converse_id,
    KleeneCategoryWithConverse.converse_bot, KleeneCategoryWithConverse.converse_top,
    KleeneCategoryWithConverse.converse_sup, KleeneCategoryWithConverse.converse_inf,
    KleeneCategoryWithConverse.converse_compl, KleeneCategoryWithConverse.converse_comp,
    KleeneCategoryWithConverse.converse_kstar,
    ResiduatedIdemSemiring.one_ldiv, ResiduatedIdemSemiring.rdiv_one,
    ResiduatedKleeneLattice.zero_ldiv, ResiduatedKleeneLattice.rdiv_zero,
    ResiduatedKleeneLattice.ldiv_top, ResiduatedKleeneLattice.top_rdiv,
    ResiduatedKleeneAlgebra.kstar_ldiv_self, ResiduatedKleeneAlgebra.kstar_rdiv_self,
    ResiduatedKleeneAlgebra.star_ldiv, ResiduatedKleeneAlgebra.star_rdiv,
    ResiduatedKleeneCategory.id_ldiv, ResiduatedKleeneCategory.rdiv_id,
    ResiduatedKleeneCategory.bot_ldiv, ResiduatedKleeneCategory.rdiv_bot,
    ResiduatedKleeneCategory.ldiv_top, ResiduatedKleeneCategory.top_rdiv,
    ResiduatedKleeneCategory.kstar_ldiv_self, ResiduatedKleeneCategory.kstar_rdiv_self,
    ResiduatedKleeneCategory.converse_ldiv, ResiduatedKleeneCategory.converse_rdiv]))
  if light || (← getGoals).isEmpty then return
  evalTactic (← `(tactic| simp (config := { failIfUnchanged := false }) only [
    FullRALaws.sup_mul, FullRALaws.mul_sup, mul_assoc,
    KleeneCategory.sup_comp, KleeneCategory.comp_sup, CategoryTheory.Category.assoc,
    ResiduatedIdemSemiring.mul_ldiv, ResiduatedIdemSemiring.rdiv_mul,
    ResiduatedIdemSemiring.ldiv_rdiv,
    ResiduatedKleeneLattice.sup_ldiv, ResiduatedKleeneLattice.ldiv_inf,
    ResiduatedKleeneLattice.rdiv_sup, ResiduatedKleeneLattice.inf_rdiv,
    ResiduatedKleeneCategory.comp_ldiv, ResiduatedKleeneCategory.rdiv_comp,
    ResiduatedKleeneCategory.ldiv_rdiv,
    ResiduatedKleeneCategory.sup_ldiv, ResiduatedKleeneCategory.ldiv_inf,
    ResiduatedKleeneCategory.rdiv_sup, ResiduatedKleeneCategory.inf_rdiv,
    inf_sup_left, inf_sup_right, sup_assoc, sup_left_comm, sup_comm,
    inf_assoc, inf_left_comm, inf_comm, inf_idem, sup_idem,
    inf_top_eq, top_inf_eq, inf_bot_eq, bot_inf_eq, sup_top_eq, top_sup_eq,
    sup_bot_eq, bot_sup_eq, inf_compl_eq_bot, compl_inf_eq_bot,
    sup_compl_eq_top, compl_sup_eq_top, inf_sup_self, sup_inf_self,
    le_refl, bot_le, le_top]))

/-- Repeat the two passes when distribution exposes more Boolean simplifications. -/
def normalize (light : Bool) : TacticM Unit := do
  for _ in [:16] do
    let before ← (← getMainGoal).getType
    normalizePass light
    if (← getGoals).isEmpty then return
    let after ← (← getMainGoal).getType
    if before == after then return

/-- The finite rule set used by the structural inclusion checker. -/
private def rules : Array Name := #[
  ``le_rfl, ``bot_le, ``le_top, ``inf_le_left, ``inf_le_right, ``le_sup_left, ``le_sup_right,
  ``ResiduatedKleeneCategory.comp_ldiv_le, ``ResiduatedKleeneCategory.rdiv_comp_le,
  ``ResiduatedKleeneCategory.le_ldiv_comp, ``ResiduatedKleeneCategory.le_comp_rdiv,
  ``ResiduatedKleeneCategory.id_le_ldiv_self, ``ResiduatedKleeneCategory.id_le_rdiv_self,
  ``ResiduatedIdemSemiring.mul_ldiv_le, ``ResiduatedIdemSemiring.rdiv_mul_le,
  ``ResiduatedIdemSemiring.le_ldiv_mul, ``ResiduatedIdemSemiring.le_mul_rdiv,
  ``ResiduatedIdemSemiring.one_le_ldiv_self, ``ResiduatedIdemSemiring.one_le_rdiv_self,
  ``FullRALaws.dedekind_comm, ``FullRALaws.typed_dedekind_comm,
  ``RelationCategory.dedekind, ``RelationCategory.comp_inf_le_inf_comp,
  ``RelationCategory.comp_inf_le_comp_inf, ``RelationAlgebra.dedekind,
  ``RelationAlgebra.mul_inf_le_inf_mul, ``RelationAlgebra.mul_inf_le_mul_inf,
  ``sup_le, ``le_inf, ``le_sup_of_le_left, ``le_sup_of_le_right,
  ``inf_le_of_left_le, ``inf_le_of_right_le,
  ``compl_le_compl, ``KleeneCategoryWithConverse.converse_mono, ``KleeneAlgebra.star_mono,
  ``ResiduatedKleeneCategory.ldiv_le_ldiv, ``ResiduatedKleeneCategory.rdiv_le_rdiv,
  ``ResiduatedIdemSemiring.ldiv_le_ldiv, ``ResiduatedIdemSemiring.rdiv_le_rdiv,
  ``KleeneCategory.comp_le_comp, ``mul_le_mul',
  ``FullRALaws.typed_le_ldiv, ``FullRALaws.typed_le_rdiv,
  ``FullRALaws.le_ldiv, ``FullRALaws.le_rdiv]

/-- Try structural rules with backtracking and a global bound on rule applications. -/
private partial def prove (goal : MVarId) (budget : IO.Ref Nat) : MetaM Bool := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let candidates := if target.isAppOfArity ``Eq 3 then #[``le_antisymm] else rules
  for name in candidates do
    let remaining ← budget.get
    if remaining == 0 then return false
    budget.set (remaining - 1)
    let saved ← saveState
    try
      let gs ← goal.apply (← mkConstWithFreshMVarLevels name)
      let mut ok := true
      for g in gs do
        unless ← prove g budget do
          ok := false
          break
      if ok then return true
    catch _ => pure ()
    saved.restore
  return false

/-- Close a normalized goal if the bounded structural inclusion check succeeds. -/
def close : TacticM Bool := do
  let goal ← getMainGoal
  let saved ← saveState
  if ← prove goal (← IO.mkRef 4096) then
    replaceMainGoal []
    return true
  saved.restore
  return false

end RelationAlgebra.FullRA
