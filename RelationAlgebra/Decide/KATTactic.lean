import RelationAlgebra.Decide.IterationTactic
import RelationAlgebra.KATCompleteness.Main
import RelationAlgebra.KAT.Hoare
import RelationAlgebra.Models.Bool
import RelationAlgebra.Decide.KATReify
import RelationAlgebra.Decide.TypedKATTactic

/-!
# The `kat` tactic

Strict iteration `a⁺` is expanded by proved rewrites before reification. Typed endomorphisms
expand to `f ≫ f∗`; no additional algebraic assumption is needed.

`kat` closes goals `a = b` or `a ≤ b` in an *arbitrary* Kleene algebra with tests (e.g.
relations `SetRel α α` with tests `Set α`, after `open scoped SetRel`; or any Kleene algebra
with the trivial tests `Bool`) that are valid in all KATs: the two sides are reified into
`KAT.KTerm`s (tests being reified into Boolean terms `KAT.BTerm`), their guarded-string
semantics are compared by `KAT.KTerm.decideEq` (kernel-evaluated), and
`KAT.Completeness.eval_eq_of_decideEq` turns the certificate into the goal.

Categorical goals `p = q` or `p ≤ q`, for `p q : X ⟶ Y`, use typed completeness instead.
The reifier understands `⊥`, `𝟙`, `⊔`, `≫`, `∗` and `TypedKAT.test`, keeping tests separate
at each object. It needs a `KleeneCategory` and, when tests occur, a `TypedKAT` instance.
See `RelationAlgebra.Examples.TypedDecide` for heterogeneous examples.

The tactic introduces binders and focuses on one goal. Guarded commands `KAT.ifThenElse`,
`KAT.whileDo` and Hoare triples `KAT.HoareTriple` are unfolded first, so `kat` proves
`KAT.HoareTriple ⊤ (KAT.whileDo b p) bᶜ` directly. The
Boolean operations `\` and `⇨` on tests are rewritten to `⊓`, `⊔`, `ᶜ` (by `sdiff_eq`,
`himp_eq`) in the same preprocessing step, since only the latter are interpreted
definitionally by the reification.  When no test occurs in the goal the trivial tests `Bool`
are used. The typed guarded commands and Hoare triples are unfolded as well.

`kat n` uses `n` units of fuel (default `1000`).  The number of atoms is `2 ^ k` for `k`
distinct primitive tests, so goals with many tests are expensive. In typed goals, `k` is
the largest number of primitive tests at a single object.
-/

open Lean Meta Elab Tactic

namespace KAT.Tactic

/-- The core of the `kat` tactic. -/
def katCore (fuel : ℕ) : TacticM Unit := focus do
  liftMetaTactic fun goal ↦ do return [(← goal.intros).2]
  RelationAlgebra.IterationTactic.expand
  if (← getGoals).isEmpty then return
  evalTactic (← `(tactic| try simp only [KAT.ifThenElse, KAT.whileDo, KAT.HoareTriple,
    TypedKAT.ifThenElse, TypedKAT.whileDo, TypedKAT.HoareTriple, sdiff_eq, himp_eq]))
  -- only the original goal is in scope here (`focus`); the preprocessing may have closed it
  if (← getGoals).isEmpty then return
  let goal ← getMainGoal
  goal.withContext do
    let goalType ← instantiateMVars (← goal.getType)
    let (isLe, K, lhs, rhs) ← match (← whnfR goalType).getAppFnArgs with
      | (``Eq, #[K, a, b]) => pure (false, K, a, b)
      | (``LE.le, #[K, _, a, b]) => pure (true, K, a, b)
      | _ => throwError "kat: the goal must be an equality or an inequality"
    if let some hom ← TypedKAT.Tactic.homType? K then
      TypedKAT.Tactic.closeGoal goal goalType hom lhs rhs isLe fuel
      return
    let some v := (← getLevel K).dec
      | throwError "kat: unexpected universe level for {K}"
    let instKA ← try synthInstance (mkApp (mkConst ``KleeneAlgebra [v]) K)
      catch _ => throwError
        "kat: {K} is not a Kleene algebra (`KleeneAlgebra {K}` not found)"
    let T := (findTestType lhs).getD ((findTestType rhs).getD (mkConst ``Bool))
    let some u := (← getLevel T).dec
      | throwError "kat: unexpected universe level for {T}"
    let instBA ← try synthInstance (mkApp (mkConst ``BooleanAlgebra [u]) T)
      catch _ => throwError "kat: {T} is not a Boolean algebra"
    let katType := mkAppN (mkConst ``KleeneAlgebraWithTests [u, v]) #[T, K, instBA, instKA]
    let instKAT ← try synthInstance katType
      catch _ => throwError "kat: no `KleeneAlgebraWithTests {T} {K}` instance found"
    let ((te, tf), st) ← (do
      let te ← reifyK lhs
      let tf ← reifyK rhs
      return (te, tf)).run {}
    let topT ← mkAppOptM ``Top.top #[T, none]
    let zeroK ← mkAppOptM ``Zero.zero #[K, none]
    let listT ← mkListLit T st.tests.toList
    let listK ← mkListLit K st.acts.toList
    let τ := mkLambda `i .default (mkConst ``Nat)
      (mkApp4 (mkConst ``List.getD [u]) T listT (.bvar 0) topT)
    let ρ := mkLambda `i .default (mkConst ``Nat)
      (mkApp4 (mkConst ``List.getD [v]) K listK (.bvar 0) zeroK)
    let kE := mkNatLit st.tests.size
    let fuelE := mkNatLit fuel
    let boolEq (p : Expr) : Expr :=
      mkApp3 (mkConst ``Eq [Level.one]) (mkConst ``Bool) p (mkConst ``Bool.true)
    let reflTrue := mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true)
    let he ← mkExpectedTypeHint reflTrue
      (boolEq (mkApp2 (mkConst ``KAT.KTerm.tvarsBelow) kE te))
    let hf ← mkExpectedTypeHint reflTrue
      (boolEq (mkApp2 (mkConst ``KAT.KTerm.tvarsBelow) kE tf))
    let decName := if isLe then ``KAT.KTerm.decideLe else ``KAT.KTerm.decideEq
    let prop := mkApp4 (mkConst decName) kE te tf fuelE
    unless (← kernelIsTrue prop) do
      throwError "kat: the goal is not a valid KAT (in)equation, or the fuel ({fuel}) ran out\
        \n(tests: {st.tests}, actions: {st.acts})"
    let h ← mkExpectedTypeHint reflTrue (boolEq prop)
    let thmName := if isLe then ``KAT.Completeness.eval_le_of_decideLe
      else ``KAT.Completeness.eval_eq_of_decideEq
    let pf := mkAppN (mkConst thmName [u, v])
      #[T, K, instBA, instKA, instKAT, τ, ρ, kE, te, tf, fuelE, he, hf, h]
    let pfType ← inferType pf
    unless ← isDefEq pfType goalType do
      throwError "kat: failed to reify the goal{indentExpr goalType}\nas{indentExpr pfType}"
    goal.assign pf

/-- `kat` decides equalities and inequalities that hold in every Kleene algebra with tests, by
reflection into guarded-string automata. Supports both `KleeneAlgebra` carriers and morphisms
in a `KleeneCategory`, with Boolean tests at each object.
`kat n` uses `n` units of fuel (default `1000`). -/
syntax (name := kat) "kat" (ppSpace num)? : tactic

elab_rules : tactic
  | `(tactic| kat $[$n]?) => katCore (n.map (·.getNat) |>.getD 1000)

end KAT.Tactic
