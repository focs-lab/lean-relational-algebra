import RelationAlgebra.Decide.KACompleteness
import Mathlib.Util.AtomM

/-!
# The `ka` tactic

`ka` closes goals of the form `a = b` or `a ≤ b` in **any** Kleene algebra whose two sides
denote the same regular language when the maximal non-Kleene-algebraic subterms are read as
variables.  It applies to an abstract `[KleeneAlgebra K]`, as well as to concrete models such as
relations `SetRel α α` (after `open scoped SetRel`), languages `Language α`, and matrices over
any of these.

It works by reflection:

1. the two sides are reified into `KleeneAlgebra.Term`s, atoms being collected with `AtomM`;
2. `KleeneAlgebra.Term.decideEq` (Antimirov partial derivatives + bisimulation) is run by the
   kernel on the two terms, producing a certificate `decideEq e f fuel = true`;
3. `KleeneAlgebra.Term.eval_eq_of_decideEq'` turns the certificate into the desired equation,
   whose sides are definitionally the original ones.  That step rests on **Kozen's completeness
   theorem** (`KleeneAlgebra.Term.completeness_eq`, proved in
   `RelationAlgebra.Decide.KACompleteness`), which is what makes the tactic sound for an
   arbitrary Kleene algebra rather than only a star-continuous one.

Use `ka 5000` to change the amount of fuel (default `1000`) for the exploration.

This is the counterpart of the `ka` tactic of Pous' `relation-algebra` library.

Two guarantees must not be confused.  *Soundness when the checker accepts* is proved: an
accepted certificate yields the equation in every Kleene algebra.  *Completeness of the search*
is not: the exploration is fuel-bounded, so a failure means either an invalid equation or
exhausted fuel.
-/

open Lean Meta Elab Tactic Mathlib.Tactic

namespace KleeneAlgebra.Tactic

/-- Register `e` as an atom and return the corresponding `Term.var`. -/
def atom (e : Expr) : AtomM Expr := do
  let (i, _) ← AtomM.addAtom e
  return mkApp (mkConst ``KleeneAlgebra.Term.var) (mkNatLit i)

/-- Reify an expression of a Kleene algebra into a `KleeneAlgebra.Term`, collecting the
maximal non-algebraic subterms as atoms. -/
partial def reify (e : Expr) : AtomM Expr := do
  let e := e.consumeMData
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) =>
    return mkApp2 (mkConst ``KleeneAlgebra.Term.add) (← reify a) (← reify b)
  | (``HMul.hMul, #[_, _, _, _, a, b]) =>
    return mkApp2 (mkConst ``KleeneAlgebra.Term.mul) (← reify a) (← reify b)
  | (``KStar.kstar, #[_, _, a]) =>
    return mkApp (mkConst ``KleeneAlgebra.Term.star) (← reify a)
  | (``OfNat.ofNat, #[_, n, _]) =>
    match n.rawNatLit? with
    | some 0 => return mkConst ``KleeneAlgebra.Term.zero
    | some 1 => return mkConst ``KleeneAlgebra.Term.one
    | _ => atom e
  | (``Zero.zero, #[_, _]) => return mkConst ``KleeneAlgebra.Term.zero
  | (``One.one, #[_, _]) => return mkConst ``KleeneAlgebra.Term.one
  | _ => atom e

/-- Evaluate a closed `Bool` expression with the kernel and test whether it is `true`. -/
def kernelIsTrue (p : Expr) : MetaM Bool := do
  match Kernel.whnf (← getEnv) (← getLCtx) p with
  | .ok r => return r.isConstOf ``Bool.true
  | .error _ => return false

/-- The core of the `ka` tactic. -/
def kaCore (fuel : ℕ) : TacticM Unit := do
  let goal ← getMainGoal
  goal.withContext do
    let goalType ← instantiateMVars (← goal.getType)
    let (isLe, K, lhs, rhs) ← match (← whnfR goalType).getAppFnArgs with
      | (``Eq, #[K, a, b]) => pure (false, K, a, b)
      | (``LE.le, #[K, _, a, b]) => pure (true, K, a, b)
      | _ => throwError "ka: the goal must be an equality or an inequality"
    let some u := (← getLevel K).dec
      | throwError "ka: unexpected universe level for {K}"
    let inst ← try synthInstance (mkApp (mkConst ``KleeneAlgebra [u]) K)
      catch _ => throwError "ka: {K} is not a Kleene algebra (`KleeneAlgebra {K}` not found)"
    let (te, tf, atoms) ← AtomM.run .reducible do
      let te ← reify lhs
      let tf ← reify rhs
      return (te, tf, (← get).atoms)
    -- the valuation `fun i ↦ [a₀, …, aₖ].getD i 0`
    let zeroK ← mkAppOptM ``Zero.zero #[K, none]
    let listK ← mkListLit K atoms.toList
    let ρ := mkLambda `i .default (mkConst ``Nat)
      (mkApp4 (mkConst ``List.getD [u]) K listK (.bvar 0) zeroK)
    let fuelE := mkNatLit fuel
    let decName := if isLe then ``KleeneAlgebra.Term.decideLe else ``KleeneAlgebra.Term.decideEq
    let prop := mkApp3 (mkConst decName) te tf fuelE
    unless (← kernelIsTrue prop) do
      throwError "ka: the goal is not a valid Kleene algebra (in)equation, or the fuel \
        ({fuel}) ran out\n(atoms: {atoms})"
    -- the certificate `decideEq e f fuel = true`, checked by the kernel
    let hDecide ← mkExpectedTypeHint
      (mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true))
      (mkApp3 (mkConst ``Eq [Level.one]) (mkConst ``Bool) prop (mkConst ``Bool.true))
    let thmName := if isLe then ``KleeneAlgebra.Term.eval_le_of_decideLe'
      else ``KleeneAlgebra.Term.eval_eq_of_decideEq'
    let pf := mkAppN (mkConst thmName [u]) #[K, inst, te, tf, fuelE, hDecide, ρ]
    let pfType ← inferType pf
    unless ← isDefEq pfType goalType do
      throwError "ka: failed to reify the goal{indentExpr goalType}\nas{indentExpr pfType}"
    goal.assign pf

/-- `ka` proves equalities and inequalities that hold in every Kleene algebra, by reflection
into regular expressions and Antimirov derivatives, using Kozen's completeness theorem.
`ka n` uses `n` units of fuel for the exploration (default `1000`). -/
syntax (name := ka) "ka" (ppSpace num)? : tactic

elab_rules : tactic
  | `(tactic| ka $[$n]?) => kaCore (n.map (·.getNat) |>.getD 1000)

end KleeneAlgebra.Tactic
