import RelationAlgebra.Decide.Normalise
import RelationAlgebra.Decide.TypedRaTactic
import RelationAlgebra.Decide.FullRATactic
import Mathlib.Util.AtomM

/-!
# The `ra`, `ra_normalise` and `ra_simpl` tactics

These tactics follow Damien Pous' `theories/normalisation.v` in
[`relation-algebra`](https://github.com/damien-pous/relation-algebra).

* `ra` normalizes both sides of an equality or inequality and attempts to close it.
  Failure does not imply the statement is false.
* `ra_normalise` performs the same normalization and leaves any unresolved goal.
* `ra_simpl` performs lighter cleanup without distributing composition or sorting
  joins and meets. It leaves any unresolved goal.

For KA with converse, the tactics reflect into `RaTerm`, using the correctness theorems
in `Decide.Normalise`. Untyped goals require `[KleeneAlgebra K] [StarRing K]`; categorical
goals use `[Category C] [KleeneCategory C] [KleeneCategoryWithConverse C]`. The typed
reifier retains endpoints and transports proofs through
`TypedRA.Term.eval_eq_of_erase_eval_eq`.

Goals containing intersection, complement, top, Boolean difference/implication, or
residuals instead use `Decide.FullRATactic`. This extension recursively applies proved
rewrites, including KA operations under Boolean and residual operations, and a bounded
structural inclusion checker. Rules cover lattice order, variance, residual adjunctions
and cancellation, and Dedekind/modular inequalities. Each rule requires its corresponding
algebraic instance; residual-only goals need neither Boolean operations nor converse.
`RelationAlgebra` and the typed `RelationCategory` hierarchy supply the full operations.

The two proof paths are kernel checked. Neither canonicity nor completeness of `ra` is
asserted. The Boolean/residual path does not extend `RaTerm` or invoke its KA-only untyping
theorem on richer syntax. Its limits are 16 normalization passes and 4096 structural rule
attempts. All three tactics introduce leading binders, focus on the original goal, and
ignore local hypotheses. For deeper KA/KAT iteration identities, use `ka` or `kat`; their
search is also fuel bounded, with no proved search completeness.

## References

* [D. Pous, *relation-algebra*, `theories/normalisation.v`](https://github.com/damien-pous/relation-algebra)
-/

open Lean Meta Elab Tactic Mathlib.Tactic

namespace RelationAlgebra.Tactic

/-- Register `e` as an atom and return the corresponding `RaTerm.var`. -/
def atom (e : Expr) : AtomM Expr := do
  let (i, _) ← AtomM.addAtom e
  return mkApp (mkConst ``RaTerm.var) (mkNatLit i)

/-- Reify an expression of a Kleene algebra with converse into a `RaTerm`, collecting the
maximal non-algebraic subterms as atoms. -/
partial def reify (e : Expr) : AtomM Expr := do
  let e := e.consumeMData
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) =>
    return mkApp2 (mkConst ``RaTerm.add) (← reify a) (← reify b)
  | (``HMul.hMul, #[_, _, _, _, a, b]) =>
    return mkApp2 (mkConst ``RaTerm.mul) (← reify a) (← reify b)
  | (``KStar.kstar, #[_, _, a]) =>
    return mkApp (mkConst ``RaTerm.star) (← reify a)
  | (``Star.star, #[_, _, a]) =>
    return mkApp (mkConst ``RaTerm.conv) (← reify a)
  | (``OfNat.ofNat, #[_, n, _]) =>
    match n.rawNatLit? with
    | some 0 => return mkConst ``RaTerm.zero
    | some 1 => return mkConst ``RaTerm.one
    | _ => atom e
  | (``Zero.zero, #[_, _]) => return mkConst ``RaTerm.zero
  | (``One.one, #[_, _]) => return mkConst ``RaTerm.one
  | _ => atom e

/-- Read a closed `RaTerm` expression back as an expression of `K`, interpreting `RaTerm.var
i` as the `i`-th atom. -/
partial def denote (tac : String) (K : Expr) (atoms : Array Expr) (e : Expr) : MetaM Expr := do
  match e.getAppFnArgs with
  | (``RaTerm.zero, _) => mkAppOptM ``Zero.zero #[K, none]
  | (``RaTerm.one, _) => mkAppOptM ``One.one #[K, none]
  | (``RaTerm.var, #[i]) =>
    let some n := i.nat? <|> (← (Meta.evalNat i).run)
      | throwError "{tac}: unexpected variable index{indentExpr i}"
    let some a := atoms[n]? | throwError "{tac}: unknown atom index {n}"
    return a
  | (``RaTerm.add, #[a, b]) =>
    mkAppM ``HAdd.hAdd #[← denote tac K atoms a, ← denote tac K atoms b]
  | (``RaTerm.mul, #[a, b]) =>
    mkAppM ``HMul.hMul #[← denote tac K atoms a, ← denote tac K atoms b]
  | (``RaTerm.star, #[a]) => mkAppM ``KStar.kstar #[← denote tac K atoms a]
  | (``RaTerm.conv, #[a]) => mkAppM ``Star.star #[← denote tac K atoms a]
  | _ => throwError "{tac}: cannot read back the normal form{indentExpr e}"

/-- The reified form of a goal: whether it is an inequality, the carrier, the two reified
sides, the valuation and the atoms. -/
structure ReifiedGoal where
  /-- `true` for a `≤` goal, `false` for an `=` goal. -/
  isLe : Bool
  /-- The carrier type of the algebra. -/
  K : Expr
  /-- The left-hand side of the goal. -/
  lhs : Expr
  /-- The right-hand side of the goal. -/
  rhs : Expr
  /-- The reified left-hand side, a closed `RaTerm`. -/
  lhsTerm : Expr
  /-- The reified right-hand side, a closed `RaTerm`. -/
  rhsTerm : Expr
  /-- The valuation sending a variable index to the corresponding atom. -/
  valuation : Expr
  /-- The atoms collected during reification. -/
  atoms : Array Expr

/-- Reify the goal `goalType`, checking that its carrier is a Kleene algebra with converse. -/
def reifyGoal (tac : String) (goalType : Expr) : MetaM ReifiedGoal := do
  let (isLe, K, lhs, rhs) ← match (← whnfR goalType).getAppFnArgs with
    | (``Eq, #[K, a, b]) => pure (false, K, a, b)
    | (``LE.le, #[K, _, a, b]) => pure (true, K, a, b)
    | _ => throwError "{tac}: the goal must be an equality or an inequality"
  let some u := (← getLevel K).dec
    | throwError "{tac}: unexpected universe level for {K}"
  let kaType := mkApp (mkConst ``KleeneAlgebra [u]) K
  unless (← synthInstance? kaType).isSome do
    throwError "{tac}: {K} is not a Kleene algebra (`KleeneAlgebra {K}` not found)"
  let semiring ← match ← synthInstance? (mkApp (mkConst ``NonUnitalNonAssocSemiring [u]) K) with
    | some inst => pure inst
    | none => throwError "{tac}: {K} is not a semiring"
  let starType := mkApp2 (mkConst ``StarRing [u]) K semiring
  unless (← synthInstance? starType).isSome do
    throwError "{tac}: {K} has no converse (`StarRing {K}` not found); a `RelationAlgebra \
      {K}` instance provides one"
  let (lhsTerm, rhsTerm, atoms) ← AtomM.run .reducible do
    let lhsTerm ← reify lhs
    let rhsTerm ← reify rhs
    return (lhsTerm, rhsTerm, (← get).atoms)
  let zeroK ← mkAppOptM ``Zero.zero #[K, none]
  let listK ← mkListLit K atoms.toList
  let valuation := mkLambda `i .default (mkConst ``Nat)
    (mkApp4 (mkConst ``List.getD [u]) K listK (.bvar 0) zeroK)
  return { isLe, K, lhs, rhs, lhsTerm, rhsTerm, valuation, atoms }

/-- Compute the normal form of a reified term and read it back as an expression of `K`. -/
def normalForm (tac : String) (fn : Name) (g : ReifiedGoal) (e : Expr) : MetaM (Expr × Expr) := do
  let nf ← Meta.reduce (mkApp (mkConst fn) e)
  return (nf, ← denote tac g.K g.atoms nf)

/-- Evaluate a closed `Bool` expression with the kernel and test whether it is `true`. -/
def kernelIsTrue (p : Expr) : MetaM Bool := do
  match Kernel.whnf (← getEnv) (← getLCtx) p with
  | .ok r => return r.isConstOf ``Bool.true
  | .error _ => return false

/-- Replace both sides of the goal by the value of `fn` on them, justified by `lemm`
(`RaTerm.eval_norm` or `RaTerm.eval_simplify`), and leave the transformed goal.  If the two
sides become identical, the goal is closed by reflexivity. -/
def rewriteBoth (tac : String) (fn lemm : Name) : TacticM Unit := focus do
  liftMetaTactic fun goal ↦ do return [(← goal.intros).2]
  let extended ← withMainContext do
    let target ← whnfR (← instantiateMVars (← (← getMainGoal).getType))
    unless target.isAppOfArity ``Eq 3 || target.isAppOfArity ``LE.le 4 do
      throwError "ra: the goal must be an equality or an inequality"
    let scalar := (← TypedRA.Tactic.homType? target.getAppArgs[0]!).isNone
    pure (FullRA.hasOperations target scalar)
  if extended then
    FullRA.normalize (fn == ``RaTerm.simplify)
    unless (← getGoals).isEmpty do
      if fn == ``RaTerm.norm then discard FullRA.close
    return
  let goal ← getMainGoal
  goal.withContext do
    let goalType ← instantiateMVars (← goal.getType)
    let (isLe, K, lhs, rhs) ← match (← whnfR goalType).getAppFnArgs with
      | (``Eq, #[K, a, b]) => pure (false, K, a, b)
      | (``LE.le, #[K, _, a, b]) => pure (true, K, a, b)
      | _ => throwError "{tac}: the goal must be an equality or an inequality"
    if let some hom ← TypedRA.Tactic.homType? K then
      let next ← TypedRA.Tactic.rewriteGoal goal goalType hom lhs rhs isLe fn
      replaceMainGoal [next]
      if isLe then
        try evalTactic (← `(tactic| exact le_rfl)) catch _ => pure ()
      else
        try evalTactic (← `(tactic| rfl)) catch _ => pure ()
      return
    let g ← reifyGoal tac goalType
    let (_, lhs') ← normalForm tac fn g g.lhsTerm
    let (_, rhs') ← normalForm tac fn g g.rhsTerm
    -- `hl : lhs' = lhs` and `hr : rhs' = rhs`, by correctness of the normalisation
    let mkHyp (t side normalised : Expr) : MetaM Expr := do
      let h ← mkAppM lemm #[g.valuation, t]
      let expected ← mkEq normalised side
      unless ← isDefEq (← inferType h) expected do
        throwError "{tac}: failed to reify{indentExpr side}"
      mkExpectedTypeHint h expected
    let hl ← mkHyp g.lhsTerm g.lhs lhs'
    let hr ← mkHyp g.rhsTerm g.rhs rhs'
    let newType ← if g.isLe then mkAppM ``LE.le #[lhs', rhs'] else mkEq lhs' rhs'
    let newGoal ← mkFreshExprSyntheticOpaqueMVar newType
    let proof ← if g.isLe then
        mkAppM ``Eq.trans_le #[← mkAppM ``Eq.symm #[hl], ← mkAppM ``LE.le.trans_eq #[newGoal, hr]]
      else
        mkAppM ``Eq.trans #[← mkAppM ``Eq.trans #[← mkAppM ``Eq.symm #[hl], newGoal], hr]
    unless ← isDefEq (← inferType proof) goalType do
      throwError "{tac}: failed to transform the goal{indentExpr goalType}"
    goal.assign proof
    replaceMainGoal [newGoal.mvarId!]
    -- the normalised goal may already be closed by reflexivity
    if g.isLe then
      try evalTactic (← `(tactic| exact le_rfl)) catch _ => pure ()
    else
      try evalTactic (← `(tactic| rfl)) catch _ => pure ()

/-- Close by reflected KA normalization or the Boolean/residual structural checker. -/
def raCore : TacticM Unit := focus do
  liftMetaTactic fun goal ↦ do return [(← goal.intros).2]
  let extended ← withMainContext do
    let target ← whnfR (← instantiateMVars (← (← getMainGoal).getType))
    unless target.isAppOfArity ``Eq 3 || target.isAppOfArity ``LE.le 4 do
      throwError "ra: the goal must be an equality or an inequality"
    let scalar := (← TypedRA.Tactic.homType? target.getAppArgs[0]!).isNone
    pure (FullRA.hasOperations target scalar)
  if extended then
    FullRA.normalize false
    if (← getGoals).isEmpty then return
    if ← FullRA.close then return
    throwError "ra: structural Boolean/residual normalization and bounded inclusion checking \
      did not close the goal"
  let goal ← getMainGoal
  goal.withContext do
    let goalType ← instantiateMVars (← goal.getType)
    let (isLe, K, lhs, rhs) ← match (← whnfR goalType).getAppFnArgs with
      | (``Eq, #[K, a, b]) => pure (false, K, a, b)
      | (``LE.le, #[K, _, a, b]) => pure (true, K, a, b)
      | _ => throwError "ra: the goal must be an equality or an inequality"
    if let some hom ← TypedRA.Tactic.homType? K then
      TypedRA.Tactic.closeGoal goal goalType hom lhs rhs isLe
      return
    let g ← reifyGoal "ra" goalType
    let test := mkApp2 (mkConst (if g.isLe then ``RaTerm.normLe else ``RaTerm.normEq))
      g.lhsTerm g.rhsTerm
    unless ← kernelIsTrue test do
      let (_, lhs') ← normalForm "ra" ``RaTerm.norm g g.lhsTerm
      let (_, rhs') ← normalForm "ra" ``RaTerm.norm g g.rhsTerm
      throwError "ra: the goal does not follow from the structural laws of relation \
        algebra.\nnormal form of the left-hand side:{indentExpr lhs'}\nnormal form of the \
        right-hand side:{indentExpr rhs'}"
    let cert ← mkExpectedTypeHint
      (mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true))
      (mkApp3 (mkConst ``Eq [Level.one]) (mkConst ``Bool) test (mkConst ``Bool.true))
    let thm := if g.isLe then ``RaTerm.eval_le_of_normLe' else ``RaTerm.eval_eq_of_normEq'
    let proof ← mkAppM thm #[cert, g.valuation]
    unless ← isDefEq (← inferType proof) goalType do
      throwError "ra: failed to reify the goal{indentExpr goalType}"
    goal.assign proof

/-- `ra` proves structural equalities and inequalities involving KA operations, converse,
Boolean operations and residuals. It produces kernel-checked proofs and is incomplete. -/
syntax (name := ra) "ra" : tactic

elab_rules : tactic
  | `(tactic| ra) => raCore

/-- `ra_normalise` normalizes both sides of an `=` or `≤` goal and attempts structural
inclusion checking. It leaves any unresolved goal for further proof. -/
syntax (name := ra_normalise) "ra_normalise" : tactic

elab_rules : tactic
  | `(tactic| ra_normalise) => rewriteBoth "ra_normalise" ``RaTerm.norm ``RaTerm.eval_norm

/-- `ra_simpl` cleans up both sides of an `=` or `≤` goal: units, zeros, basic star laws,
converse, Boolean simplification and residual units, without sorting or distribution. -/
syntax (name := ra_simpl) "ra_simpl" : tactic

elab_rules : tactic
  | `(tactic| ra_simpl) => rewriteBoth "ra_simpl" ``RaTerm.simplify ``RaTerm.eval_simplify

end RelationAlgebra.Tactic

/-! ### Regression tests -/

section Tests

open scoped Computability

section Abstract

variable {K : Type*} [KleeneAlgebra K] [StarRing K] (a b c : K)

example : star (a * b) = star b * star a := by ra

example : (a + b) * c = a * c + b * c := by ra

example : star (a∗) = (star a)∗ := by ra

example : 1 * a * 1 = a := by ra

example : 0 * a + b = b := by ra

example : a + (b + a) = b + a := by ra

example : star (star a) = a := by ra

example : (0 : K)∗ = 1 := by ra

example : a∗∗ = a∗ := by ra

example : star ((a + b)∗) = (star b + star a)∗ := by ra

example : a * (b + c) * 1 = a * b + a * c := by ra

example : a ≤ a + b := by ra

example : a * (1 + 0) ≤ b + a := by ra

-- `ra` cannot prove this (it needs a Kleene-star axiom), but `ra_normalise` simplifies it.
example : 1 * (a∗ * a) * 1 + 0 = a * a∗ := by
  ra_normalise
  exact KleeneAlgebra.kstar_mul_comm a

-- `ra_simpl` does not sort sums, so it leaves a goal here.
example : (a + b) * 1 ≤ b + a := by
  ra_simpl
  exact le_of_eq (add_comm a b)

-- `ra_simpl` closes the goal when the cleaned-up sides agree.
example : star (1 * a * (b + 0)) = star b * star a := by ra_simpl

-- other goals are left untouched: `ra` runs under `focus`, so the second goal survives.
-- The unfocused `ra` is the point of this test, hence the disabled linter.
set_option linter.style.multiGoal false in
example : 1 * a = a ∧ True := by
  constructor
  ra
  trivial

end Abstract

section Relational

open scoped SetRel

variable {α : Type*} (R S : SetRel α α)

example : star (R * S) = star S * star R := by ra

example : 1 * R * 1 = R := by ra

example : 0 * R + S = S := by ra

example : star (R∗) = (star R)∗ := by ra

example : (R + S) * R = R * R + S * R := by ra

example : R ≤ R + S := by ra

end Relational

section Abstract

variable {K : Type*} [RelationAlgebra K] (a b : K)

-- an abstract relation algebra provides the converse through `RelationAlgebra.toStarRing`
example : star (a * b) * 1 = star b * star a := by ra

-- Boolean operations are normalized by the proved-rewrite extension.
example : (a ⊓ b) * 1 + 0 = a ⊓ b := by ra

end Abstract

end Tests
