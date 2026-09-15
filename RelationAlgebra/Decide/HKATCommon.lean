import RelationAlgebra.Decide.KATReify

/-! Shared local-context and lemma-application helpers for the two branches of `hkat`. -/

open Lean Meta Elab Tactic

namespace KAT.Tactic

/-- Apply the conversion lemma `lem` to the fact `h`, which is used as the last argument of
`lem`; all the other arguments are inferred, instance arguments being synthesised.  The
conclusion of `lem` must be an equation or an inequation in the carrier `K`.  Returns `none`
if the lemma does not apply. An optional `fixedArgs` fixes its initial arguments. -/
def tryConversion (lem : Name) (K : Expr) (h : Expr) (fixedArgs : Array Expr := #[]) :
    MetaM (Option Expr) :=
  observing? do
    let info ← getConstInfo lem
    let lvls ← info.levelParams.mapM fun _ ↦ mkFreshLevelMVar
    let f := mkConst lem lvls
    let (args, bis, concl) ← forallMetaTelescope (← inferType f)
    unless 0 < args.size do throwError "no argument"
    unless fixedArgs.size < args.size do throwError "too many fixed arguments"
    for i in [:fixedArgs.size] do
      unless ← isDefEq args[i]! fixedArgs[i]! do throwError "fixed argument mismatch"
    let last := args[args.size - 1]!
    let carrier ← match (← whnfR concl).getAppFnArgs with
      | (``Eq, #[α, _, _]) => pure α
      | (``LE.le, #[α, _, _, _]) => pure α
      | _ => throwError "unexpected conclusion"
    unless ← isDefEq carrier K do throwError "the conclusion is about another carrier"
    -- Fix the carrier first: a concrete morphism may expose its implementation type,
    -- from which elaboration cannot recover the category and endpoints on its own.
    unless ← isDefEq last h do throwError "the hypothesis does not fit"
    for i in [:args.size] do
      if bis[i]!.isInstImplicit && !(← args[i]!.mvarId!.isAssigned) then
        let inst ← synthInstance (← instantiateMVars (← inferType args[i]!))
        unless ← isDefEq args[i]! inst do throwError "instance mismatch"
    let e ← instantiateMVars (mkAppN f args)
    if e.hasExprMVar || e.hasLevelMVar then throwError "underdetermined"
    return e

/-- The proofs in the local context that `hkat` may use. -/
def localFacts : TacticM (Array LocalDecl) := withMainContext do
  let mut res := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    if ← isProp decl.type then res := res.push decl
  return res

end KAT.Tactic
