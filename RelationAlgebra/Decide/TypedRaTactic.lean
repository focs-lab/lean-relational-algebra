import RelationAlgebra.TypedRA.Untyping
import RelationAlgebra.Decide.KATReify
import RelationAlgebra.Decide.TypedKATEnvironment

/-!
# Typed structural normalization

Reify categorical operations with their endpoints, normalize the erasures using `RaTerm`,
and reconstruct proofs through converse untyping. Normal-form readback solves endpoint
constraints before building an indexed expression. Every reconstructed proof is checked
against the original goal by definitional equality and subsequently by Lean's kernel.
-/

open Lean Meta Elab Tactic CategoryTheory

namespace TypedRA.Tactic

/-- A temporary tree, before the complete action environment is known. -/
private inductive Tree where
  | zero (source target : ℕ)
  | one (object : ℕ)
  | act (index : ℕ)
  | add (left right : Tree)
  | comp (left right : Tree)
  | star (body : Tree)
  | conv (body : Tree)

/-- A primitive morphism and its object indices. -/
structure Action where
  source : ℕ
  target : ℕ
  value : Expr
  deriving Inhabited

/-- Objects and actions collected from the goal. -/
private structure State where
  objects : Array Expr := #[]
  actions : Array Action := #[]

private abbrev ReifyM := StateRefT State MetaM

/-- Recognise a hom type without unfolding the category's hom-set implementation. -/
def homType? (type : Expr) : MetaM (Option Expr) := do
  let type := type.consumeMData
  if type.isAppOfArity ``Quiver.Hom 4 then return some type
  withReducible (whnfUntil type ``Quiver.Hom)

private def addObject (e : Expr) : ReifyM ℕ := do
  let s ← get
  if let some i ← KAT.Tactic.findAtom s.objects e then return i
  set { s with objects := s.objects.push e }
  return s.objects.size

private def addAction (e : Expr) (source target : ℕ) : ReifyM Tree := do
  let s ← get
  for i in [:s.actions.size] do
    let a := s.actions[i]!
    if a.source == source && a.target == target && (← withReducible (isDefEq a.value e)) then
      return .act i
  set { s with actions := s.actions.push ⟨source, target, e⟩ }
  return .act s.actions.size

/-- Pass endpoints from the goal and composition nodes, rather than inferring them from
an atom's concrete implementation type (which need not be written as `Quiver.Hom`). -/
private partial def reify (source target : ℕ) (e : Expr) : ReifyM Tree := do
  let e := e.consumeMData
  match e.getAppFnArgs with
  | (``CategoryStruct.comp, #[_, _, _, Y, _, a, b]) =>
    let middle ← addObject Y
    return .comp (← reify source middle a) (← reify middle target b)
  | (``CategoryStruct.id, #[_, _, _]) => return .one source
  | (``Max.max, #[_, _, a, b]) =>
    return .add (← reify source target a) (← reify source target b)
  | (``Bot.bot, #[_, _]) => return .zero source target
  | (``KStar.kstar, #[_, _, a]) => return .star (← reify source target a)
  | (``KleeneCategoryWithConverse.converse, #[_, _, _, _, _, _, a]) =>
    return .conv (← reify target source a)
  | _ => addAction e source target

/-- Build the indexed syntax after all action endpoints have been collected. -/
private def Tree.toExpr (src tgt : Expr) : Tree → MetaM Expr
  | .zero X Y => mkAppOptM ``Term.zero #[mkConst ``Nat, src, tgt, mkNatLit X, mkNatLit Y]
  | .one X => mkAppOptM ``Term.one #[mkConst ``Nat, src, tgt, mkNatLit X]
  | .act a => mkAppOptM ``Term.act #[mkConst ``Nat, src, tgt, mkNatLit a]
  | .add e f => do
    mkAppM ``Term.add #[← e.toExpr src tgt, ← f.toExpr src tgt]
  | .comp e f => do
    mkAppM ``Term.comp #[← e.toExpr src tgt, ← f.toExpr src tgt]
  | .star e => do
    mkAppM ``Term.star #[← e.toExpr src tgt]
  | .conv e => do
    mkAppM ``Term.conv #[← e.toExpr src tgt]

/-- A list lookup with a default, as a function on natural numbers. -/
private def listEnv (type : Expr) (entries : Array Expr) (default : Expr) : MetaM Expr := do
  let list ← mkListLit type entries.toList
  withLocalDeclD `i (mkConst ``Nat) fun i => do
    mkLambdaFVars #[i] (← mkAppM ``List.getD #[list, i, default])

/-- The dependent environments and reified sides of one categorical goal. -/
private structure GoalData where
  C : Expr
  cat : Expr
  kc : Expr
  cnv : Expr
  obj : Expr
  src : Expr
  tgt : Expr
  values : Expr
  state : State
  left : Expr
  right : Expr

private def reifyGoal (hom lhs rhs : Expr) : MetaM GoalData := do
  let C := hom.getArg! 0
  let some u := (← getLevel C).dec | throwError "ra: invalid object universe"
  let some v := (← getLevel hom).dec | throwError "ra: invalid morphism universe"
  let cat ← synthInstance (mkApp (mkConst ``Category [v, u]) C)
  let kc ← synthInstance (← mkAppOptM ``KleeneCategory #[C, cat])
  let cnv ← try synthInstance (← mkAppOptM ``KleeneCategoryWithConverse #[C, cat, kc])
    catch _ => throwError "ra: the category {C} needs a `KleeneCategoryWithConverse` instance"
  let ((left, right), s) ← (do
    let source ← addObject (hom.getArg! 2)
    let target ← addObject (hom.getArg! 3)
    return (← reify source target lhs, ← reify source target rhs)).run {}
  let obj ← listEnv C s.objects s.objects[0]!
  let actionType ← mkAppM ``TypedKAT.Reflection.Action #[obj]
  let entries ← s.actions.mapM fun a =>
    mkAppOptM ``TypedKAT.Reflection.Action.mk
      #[C, cat, obj, mkNatLit a.source, mkNatLit a.target, a.value]
  let catStruct ← mkAppOptM ``Category.toCategoryStruct #[C, cat]
  let identity ← mkAppOptM ``CategoryStruct.id #[C, catStruct, s.objects[0]!]
  let default ← mkAppOptM ``TypedKAT.Reflection.Action.mk
    #[C, cat, obj, mkNatLit 0, mkNatLit 0, identity]
  let actions ← listEnv actionType entries default
  let project (name : Name) := withLocalDeclD `i (mkConst ``Nat) fun i => do
    mkLambdaFVars #[i] (← mkAppM name #[mkApp actions i])
  let src ← project ``TypedKAT.Reflection.Action.source
  let tgt ← project ``TypedKAT.Reflection.Action.target
  let values ← project ``TypedKAT.Reflection.Action.value
  let left ← left.toExpr src tgt
  let right ← right.toExpr src tgt
  return { C, cat, kc, cnv, obj, src, tgt, values, state := s, left, right }

private def kernelIsTrue (p : Expr) : MetaM Bool := do
  match Kernel.whnf (← getEnv) (← getLCtx) p with
  | .ok r => return r.isConstOf ``Bool.true
  | .error _ => return false

private def certify (p : Expr) : MetaM Expr := do
  unless ← kernelIsTrue p do
    throwError "ra: the goal does not follow from structural normalization"
  mkExpectedTypeHint (← mkEqRefl (mkConst ``Bool.true)) (← mkEq p (mkConst ``Bool.true))

private def checkAssign (goal : MVarId) (goalType proof : Expr) : MetaM Unit := do
  unless ← isDefEq (← inferType proof) goalType do
    throwError "ra: typed proof reconstruction did not match the goal{indentExpr goalType}"
  goal.assign proof

/-- Close a categorical equality or inequality by the existing structural checker. -/
def closeGoal (goal : MVarId) (goalType hom lhs rhs : Expr) (isLe : Bool) : MetaM Unit := do
  let g ← reifyGoal hom lhs rhs
  let e ← mkAppM ``Term.erase #[g.left]
  let f ← mkAppM ``Term.erase #[g.right]
  let test := mkApp2 (mkConst (if isLe then ``RaTerm.normLe else ``RaTerm.normEq)) e f
  let cert ← certify test
  let theoremName := if isLe then ``Term.eval_le_of_normLe else ``Term.eval_eq_of_normEq
  let proof ← mkAppOptM theoremName
    #[none, g.src, g.tgt, none, none, g.C, g.cat, g.kc, g.cnv,
      g.obj, g.values, g.left, g.right, cert]
  checkAssign goal goalType proof

/-- Retype an erased normal form, solving the intermediate object constraints.
Zero is polymorphic, and identity forces equal endpoints. -/
private partial def readback (g : GoalData) (X Y term : Expr) : MetaM Expr := do
  let base := #[some (mkConst ``Nat), some g.src, some g.tgt]
  let same (a b : Expr) := do
    unless ← isDefEq a b do throwError "ra: normal-form readback has incompatible endpoints"
  match term.getAppFnArgs with
  | (``RaTerm.zero, _) => mkAppOptM ``Term.zero (base ++ #[some X, some Y])
  | (``RaTerm.one, _) =>
    same X Y
    mkAppOptM ``Term.one (base ++ #[some X])
  | (``RaTerm.var, #[n]) =>
    same X (mkApp g.src n)
    same Y (mkApp g.tgt n)
    mkAppOptM ``Term.act (base ++ #[some n])
  | (``RaTerm.add, #[a, b]) =>
    mkAppM ``Term.add #[← readback g X Y a, ← readback g X Y b]
  | (``RaTerm.mul, #[a, b]) =>
    let Z ← mkFreshExprMVar (mkConst ``Nat)
    let a' ← readback g X Z a
    let b' ← readback g Z Y b
    if Z.isMVar then
      unless ← Z.mvarId!.isAssigned do Z.mvarId!.assign (mkNatLit 0)
    mkAppM ``Term.comp #[a', b']
  | (``RaTerm.star, #[a]) =>
    same X Y
    mkAppM ``Term.star #[← readback g X X a]
  | (``RaTerm.conv, #[a]) => mkAppM ``Term.conv #[← readback g Y X a]
  | _ => throwError "ra: unexpected normal form{indentExpr term}"

/-- Display operations on the original objects and atoms, without exposing list environments. -/
private partial def denote (g : GoalData) (term : Expr) : MetaM Expr := do
  let term ← instantiateMVars term
  let args := term.getAppArgs
  let atObject (i : Expr) := do
    let some n ← (Meta.evalNat (← Meta.reduce i)).run | throwError "ra: nonconstant object index"
    let some X := g.state.objects[n]? | throwError "ra: unknown object {n}"
    pure X
  let hom (X Y : Expr) := mkAppM ``Quiver.Hom #[X, Y]
  let catStruct ← mkAppOptM ``Category.toCategoryStruct #[g.C, g.cat]
  match term.getAppFn.constName? with
  | some ``Term.zero =>
    mkAppOptM ``Bot.bot #[← hom (← atObject args[3]!) (← atObject args[4]!), none]
  | some ``Term.one => mkAppOptM ``CategoryStruct.id #[g.C, catStruct, ← atObject args[3]!]
  | some ``Term.act =>
    let some n ← (Meta.evalNat (← Meta.reduce args[3]!)).run
      | throwError "ra: nonconstant action index"
    let some a := g.state.actions[n]? | throwError "ra: unknown action {n}"
    return a.value
  | some ``Term.add =>
    mkAppOptM ``Max.max #[← hom (← atObject args[3]!) (← atObject args[4]!), none,
      ← denote g args[5]!, ← denote g args[6]!]
  | some ``Term.comp =>
    mkAppOptM ``CategoryStruct.comp #[g.C, catStruct, ← atObject args[3]!,
      ← atObject args[4]!, ← atObject args[5]!, ← denote g args[6]!, ← denote g args[7]!]
  | some ``Term.star =>
    mkAppOptM ``KStar.kstar #[← hom (← atObject args[3]!) (← atObject args[3]!), none,
      ← denote g args[4]!]
  | some ``Term.conv =>
    mkAppOptM ``KleeneCategoryWithConverse.converse #[g.C, g.cat, g.kc, g.cnv,
      ← atObject args[3]!, ← atObject args[4]!, ← denote g args[5]!]
  | _ => throwError "ra: unexpected typed normal form{indentExpr term}"

/-- Normalize both sides, leaving a readable categorical goal when it is not closed. -/
def rewriteGoal (goal : MVarId) (goalType hom lhs rhs : Expr) (isLe : Bool)
    (fn : Name) : MetaM MVarId := do
  let g ← reifyGoal hom lhs rhs
  let transform (t side : Expr) := do
    let erased ← mkAppM ``Term.erase #[t]
    let nf ← Meta.reduce (mkApp (mkConst fn) erased)
    let type ← inferType t
    let X := type.getAppArgs[3]!
    let Y := type.getAppArgs[4]!
    let typed ← instantiateMVars (← readback g X Y nf)
    let value ← denote g typed
    let erased' ← mkAppM ``Term.erase #[typed]
    let expected ← mkEq erased' (mkApp (mkConst fn) erased)
    let cert ← mkExpectedTypeHint (← mkEqRefl erased') expected
    let theoremName := if fn == ``RaTerm.norm then ``Term.eval_eq_of_erase_norm
      else ``Term.eval_eq_of_erase_simplify
    let proof ← mkAppOptM theoremName
      #[none, g.src, g.tgt, none, none, g.C, g.cat, g.kc, g.cnv,
        g.obj, g.values, t, typed, cert]
    let eq ← mkEq value side
    unless ← isDefEq (← inferType proof) eq do
      throwError "ra: typed normalization did not reconstruct the original expression"
    return (value, ← mkExpectedTypeHint proof eq)
  let (lhs', hl) ← transform g.left lhs
  let (rhs', hr) ← transform g.right rhs
  let newType ← if isLe then mkAppM ``LE.le #[lhs', rhs'] else mkEq lhs' rhs'
  let next ← mkFreshExprSyntheticOpaqueMVar newType
  let proof ← if isLe then
      mkAppM ``Eq.trans_le #[← mkAppM ``Eq.symm #[hl], ← mkAppM ``LE.le.trans_eq #[next, hr]]
    else mkAppM ``Eq.trans #[← mkAppM ``Eq.trans #[← mkAppM ``Eq.symm #[hl], next], hr]
  checkAssign goal goalType proof
  return next.mvarId!

end TypedRA.Tactic
