import RelationAlgebra.Decide.KATReify
import RelationAlgebra.Decide.TypedKATEnvironment
import RelationAlgebra.TypedKATCompleteness.Main

/-!
# Reification of typed KAT goals

The categorical branch of `kat` records objects, action endpoints, and Boolean tests at
each object. It builds a `TypedKAT.Term` and a dependent valuation whose evaluation reduces
to the original goal. The existing guarded-string checker works on the erased terms;
typed completeness reconstructs the categorical proof.

Unrecognised morphisms and Boolean expressions are treated as atoms. The reconstructed
proof must have a type definitionally equal to the goal; Lean's kernel checks the proof.
-/

open Lean Meta Elab Tactic CategoryTheory

namespace TypedKAT.Tactic

/-- A temporary tree, before the complete action environment is known. -/
private inductive Tree where
  | zero (source target : ℕ)
  | one (object : ℕ)
  | test (object : ℕ) (body : Expr)
  | act (index : ℕ)
  | add (left right : Tree)
  | comp (left right : Tree)
  | star (body : Tree)

/-- A primitive morphism and its object indices. -/
structure Action where
  source : ℕ
  target : ℕ
  value : Expr

/-- Primitive tests are indexed separately at each object. -/
private structure State where
  objects : Array Expr := #[]
  tests : Array (Array Expr) := #[]
  actions : Array Action := #[]
  testFamily : Option Expr := none
  collectActionsOnly : Bool := false

private abbrev ReifyM := StateRefT State MetaM

/-- Recognise a hom type without unfolding the category's hom-set implementation. -/
def homType? (type : Expr) : MetaM (Option Expr) := do
  let type := type.consumeMData
  if type.isAppOfArity ``Quiver.Hom 4 then return some type
  withReducible (whnfUntil type ``Quiver.Hom)

private def addObject (e : Expr) : ReifyM ℕ := do
  let s ← get
  if let some i ← KAT.Tactic.findAtom s.objects e then return i
  set { s with objects := s.objects.push e, tests := s.tests.push #[] }
  return s.objects.size

private def addAction (e : Expr) (source target : ℕ) : ReifyM Tree := do
  let s ← get
  if let some i ← KAT.Tactic.findAtom (s.actions.map (·.value)) e then return .act i
  set { s with actions := s.actions.push ⟨source, target, e⟩ }
  return .act s.actions.size

private def reifyTest (object : ℕ) (family body : Expr) : ReifyM Tree := do
  let s ← get
  -- Universal paths ignore guards; no Boolean environment is needed in collection mode.
  if s.collectActionsOnly then return .one object
  if let some T := s.testFamily then
    unless ← withReducible (isDefEq T family) do
      throwError "kat: typed tests must belong to one test family over the category"
  let (b, bs) ← (KAT.Tactic.reifyB body).run { tests := s.tests[object]! }
  set { s with tests := s.tests.set! object bs.tests, testFamily := some family }
  return .test object b

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
  | (``KleeneCategoryWithTests.test, #[_, _, _, T, _, _, _, b]) => reifyTest source T b
  | _ => addAction e source target

/-- Collect the objects and primitive actions of expressions with their expected endpoints.
This shares `kat`'s atom recognition with the typed hypothesis-elimination tactic. -/
def actionGraph (terms : Array (Expr × Expr × Expr)) : MetaM (Array Expr × Array Action) := do
  let (_, s) ← (terms.forM fun (X, Y, e) => do
    let source ← addObject X
    let target ← addObject Y
    let _ ← reify source target e).run { collectActionsOnly := true }
  return (s.objects, s.actions)

/-- Build the indexed syntax after all action endpoints have been collected. -/
private def Tree.toExpr (src tgt : Expr) : Tree → MetaM Expr
  | .zero X Y => mkAppOptM ``Term.zero #[mkConst ``Nat, src, tgt, mkNatLit X, mkNatLit Y]
  | .one X => mkAppOptM ``Term.one #[mkConst ``Nat, src, tgt, mkNatLit X]
  | .test X b => mkAppOptM ``Term.test #[mkConst ``Nat, src, tgt, mkNatLit X, b]
  | .act a => mkAppOptM ``Term.act #[mkConst ``Nat, src, tgt, mkNatLit a]
  | .add e f => do
    mkAppM ``Term.add #[← e.toExpr src tgt, ← f.toExpr src tgt]
  | .comp e f => do
    mkAppM ``Term.comp #[← e.toExpr src tgt, ← f.toExpr src tgt]
  | .star e => do
    mkAppM ``Term.star #[← e.toExpr src tgt]

/-- A list lookup with a default, as a function on natural numbers. -/
private def listEnv (type : Expr) (entries : Array Expr) (default : Expr) : MetaM Expr := do
  let list ← mkListLit type entries.toList
  withLocalDeclD `i (mkConst ``Nat) fun i => do
    mkLambdaFVars #[i] (← mkAppM ``List.getD #[list, i, default])

/-- Build a test environment whose lookup reduces at each concrete object index. -/
private def testEnv (C T d : Expr) (s : State) : MetaM Expr := do
  let mut env ← mkAppM ``Reflection.nilTests #[T, d]
  let mut xs ← mkListLit C []
  for i in (List.range s.objects.size).reverse do
    let X := s.objects[i]!
    let TX := mkApp T X
    let top ← mkAppOptM ``Top.top #[TX, none]
    let head ← listEnv TX s.tests[i]! top
    env ← mkAppM ``Reflection.consTests #[T, d, X, xs, head, env]
    xs ← mkAppM ``List.cons #[X, xs]
  return env

/-- The typed branch of `kat`, called after the common goal preprocessing. -/
def closeGoal (goal : MVarId) (goalType hom lhs rhs : Expr) (isLe : Bool)
    (fuel : ℕ) : MetaM Unit := do
  let C := hom.getArg! 0
  let some u := (← getLevel C).dec
    | throwError "kat: unexpected object universe for {C}"
  let some v := (← getLevel hom).dec
    | throwError "kat: unexpected morphism universe for {hom}"
  let instCat ← synthInstance (mkApp (mkConst ``Category [v, u]) C)
  let instKC ← try synthInstance (← mkAppOptM ``KleeneCategory #[C, instCat])
    catch _ => throwError "kat: the category {C} needs a `KleeneCategory` instance"
  let ((left, right), s) ← (do
    let source ← addObject (hom.getArg! 2)
    let target ← addObject (hom.getArg! 3)
    let left ← reify source target lhs
    let right ← reify source target rhs
    return (left, right)).run {}
  let d := s.objects[0]!
  let obj ← listEnv C s.objects d
  let T := s.testFamily.getD (mkLambda `X .default C (mkConst ``Bool))
  let instBA ← withLocalDeclD `X C fun X => do
    synthInstance (← mkForallFVars #[X] (← mkAppM ``BooleanAlgebra #[mkApp T X]))
  let instKAT ← try
      synthInstance (← mkAppOptM ``KleeneCategoryWithTests #[C, instCat, instKC, T, instBA])
    catch _ => throwError "kat: no typed KAT instance for the test family {T}"
  let τ ← testEnv C T d s
  let actionType ← mkAppM ``Reflection.Action #[obj]
  let entries ← s.actions.mapM fun a =>
    mkAppOptM ``Reflection.Action.mk
      #[C, instCat, obj, mkNatLit a.source, mkNatLit a.target, a.value]
  let instStruct ← mkAppOptM ``Category.toCategoryStruct #[C, instCat]
  let identity ← mkAppOptM ``CategoryStruct.id #[C, instStruct, mkApp obj (mkNatLit 0)]
  let default ← mkAppOptM ``Reflection.Action.mk
    #[C, instCat, obj, mkNatLit 0, mkNatLit 0, identity]
  let actions ← listEnv actionType entries default
  let project (name : Name) := withLocalDeclD `i (mkConst ``Nat) fun i => do
    mkLambdaFVars #[i] (← mkAppM name #[mkApp actions i])
  let src ← project ``Reflection.Action.source
  let tgt ← project ``Reflection.Action.target
  let ρ ← project ``Reflection.Action.value
  let e ← left.toExpr src tgt
  let f ← right.toExpr src tgt
  let eraseE ← mkAppM ``Term.erase #[e]
  let eraseF ← mkAppM ``Term.erase #[f]
  let k := mkNatLit (s.tests.foldl (fun n tests ↦ max n tests.size) 0)
  let fuelE := mkNatLit fuel
  let boolEq (p : Expr) := mkApp3 (mkConst ``Eq [Level.one]) (mkConst ``Bool) p
    (mkConst ``Bool.true)
  let reflTrue ← mkEqRefl (mkConst ``Bool.true)
  let he ← mkExpectedTypeHint reflTrue (boolEq (← mkAppM ``Term.tvarsBelow #[k, e]))
  let hf ← mkExpectedTypeHint reflTrue (boolEq (← mkAppM ``Term.tvarsBelow #[k, f]))
  let decName := if isLe then ``KAT.KTerm.decideLe else ``KAT.KTerm.decideEq
  let prop := mkApp4 (mkConst decName) k eraseE eraseF fuelE
  unless ← KAT.Tactic.kernelIsTrue prop do
    throwError "kat: the typed goal was not proved (the identity may be invalid, syntax may be \
      unsupported, or the fuel ({fuel}) may have run out)"
  let h ← mkExpectedTypeHint reflTrue (boolEq prop)
  let thmName := if isLe then ``Completeness.eval_le_of_decideLe
    else ``Completeness.eval_eq_of_decideEq
  let pf ← mkAppOptM thmName #[mkConst ``Nat, src, tgt, none, none,
    C, instCat, instKC, T, instBA, instKAT, obj, τ, ρ, e, f, k, fuelE, he, hf, h]
  let pfType ← inferType pf
  unless ← isDefEq pfType goalType do
    throwError "kat: failed to reconstruct the typed goal{indentExpr goalType}\n\
      as{indentExpr pfType}"
  goal.assign pf

end TypedKAT.Tactic
