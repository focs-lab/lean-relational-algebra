import RelationAlgebra.Decide.GuardedString

/-!
# Shared reification helpers for KAT tactics

Boolean expression reification, atom lookup, and kernel evaluation shared by the typed
and untyped tactic implementations. Unrecognised Boolean expressions become primitive tests.
-/

open Lean Meta

namespace KAT.Tactic

/-- Atoms collected during reification: primitive tests (in `T`) and actions (in `K`). -/
structure State where
  /-- The primitive tests. -/
  tests : Array Expr := #[]
  /-- The primitive actions. -/
  acts : Array Expr := #[]

/-- The reification monad. -/
abbrev KatM := StateRefT State MetaM

/-- Index of `e` in `arr` up to reducible defeq, or `none`. -/
def findAtom (arr : Array Expr) (e : Expr) : MetaM (Option ℕ) := do
  for h : i in [:arr.size] do
    if ← withReducible (isDefEq e arr[i]) then return some i
  return none

/-- Register a primitive test. -/
def addTest (e : Expr) : KatM ℕ := do
  let s ← get
  match ← findAtom s.tests e with
  | some i => return i
  | none =>
    set { s with tests := s.tests.push e }
    return s.tests.size

/-- Register a primitive action. -/
def addAct (e : Expr) : KatM ℕ := do
  let s ← get
  match ← findAtom s.acts e with
  | some i => return i
  | none =>
    set { s with acts := s.acts.push e }
    return s.acts.size

/-- Reify a Boolean-algebra expression into a `KAT.BTerm`. -/
partial def reifyB (e : Expr) : KatM Expr := do
  let e := e.consumeMData
  match e.getAppFnArgs with
  | (``Max.max, #[_, _, a, b]) =>
    return mkApp2 (mkConst ``KAT.BTerm.or) (← reifyB a) (← reifyB b)
  | (``Min.min, #[_, _, a, b]) =>
    return mkApp2 (mkConst ``KAT.BTerm.and) (← reifyB a) (← reifyB b)
  | (``Compl.compl, #[_, _, a]) => return mkApp (mkConst ``KAT.BTerm.not) (← reifyB a)
  | (``Top.top, #[_, _]) => return mkConst ``KAT.BTerm.top
  | (``Bot.bot, #[_, _]) => return mkConst ``KAT.BTerm.bot
  | _ => return mkApp (mkConst ``KAT.BTerm.tvar) (mkNatLit (← addTest e))

/-- Reify a KAT expression into a `KAT.KTerm`. -/
partial def reifyK (e : Expr) : KatM Expr := do
  let e := e.consumeMData
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) =>
    return mkApp2 (mkConst ``KAT.KTerm.add) (← reifyK a) (← reifyK b)
  | (``HMul.hMul, #[_, _, _, _, a, b]) =>
    return mkApp2 (mkConst ``KAT.KTerm.mul) (← reifyK a) (← reifyK b)
  | (``KStar.kstar, #[_, _, a]) => return mkApp (mkConst ``KAT.KTerm.star) (← reifyK a)
  | (``KleeneAlgebraWithTests.test, #[_, _, _, _, _, b]) =>
    return mkApp (mkConst ``KAT.KTerm.test) (← reifyB b)
  | (``OfNat.ofNat, #[_, n, _]) =>
    match n.rawNatLit? with
    | some 0 => return mkConst ``KAT.KTerm.zero
    | some 1 => return mkConst ``KAT.KTerm.one
    | _ => return mkApp (mkConst ``KAT.KTerm.act) (mkNatLit (← addAct e))
  | (``Zero.zero, #[_, _]) => return mkConst ``KAT.KTerm.zero
  | (``One.one, #[_, _]) => return mkConst ``KAT.KTerm.one
  | _ => return mkApp (mkConst ``KAT.KTerm.act) (mkNatLit (← addAct e))

/-- The type of tests occurring in an expression, if any. -/
def findTestType (e : Expr) : Option Expr :=
  (e.find? fun x ↦ x.isAppOfArity ``KleeneAlgebraWithTests.test 6).map (·.getArg! 0)

/-- Evaluate a closed `Bool` expression with the kernel and test whether it is `true`. -/
def kernelIsTrue (p : Expr) : MetaM Bool := do
  match Kernel.whnf (← getEnv) (← getLCtx) p with
  | .ok r => return r.isConstOf ``Bool.true
  | .error _ => return false

end KAT.Tactic
