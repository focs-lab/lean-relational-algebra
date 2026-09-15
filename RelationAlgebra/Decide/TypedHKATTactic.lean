import RelationAlgebra.Decide.HKATCommon
import RelationAlgebra.Decide.KATTactic
import RelationAlgebra.TypedKAT.Hypotheses

/-!
# Hypothesis elimination for typed `hkat`

Hypotheses in different hom-sets cannot be joined directly. We collect the finite graph
of primitive actions and use state elimination to construct path expressions `U X Y`.
A zero hypothesis `z : A ⟶ B` contributes `U X A ≫ z ≫ U B Y` to a goal in `X ⟶ Y`.
Each contribution is proved zero, and `kat` checks the remaining unconditional goal.

Path construction is metaprogramming, not a trusted algorithm: its output is checked for
typing and its only use in the proof is through `TypedKAT.context_le_bot`. No completeness
of this elimination strategy or of the fuel-bounded search is asserted.
-/

open Lean Meta Elab Tactic CategoryTheory

namespace TypedKAT.Tactic

private def conversions : Array Name :=
  #[``TypedKAT.hoareTriple_to_hoare, ``TypedKAT.le_bot_to_hoare,
    ``TypedKAT.eq_bot_to_hoare, ``TypedKAT.test_eq_to_hoare, ``TypedKAT.test_le_to_hoare,
    ``TypedKAT.test_comp_le_to_hoare, ``TypedKAT.comp_test_le_to_hoare,
    ``TypedKAT.le_test_comp_to_hoare, ``TypedKAT.le_comp_test_to_hoare]

private def rewrites : Array Name :=
  #[``TypedKAT.test_comp_eq_to_hoare, ``TypedKAT.comp_test_eq_to_hoare]

/-- Read only categorical equations and inequalities in the goal's category. -/
private def relation? (C type : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let (carrier, lhs, rhs) ← match (← whnfR (← instantiateMVars type)).getAppFnArgs with
    | (``Eq, #[K, a, b]) => pure (K, a, b)
    | (``LE.le, #[K, _, a, b]) => pure (K, a, b)
    | _ => return none
  let some hom ← homType? carrier | return none
  unless ← withReducible (isDefEq C (hom.getArg! 0)) do return none
  return some (hom, lhs, rhs)

private def toHoare (C instCat instKC : Expr) (families : Array Expr) (K h : Expr) :
    MetaM (Option Expr) := do
  for lem in conversions do
    if lem == ``TypedKAT.test_eq_to_hoare || lem == ``TypedKAT.test_le_to_hoare then
      -- A raw Boolean value does not determine a dependent family (e.g. a constant one).
      for T in families do
        if let some e ← KAT.Tactic.tryConversion lem K h #[C, instCat, instKC, T] then
          return some e
    if let some e ← KAT.Tactic.tryConversion lem K h then return some e
  return none

private def rewriteHyps (C : Expr) (facts : Array LocalDecl) : TacticM (Array FVarId) := do
  let mut used := #[]
  for decl in facts do
    let some (hom, _, _) ← withMainContext (relation? C decl.type) | continue
    for lem in rewrites do
      let some eq ← withMainContext (KAT.Tactic.tryConversion lem hom decl.toExpr) | continue
      let progress ← withMainContext do
        try
          let goal ← getMainGoal
          let r ← goal.rewrite (← goal.getType) eq
          replaceMainGoal ((← goal.replaceTargetEq r.eNew r.eqProof) :: r.mvarIds)
          return true
        catch _ => return false
      if progress then
        used := used.push decl.fvarId
        break
  return used

/-- State elimination over expressions. `none` represents a zero entry. Eliminating
an object stars its diagonal and extends the incoming and outgoing paths through it. -/
private def paths (C instCat : Expr) (objects : Array Expr) (actions : Array Action) :
    MetaM (Array (Array (Option Expr))) := do
  let n := objects.size
  let mut matrix : Array (Array (Option Expr)) := Array.replicate n (Array.replicate n none)
  let instStruct ← mkAppOptM ``Category.toCategoryStruct #[C, instCat]
  let instQuiver ← mkAppOptM ``CategoryStruct.toQuiver #[C, instStruct]
  let hom (i j : ℕ) := mkAppOptM ``Quiver.Hom #[C, instQuiver, objects[i]!, objects[j]!]
  let join (i j : ℕ) (a : Option Expr) (b : Expr) : MetaM Expr := do
    match a with
    | none => return b
    | some a =>
      if a == b then return a
      mkAppOptM ``Max.max #[← hom i j, none, a, b]
  let comp (i k j : ℕ) (a b : Expr) : MetaM Expr := do
    if a.isAppOf ``CategoryStruct.id then return b
    if b.isAppOf ``CategoryStruct.id then return a
    mkAppOptM ``CategoryStruct.comp
      #[C, instStruct, objects[i]!, objects[k]!, objects[j]!, a, b]
  for a in actions do
    let e ← join a.source a.target (matrix[a.source]!)[a.target]! a.value
    matrix := matrix.modify a.source (·.set! a.target (some e))
  for k in [:n] do
    let old := matrix
    let loop ← match (old[k]!)[k]! with
      | none => mkAppOptM ``CategoryStruct.id #[C, instStruct, objects[k]!]
      | some e => mkAppOptM ``KStar.kstar #[← hom k k, none, e]
    matrix := matrix.modify k (·.set! k (some loop))
    for i in [:n] do
      if i == k then continue
      let some left := ((old[i]!)[k]!) | continue
      let left ← comp i k k left loop
      matrix := matrix.modify i (·.set! k (some left))
      for j in [:n] do
        if j == k then continue
        let some right := ((old[k]!)[j]!) | continue
        let through ← comp i k j left right
        let e ← join i j (old[i]!)[j]! through
        matrix := matrix.modify i (·.set! j (some e))
    for j in [:n] do
      if j == k then continue
      let some right := ((old[k]!)[j]!) | continue
      let e ← comp k k j loop right
      matrix := matrix.modify k (·.set! j (some e))
  return matrix

/-- The categorical branch of `hkat`; the caller has introduced binders and focused the goal. -/
def hkatCore (hom : Expr) (fuel : ℕ) : TacticM Unit := do
  -- Normalize commands and Boolean connectives in hypotheses too, before extracting actions.
  evalTactic (← `(tactic| try simp only [TypedKAT.ifThenElse, TypedKAT.whileDo,
    TypedKAT.HoareTriple, sdiff_eq, himp_eq] at *))
  if (← getGoals).isEmpty then return
  let C := hom.getArg! 0
  let facts ← KAT.Tactic.localFacts
  let rewritten ← rewriteHyps C facts
  withMainContext do
    let goal ← getMainGoal
    let goalType ← instantiateMVars (← goal.getType)
    let some (goalHom, lhs, rhs) ← relation? C goalType
      | throwError "hkat: expected a categorical equality or inequality"
    let isLe := (← whnfR goalType).isAppOf ``LE.le
    let X := goalHom.getArg! 2
    let Y := goalHom.getArg! 3
    let mut terms := #[(X, Y, lhs), (X, Y, rhs)]
    for decl in facts do
      if let some (K, a, b) ← relation? C decl.type then
        terms := terms.push (K.getArg! 2, K.getArg! 3, a)
        terms := terms.push (K.getArg! 2, K.getArg! 3, b)
    let mut families := #[]
    for (_, _, e) in terms do
      if let some test := e.find? (·.isAppOfArity ``KleeneCategoryWithTests.test 8) then
        let T := test.getArg! 3
        if (← KAT.Tactic.findAtom families T).isNone then families := families.push T
    -- A test-free goal may still use Boolean facts through a local typed KAT instance.
    for decl in ← getLCtx do
      let type ← whnfR decl.type
      if type.isAppOfArity ``KleeneCategoryWithTests 5 then
        if ← withReducible (isDefEq (type.getArg! 0) C) then
          let T := type.getArg! 3
          if (← KAT.Tactic.findAtom families T).isNone then families := families.push T
    let (objects, _) ← actionGraph terms
    let some u := (← getLevel C).dec | throwError "hkat: unexpected object universe"
    let some v := (← getLevel goalHom).dec | throwError "hkat: unexpected morphism universe"
    let instCat ← synthInstance (mkApp (mkConst ``Category [v, u]) C)
    let instKC ← try synthInstance (← mkAppOptM ``KleeneCategory #[C, instCat])
      catch _ => throwError "hkat: the category {C} needs a `KleeneCategory` instance"
    let instStruct ← mkAppOptM ``Category.toCategoryStruct #[C, instCat]
    let instQuiver ← mkAppOptM ``CategoryStruct.toQuiver #[C, instStruct]
    -- A concrete constructor can expose the implementation of a hom-set in its type.
    -- Try the known endpoints too; conversion still requires definitional equality.
    let homs := objects.flatMap fun X => objects.map fun Y =>
      mkApp4 (mkConst ``Quiver.Hom [v, u]) C instQuiver X Y
    let mut hyps := #[]
    for decl in facts do
      if rewritten.contains decl.fvarId then continue
      let carriers ← match ← relation? C decl.type with
        | some (K, _, _) => pure #[K]
        | none => pure homs
      -- A constant test family can use the same Boolean fact at several objects.
      -- Keep each well-typed conversion rather than choosing one arbitrary object.
      for K in carriers do
        if let some h ← toHoare C instCat instKC families K decl.toExpr then
          hyps := hyps.push h
          continue
        unless (← whnfR decl.type).isAppOf ``Eq do continue
        let some hle ← observing? (mkAppM ``le_of_eq #[decl.toExpr]) | continue
        let some hge ← observing? (do mkAppM ``le_of_eq #[← mkAppM ``Eq.symm #[decl.toExpr]])
          | continue
        for h in #[hle, hge] do
          if let some hz ← toHoare C instCat instKC families K h then hyps := hyps.push hz
    if hyps.isEmpty then
      if rewritten.isEmpty then
        throwError "hkat: no usable typed hypothesis found; use `kat` for a goal without hypotheses"
    else
      -- Keep only the goal and converted hypotheses in the action graph.
      terms := #[(X, Y, lhs), (X, Y, rhs)]
      for h in hyps do
        let some (K, z, _) ← relation? C (← inferType h)
          | throwError "hkat: invalid typed Hoare conversion"
        terms := terms.push (K.getArg! 2, K.getArg! 3, z)
      let (objects, actions) ← actionGraph terms
      let matrix ← paths C instCat objects actions
      let some source ← KAT.Tactic.findAtom objects X | throwError "hkat: missing source"
      let some target ← KAT.Tactic.findAtom objects Y | throwError "hkat: missing target"
      let mut aggregate : Option Expr := none
      for h in hyps do
        let some (K, z, _) ← relation? C (← inferType h)
          | throwError "hkat: invalid typed Hoare conversion"
        let some a ← KAT.Tactic.findAtom objects (K.getArg! 2) | continue
        let some b ← KAT.Tactic.findAtom objects (K.getArg! 3) | continue
        let some left := ((matrix[source]!)[a]!) | continue
        let some right := ((matrix[b]!)[target]!) | continue
        let hz ← mkAppOptM ``TypedKAT.context_le_bot
          #[C, instCat, instKC, X, Y, objects[a]!, objects[b]!, left, right, z, h]
        aggregate ← match aggregate with
          | none => pure (some hz)
          | some old => some <$> mkAppM ``sup_le #[old, hz]
      if let some hz := aggregate then
        let some (_, z, _) ← relation? C (← inferType hz)
          | throwError "hkat: invalid typed zero sum"
        let elim := if isLe then ``TypedKAT.hoare_elim_le else ``TypedKAT.hoare_elim_eq
        replaceMainGoal (← goal.apply (← mkAppM elim #[z, lhs, rhs, hz]))
      else if rewritten.isEmpty then
        throwError "hkat: no hypothesis has action paths connecting it to the goal's endpoints"
  KAT.Tactic.katCore fuel

end TypedKAT.Tactic
