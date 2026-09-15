import RelationAlgebra.Decide.KATTactic
import RelationAlgebra.Decide.HKATCommon
import RelationAlgebra.Decide.TypedHKATTactic
import RelationAlgebra.KAT.Hypotheses

/-!
# The `hkat` tactic

`hkat` closes goals `a = b`, `a ≤ b` and `KAT.HoareTriple b p c` in an *arbitrary* Kleene algebra
with tests, and their typed categorical counterparts, **using the hypotheses of the local
context**, following Hardin and Kozen's
elimination of Hoare hypotheses.  It is the counterpart of the `hkat` tactic of
`theories/kat_tac.v` in Damien Pous' `relation-algebra` library for Rocq/Coq.

## Untyped goals

1. `intros`, then unfold `KAT.ifThenElse`, `KAT.whileDo`, `KAT.HoareTriple`, `\` and `⇨` in the
   goal, exactly as `kat` does.  If this closes the goal, `hkat` stops.
2. Use the hypotheses of the shape `⌜c⌝ * p = ⌜c⌝` or `p * ⌜c⌝ = ⌜c⌝` as *rewriting* rules in
   the goal (`KAT.test_mul_eq_to_hoare`, `KAT.mul_test_eq_to_hoare`).
3. Convert every other usable hypothesis into a *Hoare hypothesis* `z ≤ 0` with the lemmas of
   `RelationAlgebra.KAT.Hypotheses`, and merge them all into a single `z ≤ 0` with
   `KAT.add_le_zero`.  The shapes that are recognised are, in the order in which they are
   tried:

   | hypothesis | lemma |
   | --- | --- |
   | `KAT.HoareTriple b p c` | `KAT.hoareTriple_to_hoare` |
   | `x ≤ 0` | `KAT.le_zero_to_hoare` |
   | `x = 0` | `KAT.eq_zero_to_hoare` |
   | `b = c` (tests) | `KAT.test_eq_to_hoare` |
   | `b ≤ c` (tests) | `KAT.test_le_to_hoare` |
   | `⌜b⌝ * p ≤ q * ⌜c⌝` | `KAT.test_mul_le_to_hoare` |
   | `p * ⌜b⌝ ≤ ⌜c⌝ * q` | `KAT.mul_test_le_to_hoare` |
   | `q ≤ ⌜c⌝ * p` | `KAT.le_test_mul_to_hoare` |
   | `q ≤ p * ⌜c⌝` | `KAT.le_mul_test_to_hoare` |

   An equation `x = y` in the Kleene algebra that matches none of the above is split into the
   two inequalities `x ≤ y` and `y ≤ x`, and both are fed to the table again.
4. Build the *universal expression* `u = (a₁ + ⋯ + aₙ)∗`, where `a₁, …, aₙ` are the actions
   occurring in the goal and in `z` (`u = 1` if there is none), apply `KAT.hoare_elim_eq` or
   `KAT.hoare_elim_le` with `u` for both `u` and `v`, and discharge the remaining
   hypothesis-free goal with `kat`.

## Typed goals

For categorical goals, `hkat` uses the corresponding conversion lemmas in
`TypedKAT/Hypotheses.lean`. Tests at the source and target may belong to different Boolean
algebras in the same test family. The supported shapes above use `⌞b⌟`, `≫`, `⊔`, and `⊥`
in place of their untyped counterparts; the two special rewriting rules are endomorphism
rules. Commands and Boolean connectives are normalized in the hypotheses as well.

Instead of joining hypotheses from incompatible hom-sets, it builds path expressions from
the finite graph of actions in the goal and the converted hypotheses. For a goal in
`X ⟶ Y`, a zero hypothesis `z : A ⟶ B` contributes `U X A ≫ z ≫ U B Y`, proved zero by
`TypedKAT.context_le_bot`. These contributions can be joined in `X ⟶ Y`; typed `kat`
checks the resulting unconditional equality or inequality. See `Decide/TypedHKATTactic.lean`.

`hkat n` passes `n` units of fuel to `kat` (default `1000`).  `hkat` acts on the main goal
only; the other goals are left untouched.

## Limitations

* `hkat` inherits the requirements of `kat`: the carrier must be a `KleeneAlgebra`
  (this is checked, with a dedicated error message) carrying a `KleeneAlgebraWithTests`
  instance. Typed goals instead need `[Category C] [KleeneCategory C]` and, when tests
  occur, a single `[TypedKAT C T]` test family with `[∀ X, BooleanAlgebra (T X)]`.
  Search is fuel-bounded; typed path construction can make the checked expressions larger.
* Step 4 is *sound* — that is all that is used here, see `RelationAlgebra.KAT.Hypotheses`.  Its
  *completeness* is the Hardin–Kozen theorem, which is **not** formalised in this development.
  Completeness of the typed path construction is also not proved:
  a failure of `hkat` establishes nothing about the goal.
* If no hypothesis can be used at all, `hkat` fails with an error rather than silently
  behaving like `kat`.  (If step 2 rewrote the goal but produced no Hoare hypothesis, `hkat`
  does continue, with `kat` on the rewritten goal.)

## References

* [C. Hardin and D. Kozen, *On the elimination of hypotheses in Kleene algebra with tests*,
  TR2002-1879, Computer Science Department, Cornell University, October 2002][hardinkozen2002]
* `theories/kat_tac.v` of [`relation-algebra`](https://github.com/damien-pous/relation-algebra)
  by Damien Pous, whose hypothesis conversions and untyped elimination this tactic ports.
-/

open Lean Meta Elab Tactic

namespace KAT.Tactic

/-- The lemmas turning a hypothesis into a Hoare hypothesis `_ ≤ 0`, in the order in which
`hkat` tries them.  Each of them takes the hypothesis as its last argument. -/
def hoareConversions : Array Name :=
  #[``KAT.hoareTriple_to_hoare, ``KAT.le_zero_to_hoare, ``KAT.eq_zero_to_hoare,
    ``KAT.test_eq_to_hoare, ``KAT.test_le_to_hoare, ``KAT.test_mul_le_to_hoare,
    ``KAT.mul_test_le_to_hoare, ``KAT.le_test_mul_to_hoare, ``KAT.le_mul_test_to_hoare]

/-- The lemmas turning a hypothesis into a rewriting rule.  Each of them takes the hypothesis
as its last argument. -/
def rewriteConversions : Array Name :=
  #[``KAT.test_mul_eq_to_hoare, ``KAT.mul_test_eq_to_hoare]

/-- Try every lemma of `hoareConversions` on the fact `h`, and return the first Hoare
hypothesis obtained, if any. -/
def toHoare (K : Expr) (h : Expr) : MetaM (Option Expr) := do
  for lem in hoareConversions do
    if let some e ← tryConversion lem K h then return some e
  return none

/-- Use the hypotheses of the shape `⌜c⌝ * p = ⌜c⌝` and `p * ⌜c⌝ = ⌜c⌝` as rewriting rules in
the goal.  Returns the hypotheses that were used this way; they are not used again as Hoare
hypotheses, as in Pous' `aggregate_hoare_hypotheses`. -/
def rewriteHyps (K : Expr) (facts : Array LocalDecl) : TacticM (Array FVarId) := do
  let mut used := #[]
  for decl in facts do
    for lem in rewriteConversions do
      let some eq ← withMainContext (tryConversion lem K decl.toExpr) | continue
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

/-- Collect the Hoare hypotheses derived from the local context.  An equation that is not
directly convertible is split into its two inequalities, and both are tried. -/
def collectHoareHyps (K : Expr) (facts : Array LocalDecl) (skip : Array FVarId) :
    TacticM (Array Expr) := withMainContext do
  let mut res := #[]
  for decl in facts do
    if skip.contains decl.fvarId then continue
    let h := decl.toExpr
    if let some e ← toHoare K h then
      res := res.push e
      continue
    unless (← instantiateMVars decl.type).isAppOf ``Eq do continue
    let some hle ← observing? (mkAppM ``le_of_eq #[h]) | continue
    let some hge ← observing? (do mkAppM ``le_of_eq #[← mkAppM ``Eq.symm #[h]]) | continue
    for d in #[hle, hge] do
      if let some e ← toHoare K d then res := res.push e
  return res

/-- The universal expression `(a₁ + ⋯ + aₙ)∗` built from the actions of the expressions `es`,
or `1` when no action occurs in them. -/
def universalExpr (K : Expr) (es : Array Expr) : MetaM Expr := do
  let (_, st) ← (es.forM fun e ↦ do let _ ← reifyK e).run {}
  if st.acts.isEmpty then
    return (← mkAppOptM ``One.one #[K, none])
  let mut sum := st.acts[0]!
  for i in [1:st.acts.size] do
    sum ← mkAppM ``HAdd.hAdd #[sum, st.acts[i]!]
  mkAppM ``KStar.kstar #[sum]

/-- The core of the `hkat` tactic. -/
def hkatCore (fuel : ℕ) : TacticM Unit := focus do
  liftMetaTactic fun goal ↦ do return [(← goal.intros).2]
  evalTactic (← `(tactic| try simp only [KAT.ifThenElse, KAT.whileDo, KAT.HoareTriple,
    TypedKAT.ifThenElse, TypedKAT.whileDo, TypedKAT.HoareTriple, sdiff_eq, himp_eq]))
  -- only the original goal is in scope here (`focus`); the preprocessing may have closed it
  if (← getGoals).isEmpty then return
  -- Everything below reads the goal's local context, which `intros` has just extended, so it
  -- must run inside that context: `K` and the hypotheses are free variables of it.
  let K ← withMainContext do
    let K ← match (← whnfR (← instantiateMVars (← getMainTarget))).getAppFnArgs with
      | (``Eq, #[K, _, _]) => pure K
      | (``LE.le, #[K, _, _, _]) => pure K
      | _ => throwError "hkat: the goal must be an equality or an inequality"
    pure K
  if let some hom ← withMainContext (TypedKAT.Tactic.homType? K) then
    TypedKAT.Tactic.hkatCore hom fuel
    return
  withMainContext do
    let some v := (← getLevel K).dec
      | throwError "hkat: unexpected universe level for {K}"
    try
      let _ ← synthInstance (mkApp (mkConst ``KleeneAlgebra [v]) K)
    catch _ =>
      throwError "hkat: {K} is not a Kleene algebra (`KleeneAlgebra {K}` not found)"
  let facts ← localFacts
  let rewritten ← rewriteHyps K facts
  let hyps ← collectHoareHyps K facts rewritten
  if hyps.isEmpty then
    if rewritten.isEmpty then
      throwError "hkat: no usable hypothesis found in the context\
        \n(`hkat` needs a hypothesis it can turn into a Hoare hypothesis `z ≤ 0`; use `kat` \
        for a goal that needs no hypothesis)"
  else
    withMainContext do
      let mut hz := hyps[0]!
      for i in [1:hyps.size] do
        hz ← mkAppM ``KAT.add_le_zero #[hz, hyps[i]!]
      let goal ← getMainGoal
      let goalType ← instantiateMVars (← goal.getType)
      let (isLe, lhs, rhs) ← match (← whnfR goalType).getAppFnArgs with
        | (``Eq, #[_, a, b]) => pure (false, a, b)
        | (``LE.le, #[_, _, a, b]) => pure (true, a, b)
        | _ => throwError "hkat: the goal must be an equality or an inequality"
      let some z := (← whnfR (← instantiateMVars (← inferType hz))).getAppFnArgs.2[2]?
        | throwError "hkat: could not read the merged Hoare hypothesis"
      let u ← universalExpr K #[lhs, rhs, z]
      let elim := if isLe then ``KAT.hoare_elim_le else ``KAT.hoare_elim_eq
      let goals ← goal.apply (← mkAppM elim #[u, u, z, lhs, rhs, hz])
      replaceMainGoal goals
  katCore fuel

/-- `hkat` proves equalities, inequalities and Hoare triples in arbitrary untyped or typed
Kleene algebras with tests *under the hypotheses of the local context*, by eliminating Hoare
hypotheses à la
Hardin–Kozen and calling `kat`.  `hkat n` uses `n` units of fuel (default `1000`). -/
syntax (name := hkat) "hkat" (ppSpace num)? : tactic

elab_rules : tactic
  | `(tactic| hkat $[$n]?) => hkatCore (n.map (·.getNat) |>.getD 1000)

end KAT.Tactic

/-! ## Regression tests -/

section Tests

open scoped Computability SetRel KAT

variable {α : Type*} {b c : Set α} {p q : SetRel α α}

/-- A test commuting with an action commutes with its iteration: false without the
hypothesis. -/
example (h : ⌜b⌝ * p ≤ p * ⌜b⌝) : (⌜b⌝ : SetRel α α) * p∗ ≤ p∗ * ⌜b⌝ := by hkat

/-- The same, from an equation: `hkat` splits it into two inequalities. -/
example (h : (⌜b⌝ : SetRel α α) * p = p * ⌜b⌝) : (⌜b⌝ : SetRel α α) * p∗ = p∗ * ⌜b⌝ := by hkat

/-- The Hoare rule for iteration, derived from a `KAT.HoareTriple` hypothesis. -/
example (h : KAT.HoareTriple b p b) : KAT.HoareTriple b (p∗) b := by hkat

/-- A `KAT.HoareTriple` hypothesis in inequational form. -/
example (h : KAT.HoareTriple b p c) : (⌜b⌝ : SetRel α α) * p ≤ p * ⌜c⌝ := by hkat

/-- A hypothesis of the shape `x ≤ 0`. -/
example (h : p ≤ 0) : p * q = 0 := by hkat

/-- A hypothesis of the shape `x = 0`. -/
example (h : p * q = 0) : q∗ * (p * q) * p∗ = 0 := by hkat

/-- Two hypotheses, merged by `KAT.add_le_zero`. -/
example (h₁ : ⌜b⌝ * p ≤ p * ⌜b⌝) (h₂ : p * q ≤ (0 : SetRel α α)) :
    (⌜b⌝ : SetRel α α) * p∗ * q ≤ p∗ * ⌜b⌝ * q := by hkat

/-- An inclusion between tests. -/
example (h : b ≤ c) : (⌜b⌝ : SetRel α α) * p ≤ ⌜c⌝ * p := by hkat

/-- An equation between tests. -/
example (h : b = c) : (⌜b⌝ : SetRel α α) * p = ⌜c⌝ * p := by hkat

/-- A commutation hypothesis in the other direction. -/
example (h : p * ⌜b⌝ ≤ ⌜c⌝ * q) : (⌜cᶜ⌝ : SetRel α α) * p * ⌜b⌝ = 0 := by hkat

/-- A hypothesis `q ≤ p * ⌜c⌝`. -/
example (h : q ≤ p * ⌜c⌝) : q * ⌜cᶜ⌝ = 0 := by hkat

/-- A hypothesis `q ≤ ⌜c⌝ * p`. -/
example (h : q ≤ ⌜c⌝ * p) : (⌜cᶜ⌝ : SetRel α α) * q = 0 := by hkat

/-- A hypothesis `⌜c⌝ * p = ⌜c⌝` is used as a rewriting rule, not as a Hoare hypothesis. -/
example (h : (⌜c⌝ : SetRel α α) * p = ⌜c⌝) : (⌜c⌝ : SetRel α α) * p * ⌜c⌝ = ⌜c⌝ := by hkat

/-- The mirror rewriting rule, from `p * ⌜c⌝ = ⌜c⌝`. -/
example (h : p * ⌜c⌝ = (⌜c⌝ : SetRel α α)) : (⌜cᶜ⌝ : SetRel α α) * p * ⌜c⌝ = 0 := by hkat

/-- A loop whose guard is falsified by the body is executed at most once (Kozen–Patron style).
The goal is not provable without the hypothesis, as the `fail_if_success` records. -/
example (h : ⌜b⌝ * p ≤ p * ⌜bᶜ⌝) : KAT.whileDo b p = KAT.ifThenElse b p 1 := by
  fail_if_success kat
  hkat

/-! ### Binders introduced by `hkat` itself

`hkat` starts with `intros`, so the carrier, its instances, the actions and the hypotheses may
all be introduced by the tactic rather than already present.  Everything the tactic then does
has to run in the *extended* local context; these regressions pin that down. -/

/-- The actions and both hypotheses are introduced by `hkat`. -/
example {K : Type} [KleeneAlgebra K] :
    ∀ p q : K, p ≤ 0 → q ≤ 0 → p + q = 0 := by hkat

/-- The carrier, its instance, the actions and the hypotheses are all introduced by `hkat`. -/
example : ∀ (K : Type) (_ : KleeneAlgebra K) (p q : K), p ≤ 0 → q ≤ 0 → p * q = 0 := by
  hkat

/-- The same with an instance-implicit binder. -/
example : ∀ (K : Type) [_inst : KleeneAlgebra K] (p : K), p ≤ 0 → p * p = 0 := by hkat

/-- Tests, actions and a commutation hypothesis, all introduced by `hkat`. -/
example {β : Type} : ∀ (b : Set β) (p : SetRel β β),
    ⌜b⌝ * p ≤ p * ⌜b⌝ → (⌜b⌝ : SetRel β β) * p∗ ≤ p∗ * ⌜b⌝ := by hkat

/-- Three introduced hypotheses, merged by `KAT.add_le_zero` in the extended context. -/
example {β : Type} : ∀ (p q r : SetRel β β), p ≤ 0 → q ≤ 0 → r ≤ 0 → p + q + r = 0 := by hkat

/-- A mix: one hypothesis already in the context, one introduced by `hkat`. -/
example {β : Type} (p : SetRel β β) (h₁ : p ≤ 0) :
    ∀ q : SetRel β β, q ≤ 0 → p + q = 0 := by hkat

-- `hkat` acts on the main goal only; other goals are left alone.
set_option linter.style.multiGoal false in
example (h : p ≤ 0) : p * q = 0 ∧ True := by
  constructor
  hkat
  trivial

end Tests
