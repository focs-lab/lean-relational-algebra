# Using the library

[Quick start](../README.md#get-started) · [Contributing](../CONTRIBUTING.md)

## Reading the notation

For relations `R S : SetRel α α` and a test `b : Set α`:

| Expression | Meaning |
| --- | --- |
| `R + S` | Union / nondeterministic choice |
| `R * S` | Sequential composition: first `R`, then `S` |
| `0`, `1` | Empty relation, identity relation |
| `R∗` | Zero or more steps of `R` (reflexive-transitive closure) |
| `R⁺` | One or more steps of `R` (transitive closure) |
| `R ≤ S` | Relation inclusion |
| `⌜b⌝` | Identity restricted to states satisfying `b` |
| `bᶜ` | Negation of the test |
| `star R` | Converse: reverse every pair in `R` |
| `R ⊓ S`, `Rᶜ`, `⊤` | Intersection, relation complement, universal relation |
| `R ⇘ S`, `S ⇙ R` | Left and right residuals; enable `open scoped RelationAlgebra` |

`open scoped Computability` enables `∗` and `⁺`; `KAT` enables `⌜b⌝`; `SetRel` selects the
relational algebra instances. The last scope matters because relations are represented as
sets, which can also carry Mathlib's pointwise operations.

`KAT.ifThenElse b p q` and `KAT.whileDo b p` encode guarded commands.
`KAT.HoareTriple b p c` means **partial correctness**: every terminating execution of `p`
from `b` ends in `c`. It is defined by `⌜b⌝ * p * ⌜cᶜ⌝ = 0`.

## Tactic support

| Tactic | Goals | Operations understood |
| --- | --- | --- |
| `ka` | Equalities and inequalities | `0`, `1`, `+`, `*`, `∗`, `⁺` |
| `kat` | Equalities, inequalities, and `KAT.HoareTriple` | KA operations, embedded Boolean tests, `ifThenElse`, `whileDo` |
| `kat` on typed goals | Equalities, inequalities, and `TypedKAT.HoareTriple` | `⊥`, `𝟙`, `⊔`, `≫`, `∗`, `⁺`, typed tests and guarded commands |
| `hkat` | Untyped or typed goals, using Hoare-style hypotheses from the context | The same operations as `kat` |
| `ra`, `ra_normalise`, `ra_simpl` | Untyped or typed equalities and inequalities | KA operations, converse, `⊓`, `ᶜ`, `⊤`, `\`, `⇨`, and residuals |

`ka` proves identities in any Kleene algebra. `kat` adds Boolean tests and also supports
typed composition. `hkat` adds reasoning from hypotheses at one or several objects.
`ra` normalises expressions and checks structural inclusions.

`ka` requires only `[KleeneAlgebra K]`. It is sound in every Kleene algebra because
**Kozen's completeness theorem** is proved in
[Decide/KACompleteness](../RelationAlgebra/Decide/KACompleteness.lean): regular expressions with
the same language are equal in every Kleene algebra.

For untyped goals, `kat` and `hkat` require `[KleeneAlgebra K]` plus a
`KleeneAlgebraWithTests T K` instance for an arbitrary `[BooleanAlgebra T]`. They are sound in every such algebra because the untyped
**Kozen–Smith completeness theorem** is proved in
[KATCompleteness/Main](../RelationAlgebra/KATCompleteness/Main.lean): terms with the same
guarded-string semantics have the same value in every KAT. Neither completeness of the lattice,
star-continuity, commutativity nor finiteness is assumed. Relations have tests `Set α`;
languages have the trivial tests `Bool`.

**Typed KAT completeness** is also proved in
[TypedKATCompleteness/Main](../RelationAlgebra/TypedKATCompleteness/Main.lean), for arbitrary
categories and object alphabets. `kat` and `hkat` use it to prove categorical goals directly.
They require `[Category C] [KleeneCategory C]` and, when tests occur, `[TypedKAT C T]`
with `[∀ X, BooleanAlgebra (T X)]`. See [typed identities](../RelationAlgebra/Examples/TypedDecide.lean)
and [typed hypothesis examples](../RelationAlgebra/Examples/TypedHypotheses.lean).

For the Kleene-with-converse fragment, `ra` requires `[KleeneAlgebra K] [StarRing K]`,
or `[Category C] [KleeneCategory C] [KleeneCategoryWithConverse C]` for typed goals.
Boolean and residual rules use the corresponding interfaces: `RelationAlgebra K` supplies
all untyped operations; typed relation algebra combines `BooleanKleeneCategory`,
`KleeneCategoryWithConverse`, and `RelationCategory`. Residual-only goals also work with
`ResiduatedKleeneAlgebra` or `ResiduatedKleeneCategory`, without Boolean structure or converse.

`ra_normalise` simplifies both sides and tries structural inclusion rules. `ra_simpl`
performs lighter cleanup without distributing products or sorting joins and meets.
Both leave any remaining goal for further proof. See
[worked examples](../RelationAlgebra/Examples/FullRa.lean).

All six commands accept strict iteration. They expand `a⁺` to `a * a∗` (typed:
`f ≫ f∗`) by proved rewrites before reification. `hkat` expands it in hypotheses too;
the `ra` commands first simplify constants, nested iterations and converse. The checker
syntax and its soundness assumptions are unchanged.

Every successful tactic produces a kernel-checked proof. *Algebraic completeness* is proved for Kleene
algebra and for both untyped and typed KAT. *Search completeness* is proved for none of them.

`ka`, `kat` and `hkat` search for bisimulation certificates using derivatives, and Lean's
kernel checks the resulting proofs. Search uses **1,000 units of fuel** by default; try
`ka 5000` or `hkat 200000` for a larger search. With `k` primitive tests, `kat` enumerates
`2^k` Boolean assignments (for typed goals, `k` is the largest test count at any object).
Adding tests can be expensive: the four-test example in
[Examples/CompilerOpts](../RelationAlgebra/Examples/CompilerOpts.lean) needs `hkat 500000` and
about a minute. The Boolean/residual extension of `ra` uses up to 16 normalization passes
and a structural check bounded to 4,096 rule attempts. These bounds are separate from the
derivative search fuel.

Keep these limits in mind:

- A failed tactic does **not** establish that the goal is false: fuel, resource limits, or
  unsupported syntax may prevent a proof. Search completeness is not proved.
- `ka`, `kat` and `ra` ignore the local context. `hkat` is the one that reads it: it turns
  Hoare-style hypotheses into zero constraints and calls `kat` after eliminating them.
  For typed goals, it first composes each constraint with paths connecting it to the goal’s
  endpoints. This can need more fuel; try `hkat 10000`.
- `hkat` accepts Hoare triples, zero constraints, Boolean equalities and inequalities, and
  supported guarded action constraints. Arbitrary action equations are not supported.
  Soundness of elimination is proved; Hardin–Kozen completeness is not.
- `ra` is incomplete: it uses structural laws, Boolean simplification, residual adjunctions
  and variance, and Dedekind/modular inequalities. It does not decide all relation-algebra
  identities. The Boolean/residual extension uses proved rewrites directly; the existing
  expression syntax and untyping theorem still cover only KA with converse.

The tactics apply to abstract KATs, not just to concrete models:

```lean
import RelationAlgebra
open scoped Computability KAT

example {T K : Type*} [BooleanAlgebra T] [KleeneAlgebra K] [KAT T K]
    (b : T) (p : K) : KAT.HoareTriple ⊤ (KAT.whileDo b p) bᶜ := by
  kat

example {T K : Type*} [BooleanAlgebra T] [KleeneAlgebra K] [KAT T K]
    (b : T) (p : K) (h : KAT.HoareTriple b p b) : KAT.HoareTriple b p∗ b := by
  hkat
```

The proved Hoare rules are also available directly. For example, an invariant preserved by the
guarded body is preserved by the loop:

```lean
example {T K : Type*} [BooleanAlgebra T] [KleeneAlgebra K] [KAT T K]
    (b i : T) (p : K) (h : KAT.HoareTriple (b ⊓ i) p i) :
    KAT.HoareTriple i (KAT.whileDo b p) (bᶜ ⊓ i) :=
  KAT.HoareTriple.whileDo h
```

## One or more steps

Strict iteration is a derived operation: `a⁺ = a * a∗ = a∗ * a`. It needs no additional
axioms. Star permits zero steps; strict iteration requires at least one. A nonempty cycle
can still relate a state to itself.

```lean
import RelationAlgebra
open scoped Computability

example {K : Type*} [KleeneAlgebra K] (a : K) : a⁺ = a + a * a⁺ := by ka
example {K : Type*} [KleeneAlgebra K] (a b : K) : a * (b * a)⁺ = (a * b)⁺ * a := by ka
```

For typed morphisms, `f⁺` is available only when `f : X ⟶ X`; the induction and sliding
laws still allow rectangular contexts. Relational membership is exactly `Relation.TransGen`,
and `Matrix.ofRel_kplus` proves the same nonempty-path semantics for zero-one matrices.
See [the laws](../RelationAlgebra/Kleene/Iteration.lean),
[typed laws](../RelationAlgebra/TypedIteration.lean), and
[examples](../RelationAlgebra/Examples/Iteration.lean).

## Programs with different source and target types

Use categorical composition `≫` and choice `⊔`. Star is available only for endomorphisms.
Tests at an object `X` belong to `T X`, with the typed notation `⌞b⌟`:

```lean
import RelationAlgebra

open CategoryTheory
open scoped Computability TypedKAT

example {C : Type*} [Category C] [KleeneCategory C]
    {X Y : C} (p : X ⟶ Y) (q : Y ⟶ X) :
    p ≫ (q ≫ p)∗ = (p ≫ q)∗ ≫ p := by
  kat

example {C : Type*} [Category C] [KleeneCategory C]
    {T : C → Type*} [∀ X, BooleanAlgebra (T X)] [TypedKAT C T]
    {X Y : C} (b : T X) (p : X ⟶ Y) :
    TypedKAT.ifThenElse b p p = p := by
  kat

-- Compose specifications whose programs change the state space.
example {C : Type*} [Category C] [KleeneCategory C]
    {T : C → Type*} [∀ X, BooleanAlgebra (T X)] [TypedKAT C T]
    {X Y Z : C} (p : X ⟶ Y) (q : Y ⟶ Z) (b : T X) (c : T Y) (d : T Z)
    (hp : TypedKAT.HoareTriple b p c) (hq : TypedKAT.HoareTriple c q d) :
    TypedKAT.HoareTriple b (p ≫ q) d := by
  hkat
```

`CategoryTheory.RelCat` supplies the model of heterogeneous relations. More examples,
including source and target guards, loops, and inequalities, are in
[Examples/TypedDecide](../RelationAlgebra/Examples/TypedDecide.lean).

To reuse an untyped law directly, use
[`TypedKAT.Term.eval_eq_of_erase_eval_eq`](../RelationAlgebra/TypedKAT/Untyping.lean), or
`eval_le_of_erase_eval_le` for inequalities. Prove the law for the erased expressions over
arbitrary untyped KATs; the theorem transports it to any typed interpretation. No atom bound
or checker fuel is required. See [worked examples](../RelationAlgebra/Examples/Untyping.lean).

Converse reverses a morphism's endpoints: `f : X ⟶ Y` gives `fᵒ : Y ⟶ X`.
Enable the notation with `open scoped KleeneCategoryWithConverse`:

```lean
open CategoryTheory
open scoped KleeneCategoryWithConverse

example {C : Type*} [Category C] [KleeneCategory C] [KleeneCategoryWithConverse C]
    {X Y Z : C} (f h : X ⟶ Y) (g : Y ⟶ Z) :
    ((f ⊔ h) ≫ g)ᵒ = gᵒ ≫ fᵒ ⊔ gᵒ ≫ hᵒ := by
  ra
```

Instances cover heterogeneous relations (`RelCat`) and rectangular matrices (`Matrix.Mat K`).
Matrix converse is conjugate transpose, so coefficients require `[StarRing K]`.
[`TypedRA.Term.eval_eq_of_erase_eval_eq`](../RelationAlgebra/TypedRA/Untyping.lean) and its
inequality counterpart transport universally valid untyped laws with converse to typed
models, without finiteness or continuity assumptions. See the
[untyping examples](../RelationAlgebra/Examples/ConverseUntyping.lean).

Residuals retain their endpoints. For `f : X ⟶ Y` and `h : X ⟶ Z`, `f ⇘ h : Y ⟶ Z`
is the greatest `g` such that `f ≫ g ≤ h`; dually, `h ⇙ g : X ⟶ Y` is the greatest such
`f`. Open `ResiduatedKleeneCategory` for the typed notation:

```lean
open scoped ResiduatedKleeneCategory

example {C : Type*} [Category C] [KleeneCategory C] [ResiduatedKleeneCategory C]
    {X Y Z : C} (f : X ⟶ Y) (h : X ⟶ Z) : f ≫ (f ⇘ h) ≤ h := by
  ra
```

`RelCat` supplies Boolean operations and both residuals. Relation complement is taken
inside the universal relation between the two objects; KAT test complement is relative to
an object's identity. For rectangular matrices, `Matrix.lres` and `Matrix.rres` take finite
meets of scalar residuals, requiring `[ResiduatedKleeneLattice K]`. They also supply the
residuals on `Matrix.Mat K`; empty dimensions produce top entries. See
[typed interfaces](../RelationAlgebra/Examples/TypedResidual.lean) and
[matrix examples](../RelationAlgebra/Examples/MatrixResidual.lean).

For guarded-string semantics, `TypedKAT.LanguageCat src tgt k` is a typed KAT with atoms
of length `k`, over an arbitrary object alphabet. Use `LanguageCat.Tests X` for tests at
object `X`, and `testVarAt X i` for a primitive test. `Term.eval_languageCat` proves that
canonical interpretation agrees with `Term.lang`. See the
[language-model examples](../RelationAlgebra/Examples/LanguageModel.lean).

For expressions modulo the KAT laws, use `TypedKAT.FreeCat src tgt`. Its morphisms are
classes of typed expressions, and `FreeCat.Tests X` is the free Boolean algebra of tests at
`X`. Equality and order compare guarded-string languages at every atom bound, so there is
no fixed limit on test variable indices.

`FreeCat.lift o τ ρ` interprets this free model in any typed KAT. Supply an object map `o`,
independent test valuations `τ` at each object, and actions `ρ` with matching endpoints.
`FreeCat.existsUnique_lift` proves that this interpretation is the **unique typed KAT
homomorphism** extending those assignments. See the
[free-model examples](../RelationAlgebra/Examples/FreeKAT.lean).

## Concrete typed models

| Model | Use it for | Examples |
| --- | --- | --- |
| `FinRelCat` | Computable relations between finite types; Boolean tests, converse, star and residuals | [Finite relations](../RelationAlgebra/Examples/FiniteRelations.lean) |
| `SetoidRelCat` | Relations respecting equivalences on two state spaces; identity is equivalence, tests are subsets of the quotient | [Setoid relations](../RelationAlgebra/Examples/SetoidRelations.lean) |
| `TraceCat σ src tgt` | Trace languages over arbitrary shared states `σ`, with action endpoints specified by `src` and `tgt` | [Typed traces](../RelationAlgebra/Examples/TypedTraces.lean) |

The first two models have faithful typed KAT interpretations in `RelCat`, with an order
isomorphism on every hom-set. For setoids, the interpretation uses quotient types.

Trace composition checks both action types and equality of the shared boundary state.
Top, complement and residuals range only over well-typed traces. Forgetting types preserves
composition, tests and iteration; it need not preserve top or complement. This general
trace model has no atom bound and does not require finite states or actions.

## Maps, points, and atoms

`AllegoryCategory C` provides typed composition, converse, intersection, and the modular
law. It requires no Kleene star or Boolean structure. `RelationCategory` supplies it
automatically, including for relations, finite relations, setoid relations, and matrices.

For `f : X ⟶ Y`, the predicates in `AllegoryCategory` have these relational meanings:

| Predicate | Meaning |
| --- | --- |
| `Functional f` | Each input has at most one output |
| `Total f` | Every input has an output |
| `Injective f` | Each output has at most one input |
| `Surjective f` | Every output has an input |
| `IsMap f` | Functional and total; exactly the graphs of functions in `RelCat` |
| `IsPoint f` | A singleton row, with a nonempty target |
| `IsAtom f` | A singleton pair |

```lean
example {C : Type*} [CategoryTheory.Category C] [AllegoryCategory C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : AllegoryCategory.IsMap f) (hg : AllegoryCategory.IsMap g) :
    AllegoryCategory.IsMap (f ≫ g) := hf.comp hg

example {X Y : CategoryTheory.RelCat} (f : X → Y) :
    AllegoryCategory.IsMap (CategoryTheory.RelCat.graph f) :=
  CategoryTheory.RelCat.graph_isMap f
```

Points and atoms need top on each hom-set. Their abstract definition of nonemptiness
quantifies over all objects; it agrees with `f ≠ ⊥` in `RelCat`, but not in every allegory.
Similarly, `AllegoryCategory.IsAtom` agrees with Mathlib's lattice `IsAtom` for relations;
the abstract minimality theorem is among **nonempty** morphisms. Every algebraic atom
factors into two points over any nonempty common target.

Use `open scoped AllegoryCategory` for converse notation `fᵒ` in the weak interface.
`End` and `SingleObj` reverse composition relative to scalar multiplication, so their
compatibility theorems exchange functional/injective and total/surjective.
See the [worked examples](../RelationAlgebra/Examples/TypedAllegory.lean), including empty
carriers and the distinction between algebraic and lattice atoms.

## Residuals without Kleene star

`ResiduatedAllegoryCategory C` adds two operations to `AllegoryCategory C`, on the
same hom-set orders. For `f : X ⟶ Y` and `h : X ⟶ Z`, `f ⇘ h : Y ⟶ Z` is the
greatest `g` with `f ≫ g ≤ h`. Dually, `h ⇙ g` is the greatest such `f`.
Enable their notation with `open scoped ResiduatedAllegoryCategory`.

```lean
open scoped AllegoryCategory ResiduatedAllegoryCategory in
example {C : Type*} [CategoryTheory.Category C] [AllegoryCategory C]
    [ResiduatedAllegoryCategory C] {X Y Z : C} (f : X ⟶ Y) (h : X ⟶ Z) :
    f ≫ (f ⇘ h) ≤ h := ResiduatedAllegoryCategory.comp_ldiv_le f h
```

The core needs neither Boolean complements nor Kleene star, and assumes no bottom,
top, or completeness. With bottom, composition annihilates it by adjunction. With
bottom and top, `ResiduatedAllegoryCategory.isVector_disjoint_iff` proves that a vector
`g` satisfies `f ⊓ g = ⊥ ↔ gᵒ ≫ f = ⊥`, without using complements.

Existing relation categories inherit the interface and retain their residual
operations. Finite relations still compute. `ResiduatedAllegory K` is the scalar
interface; `End` and `SingleObj` exchange left and right residuals because they reverse
composition. The [examples](../RelationAlgebra/Examples/ResiduatedAllegory.lean) include
a three-element chain with no complement for its middle element, empty carriers,
and compatibility with finite relations, setoid relations, and matrices.

## Library guide

The library reuses Mathlib's `KleeneAlgebra`, `BooleanAlgebra`, `SetRel`, `Language`,
`Matrix`, and category APIs. Tests form a separate Boolean algebra `T`, connected to `K`
by `KleeneAlgebraWithTests T K` (abbreviated `KAT T K`).

| To work with… | Start here |
| --- | --- |
| Sliding, denesting, bisimulation, and least fixed points | [Kleene/Basic](../RelationAlgebra/Kleene/Basic.lean) |
| Strict iteration and nonempty paths | [Kleene/Iteration](../RelationAlgebra/Kleene/Iteration.lean), [TypedIteration](../RelationAlgebra/TypedIteration.lean), [MatrixIteration](../RelationAlgebra/Models/MatrixIteration.lean) |
| Quantale constructions and complete KAs | [Kleene/Quantale](../RelationAlgebra/Kleene/Quantale.lean), [Kleene/Complete](../RelationAlgebra/Kleene/Complete.lean) |
| Tests, guarded commands, and partial-correctness rules | [KAT/Defs](../RelationAlgebra/KAT/Defs.lean), [KAT/Basic](../RelationAlgebra/KAT/Basic.lean), [KAT/Hoare](../RelationAlgebra/KAT/Hoare.lean) |
| Relations and finite matrices | [Models/Rel](../RelationAlgebra/Models/Rel.lean), [Models/Matrix](../RelationAlgebra/Models/Matrix.lean), [Models/MatrixExt](../RelationAlgebra/Models/MatrixExt.lean) |
| Traces, guarded strings, setoid and finite relations | [Models/Trace](../RelationAlgebra/Models/Trace.lean), [Models/TypedTrace](../RelationAlgebra/Models/TypedTrace.lean), [Models/SetoidRelCategory](../RelationAlgebra/Models/SetoidRelCategory.lean), [Models/FinRelCategory](../RelationAlgebra/Models/FinRelCategory.lean) |
| Converse, relation algebra, residuals, allegories, vectors and points | [Converse](../RelationAlgebra/Converse.lean), [Residuated](../RelationAlgebra/Residuated.lean), [Allegory](../RelationAlgebra/Allegory.lean), [Vectors](../RelationAlgebra/Vectors.lean) |
| Typed (many-object) Kleene algebra and typed KAT | [Typed](../RelationAlgebra/Typed.lean), [TypedKAT](../RelationAlgebra/TypedKAT.lean) |
| Typed allegories, maps, points, and atoms | [TypedAllegory](../RelationAlgebra/TypedAllegory.lean), [TypedPoints](../RelationAlgebra/TypedPoints.lean), [Boolean/iteration laws](../RelationAlgebra/TypedRelationPredicates.lean), [relational characterization](../RelationAlgebra/Models/RelPoints.lean) |
| Residuals on weak allegories | [ResiduatedAllegory](../RelationAlgebra/ResiduatedAllegory.lean), [TypedResiduatedAllegory](../RelationAlgebra/TypedResiduatedAllegory.lean) |
| Typed expressions and guarded-string semantics | [TypedKAT/Syntax](../RelationAlgebra/TypedKAT/Syntax.lean), [TypedKAT/GuardedString](../RelationAlgebra/TypedKAT/GuardedString.lean), [examples](../RelationAlgebra/Examples/TypedSyntax.lean) |
| Guarded-string languages as a typed KAT model | [TypedKAT/LanguageModel](../RelationAlgebra/TypedKAT/LanguageModel.lean), [examples](../RelationAlgebra/Examples/LanguageModel.lean) |
| Expressions modulo the KAT laws and their universal property | [TypedKAT/Free](../RelationAlgebra/TypedKAT/Free.lean), [semantic relations](../RelationAlgebra/TypedKAT/Semantics.lean), [homomorphisms](../RelationAlgebra/TypedKAT/Hom.lean), [examples](../RelationAlgebra/Examples/FreeKAT.lean) |
| Tactics, derivatives, and soundness proofs | [Decide](../RelationAlgebra/Decide) |
| Hoare hypotheses and the `hkat` tactic | [KAT/Hypotheses](../RelationAlgebra/KAT/Hypotheses.lean), [typed hypotheses](../RelationAlgebra/TypedKAT/Hypotheses.lean), [Decide/HKATTactic](../RelationAlgebra/Decide/HKATTactic.lean) |
| Normalisation and the `ra` tactics | [Decide/RaTactic](../RelationAlgebra/Decide/RaTactic.lean), [Kleene core](../RelationAlgebra/Decide/Normalise.lean), [Boolean/residual extension](../RelationAlgebra/Decide/FullRATactic.lean) |
| Automata and Kozen's completeness proof | [Automata](../RelationAlgebra/Automata), [Decide/KACompleteness](../RelationAlgebra/Decide/KACompleteness.lean) |
| Kozen–Smith completeness for KAT (untyped) | [KATCompleteness](../RelationAlgebra/KATCompleteness) |
| Typed KAT completeness and reflection | [TypedKATCompleteness](../RelationAlgebra/TypedKATCompleteness) |
| Reusing untyped laws in typed models | [KAT untyping](../RelationAlgebra/TypedKAT/Untyping.lean), [converse untyping](../RelationAlgebra/TypedRA/Untyping.lean) |
| Typed converse, Boolean relation algebra, and residuals | [TypedConverse](../RelationAlgebra/TypedConverse.lean), [TypedBoolean](../RelationAlgebra/TypedBoolean.lean), [TypedResiduated](../RelationAlgebra/TypedResiduated.lean) |
| Rectangular matrix residuals and relation algebra | [Models/MatrixResidual](../RelationAlgebra/Models/MatrixResidual.lean), [examples](../RelationAlgebra/Examples/MatrixResidual.lean) |
| The IMP while-language on top of KAT | [Examples/Imp](../RelationAlgebra/Examples/Imp.lean) |
| Certified compiler optimisations | [Examples/CompilerOpts](../RelationAlgebra/Examples/CompilerOpts.lean) |
| Paterson’s S6A = S6E flowchart equivalence | [Examples/Paterson](../RelationAlgebra/Examples/Paterson.lean), [schemes](../RelationAlgebra/Examples/Paterson/Programs.lean), [regressions](../RelationAlgebra/Examples/Paterson/Regression.lean) |

Each module starts with an overview of its definitions and conventions. The Hoare rules
cover propositional control flow; termination proofs are outside their scope. The matrix star
uses Kozen's block construction; the general instance is noncomputable, and
`Matrix.kstarFin` is a computable version for `Fin n` proved equal to it.

[PORTING.md](../PORTING.md) tracks coverage of Pous' library module by module, and is explicit
about what is proved and what is not.

**Paterson’s flowcharts** are a worked application of the framework. `Paterson.paterson M`
proves that S6A and S6E define the same state relation for arbitrary interpretations of
`f`, `g`, and `P` over natural-valued stores, following Pous’s model. Both schemes return
through `io` and clear their four temporary variables. The proof combines assignment
substitution, dead-store elimination through loops, and KAT reasoning; it does not assume
that the programs terminate. Import `RelationAlgebra.Examples.Paterson` for this development.
