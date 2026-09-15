# Relational algebra in Lean 4

Prove equations between programs and relations using **Kleene algebra (KA)** and
**Kleene algebra with tests (KAT)**. This library provides algebraic laws, relational and
matrix models, Hoare rules, and the `ka` and `kat` tactics, built on Mathlib.

The project is inspired by **Damien Pous's
[relation-algebra library for Rocq/Coq](https://github.com/damien-pous/relation-algebra)**.
His algebraic organization and approach to automated KA/KAT reasoning are central references
for this Lean development. See [credits and references](#credits-and-references).

**Current scope:** the theorem library supports abstract KA/KAT reasoning. `ka`, `kat` and
`hkat` all work in **any** Kleene algebra, because Kozen's completeness theorem and the
untyped Kozen–Smith completeness theorem for KAT are both proved here. `hkat` additionally
uses Hoare-style hypotheses from the context. `kat` also handles typed categorical goals,
where programs can have different source and target objects. `ra` handles converse over the
Kleene fragment. See [tactic support](#tactic-support) before choosing a model.

## Get started

Install [Lean and Lake](https://lean-lang.org/install/), then run:

```sh
git clone https://github.com/focs-lab/lean-relational-algebra.git
cd lean-relational-algebra
lake exe cache get
lake build
```

The project pins **Lean 4.30.0 and Mathlib 4.30.0**. The cache command downloads prebuilt
Mathlib dependencies.

Save this as `Demo.lean` in the repository and check it with `lake env lean Demo.lean`:

```lean
import RelationAlgebra

open scoped Computability SetRel KAT

variable {α : Type*}

-- Denesting: two equivalent ways to express iteration.
example (R S : SetRel α α) : (R + S)∗ = R∗ * (S * R∗)∗ := by
  ka

-- A guard and its negation cannot both hold.
example (b : Set α) : (⌜b⌝ : SetRel α α) * ⌜bᶜ⌝ = 0 := by
  kat

-- Whenever the loop terminates, its guard is false.
example (b : Set α) (R : SetRel α α) :
    KAT.HoareTriple ⊤ (KAT.whileDo b R) bᶜ := by
  kat

-- `hkat` also uses the hypotheses in the context.
example (b : Set α) (R : SetRel α α) (h : ⌜b⌝ * R ≤ R * ⌜b⌝) :
    (⌜b⌝ : SetRel α α) * R∗ ≤ R∗ * ⌜b⌝ := by
  hkat

-- `ra` adds converse, for any Kleene algebra with an involution.
example (R S : SetRel α α) : star (R * S) = star S * star R := by
  ra
```

More examples: [algebra and relations](RelationAlgebra/Examples/Basic.lean) ·
[using the tactics](RelationAlgebra/Examples/Decide.lean) ·
[typed goals](RelationAlgebra/Examples/TypedDecide.lean).

<details>
<summary><strong>Use as a dependency in another project</strong></summary>

Use the same Lean toolchain (**Lean 4.30.0**) and add this entry to your `lakefile.toml`:

```toml
[[require]]
name = "relation_algebra"
git = "https://github.com/focs-lab/lean-relational-algebra.git"
rev = "8502d9911da9f48881659ee9b4699568bb672081"
```

This pins the library to a revision with typed `kat`, KA/KAT completeness, and algebraic
untyping.
Run `lake update`, `lake exe cache get`, and `lake build`, then import `RelationAlgebra` to use
the library.

</details>

## Reading the notation

For relations `R S : SetRel α α` and a test `b : Set α`:

| Expression | Meaning |
| --- | --- |
| `R + S` | Union / nondeterministic choice |
| `R * S` | Sequential composition: first `R`, then `S` |
| `0`, `1` | Empty relation, identity relation |
| `R∗` | Zero or more steps of `R` (reflexive-transitive closure) |
| `R ≤ S` | Relation inclusion |
| `⌜b⌝` | Identity restricted to states satisfying `b` |
| `bᶜ` | Negation of the test |
| `star R` | Converse: reverse every pair in `R` |

`open scoped Computability` enables `∗`; `KAT` enables `⌜b⌝`; `SetRel` selects the
relational algebra instances. The last scope matters because relations are represented as
sets, which can also carry Mathlib's pointwise operations.

`KAT.ifThenElse b p q` and `KAT.whileDo b p` encode guarded commands.
`KAT.HoareTriple b p c` means **partial correctness**: every terminating execution of `p`
from `b` ends in `c`. It is defined by `⌜b⌝ * p * ⌜cᶜ⌝ = 0`.

## Tactic support

| Tactic | Goals | Operations understood |
| --- | --- | --- |
| `ka` | Equalities and inequalities | `0`, `1`, `+`, `*`, `∗` |
| `kat` | Equalities, inequalities, and `KAT.HoareTriple` | KA operations, embedded Boolean tests, `ifThenElse`, `whileDo` |
| `kat` on typed goals | Equalities, inequalities, and `TypedKAT.HoareTriple` | `⊥`, `𝟙`, `⊔`, `≫`, `∗`, typed tests and guarded commands |
| `hkat` | Untyped goals, using Hoare-style hypotheses from the context | Untyped KAT operations |
| `ra`, `ra_normalise`, `ra_simpl` | Equalities and inequalities | KA operations and converse |

`ka` proves identities in any Kleene algebra. `kat` adds Boolean tests and also supports
typed composition. `hkat` uses hypotheses for untyped goals. `ra` normalises expressions
with converse.

`ka` requires only `[KleeneAlgebra K]`. It is sound in every Kleene algebra because
**Kozen's completeness theorem** is proved in
[Decide/KACompleteness](RelationAlgebra/Decide/KACompleteness.lean): regular expressions with
the same language are equal in every Kleene algebra.

For untyped goals, `kat` and `hkat` require `[KleeneAlgebra K]` plus a
`KleeneAlgebraWithTests T K` instance for an arbitrary `[BooleanAlgebra T]`. They are sound in every such algebra because the untyped
**Kozen–Smith completeness theorem** is proved in
[KATCompleteness/Main](RelationAlgebra/KATCompleteness/Main.lean): terms with the same
guarded-string semantics have the same value in every KAT. Neither completeness of the lattice,
star-continuity, commutativity nor finiteness is assumed. Relations have tests `Set α`;
languages have the trivial tests `Bool`.

**Typed KAT completeness** is also proved in
[TypedKATCompleteness/Main](RelationAlgebra/TypedKATCompleteness/Main.lean), for arbitrary
categories and object alphabets. `kat` uses it to prove ordinary categorical goals directly:
it requires `[Category C] [KleeneCategory C]` and, when tests occur, `[TypedKAT C T]`
with `[∀ X, BooleanAlgebra (T X)]`. See [typed tactic examples](RelationAlgebra/Examples/TypedDecide.lean).

`ra` requires `[KleeneAlgebra K] [StarRing K]`, which a `RelationAlgebra` instance supplies.

Three guarantees are worth keeping apart. *Accepting-checker soundness* is proved for all four
tactics: if the checker accepts, the goal holds. *Algebraic completeness* is proved for Kleene
algebra and for both untyped and typed KAT. *Search completeness* is proved for none of them.

`ka`, `kat` and `hkat` search for bisimulation certificates using derivatives, and Lean's
kernel checks the resulting proofs. Search uses **1,000 units of fuel** by default; try
`ka 5000` or `hkat 200000` for a larger search. With `k` primitive tests, `kat` enumerates
`2^k` Boolean assignments (for typed goals, `k` is the largest test count at any object).
Adding tests can be expensive: the four-test example in
[Examples/CompilerOpts](RelationAlgebra/Examples/CompilerOpts.lean) needs `hkat 500000` and
about a minute. `ra` does not search at all; it normalises both sides and compares.

Keep these limits in mind:

- A failed tactic does **not** establish that the goal is false: fuel, resource limits, or
  unsupported syntax may prevent a proof. Search completeness is not proved.
- `ka`, `kat` and `ra` ignore the local context. `hkat` is the one that reads it: it turns
  Hoare-style hypotheses into the form `z ≤ 0`, merges them, eliminates them à la
  Hardin–Kozen, and then calls `kat`.
- `hkat` does not yet support typed categorical goals. Use `kat` for typed identities and
  apply the typed Hoare rules directly when hypotheses are needed.
- `ra` covers `0`, `1`, `+`, `*`, `∗` and converse. It treats `⊓`, `ᶜ`, `⊤` and residuals as
  opaque atoms, and it is a normaliser rather than a decision procedure, so it is incomplete
  by design, as upstream's is.

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
```

`CategoryTheory.RelCat` supplies the model of heterogeneous relations. More examples,
including source and target guards, loops, and inequalities, are in
[Examples/TypedDecide](RelationAlgebra/Examples/TypedDecide.lean).

To reuse an untyped law directly, use
[`TypedKAT.Term.eval_eq_of_erase_eval_eq`](RelationAlgebra/TypedKAT/Untyping.lean), or
`eval_le_of_erase_eval_le` for inequalities. Prove the law for the erased expressions over
arbitrary untyped KATs; the theorem transports it to any typed interpretation. No atom bound
or checker fuel is required. See [worked examples](RelationAlgebra/Examples/Untyping.lean).

## Library guide

The library reuses Mathlib's `KleeneAlgebra`, `BooleanAlgebra`, `SetRel`, `Language`,
`Matrix`, and category APIs. Tests form a separate Boolean algebra `T`, connected to `K`
by `KleeneAlgebraWithTests T K` (abbreviated `KAT T K`).

| To work with… | Start here |
| --- | --- |
| Sliding, denesting, bisimulation, and least fixed points | [Kleene/Basic](RelationAlgebra/Kleene/Basic.lean) |
| Quantale constructions and complete KAs | [Kleene/Quantale](RelationAlgebra/Kleene/Quantale.lean), [Kleene/Complete](RelationAlgebra/Kleene/Complete.lean) |
| Tests, guarded commands, and partial-correctness rules | [KAT/Defs](RelationAlgebra/KAT/Defs.lean), [KAT/Basic](RelationAlgebra/KAT/Basic.lean), [KAT/Hoare](RelationAlgebra/KAT/Hoare.lean) |
| Relations and finite matrices | [Models/Rel](RelationAlgebra/Models/Rel.lean), [Models/Matrix](RelationAlgebra/Models/Matrix.lean), [Models/MatrixExt](RelationAlgebra/Models/MatrixExt.lean) |
| Traces, guarded strings, setoid and finite relations | [Models/Trace](RelationAlgebra/Models/Trace.lean), [Models/SetoidRel](RelationAlgebra/Models/SetoidRel.lean), [Models/FinRel](RelationAlgebra/Models/FinRel.lean) |
| Converse, relation algebra, residuals, allegories, vectors and points | [Converse](RelationAlgebra/Converse.lean), [Residuated](RelationAlgebra/Residuated.lean), [Allegory](RelationAlgebra/Allegory.lean), [Vectors](RelationAlgebra/Vectors.lean) |
| Typed (many-object) Kleene algebra and typed KAT | [Typed](RelationAlgebra/Typed.lean), [TypedKAT](RelationAlgebra/TypedKAT.lean) |
| Typed expressions and guarded-string semantics | [TypedKAT/Syntax](RelationAlgebra/TypedKAT/Syntax.lean), [TypedKAT/GuardedString](RelationAlgebra/TypedKAT/GuardedString.lean), [examples](RelationAlgebra/Examples/TypedSyntax.lean) |
| Tactics, derivatives, and soundness proofs | [Decide](RelationAlgebra/Decide) |
| Hoare hypotheses and the `hkat` tactic | [KAT/Hypotheses](RelationAlgebra/KAT/Hypotheses.lean), [Decide/HKATTactic](RelationAlgebra/Decide/HKATTactic.lean) |
| Normalisation and the `ra` tactics | [Decide/Normalise](RelationAlgebra/Decide/Normalise.lean), [Decide/RaTactic](RelationAlgebra/Decide/RaTactic.lean) |
| Automata and Kozen's completeness proof | [Automata](RelationAlgebra/Automata), [Decide/KACompleteness](RelationAlgebra/Decide/KACompleteness.lean) |
| Kozen–Smith completeness for KAT (untyped) | [KATCompleteness](RelationAlgebra/KATCompleteness) |
| Typed KAT completeness and reflection | [TypedKATCompleteness](RelationAlgebra/TypedKATCompleteness) |
| Reusing untyped laws in typed models | [TypedKAT/Untyping](RelationAlgebra/TypedKAT/Untyping.lean), [examples](RelationAlgebra/Examples/Untyping.lean) |
| The IMP while-language on top of KAT | [Examples/Imp](RelationAlgebra/Examples/Imp.lean) |
| Certified compiler optimisations | [Examples/CompilerOpts](RelationAlgebra/Examples/CompilerOpts.lean) |

Each module starts with an overview of its definitions and conventions. The Hoare rules
cover propositional control flow; termination proofs are outside their scope. The matrix star
uses Kozen's block construction; the general instance is noncomputable, and
`Matrix.kstarFin` is a computable version for `Fin n` proved equal to it.

[PORTING.md](PORTING.md) tracks coverage of Pous' library module by module, and is explicit
about what is proved and what is not.

## Next steps

KA completeness and untyped KAT completeness are done, so `ka`, `kat` and `hkat` all work in
arbitrary Kleene algebras. Typed expressions and their guarded-string semantics are now
available, with completeness proved for arbitrary typed KATs: composition checks endpoints,
tests have an interpretation at each object, and only endomorphisms can be iterated.
`kat` reifies typed goals directly, and the algebraic untyping interface transports
universally valid untyped laws to typed models. The next priorities are **typed `hkat`**
and packaging the typed free models. Further work
includes extending `ra` beyond the Kleene fragment and proving Paterson's flowchart equivalence.
[PORTING.md](PORTING.md) has the
dependency-ordered plan and an exact continuation point.

## Credits and references

**Damien Pous and the contributors to
[relation-algebra](https://github.com/damien-pous/relation-algebra)** deserve particular
credit for the Rocq/Coq development that motivates this project: its treatment of tests and
typed algebras, and its use of derivatives and reflection for automated proofs.
Its [documentation](https://perso.ens-lyon.fr/damien.pous/ra/) is a valuable companion.
That library goes further than this one in several respects: it supports typed hypothesis
automation, its `ra` covers the whole lattice and residual syntax, and its structures are
typed throughout.
[PORTING.md](PORTING.md) records the gaps module by module.

We also build on the work of the **[Lean](https://github.com/leanprover/lean4)** and
**[Mathlib](https://github.com/leanprover-community/mathlib4)** contributors, reusing their
proof infrastructure, algebraic hierarchies, and models.

The main mathematical and mechanization references are:

- **Damien Pous (2013).** [Kleene Algebra with Tests and Coq Tools for While Programs](https://arxiv.org/abs/1302.1737). KAT formalization and automation.
- **Dexter Kozen (1994).** [A Completeness Theorem for Kleene Algebras and the Algebra of Regular Events](https://www.cs.cornell.edu/~kozen/papers/ka.pdf). KA axioms, matrices, and completeness.
- **Dexter Kozen (1997).** [Kleene Algebra with Tests](https://www.cs.cornell.edu/~kozen/Papers/kat.pdf). The KAT framework.
- **Dexter Kozen (2000).** [On Hoare Logic and Kleene Algebra with Tests](https://www.cs.cornell.edu/~kozen/Papers/Hoare.pdf). The algebraic encoding of partial correctness.
- **Dexter Kozen and Frederick Smith (CSL 1996).** [Kleene Algebra with Tests: Completeness and Decidability](https://www.cs.cornell.edu/~kozen/Papers/gs.pdf). Guarded strings and KAT completeness; both untyped and typed forms are proved here.
- **Valentin Antimirov (1996).** [Partial Derivatives of Regular Expressions and Finite Automaton Constructions](https://doi.org/10.1016/0304-3975(95)00182-4). The partial-derivative construction.
- **Alexander Krauss and Tobias Nipkow (2012).** [Proof Pearl: Regular Expression Equivalence and Relation Algebra](https://www21.in.tum.de/~nipkow/pubs/jar12.pdf). Verified equivalence checking and its application to relations.
- **Alfred Tarski (1941).** [On the Calculus of Relations](https://doi.org/10.2307/2268577). Foundations of relation algebra.
