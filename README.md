# RelationAlgebra: Kleene algebra, KAT and relation algebra in Lean 4

A reusable Lean 4 / Mathlib library for **Kleene algebra (KA)**, **Kleene algebra with tests
(KAT)** and **relation algebra**, in the spirit of Damien Pous'
[`relation-algebra`](https://github.com/damien-pous/relation-algebra) library for Rocq/Coq,
including reflective decision procedures (`ka`, `kat`).

The guiding principle is to reuse Mathlib wherever it already has the right notion:

| Concept | Provided by |
|---|---|
| idempotent semirings, Kleene algebras, `a∗`, Kozen's induction axioms | Mathlib (`Mathlib.Algebra.Order.Kleene`) |
| Boolean algebras of tests | Mathlib (`BooleanAlgebra`) |
| converse | Mathlib (`star`, `StarRing`) |
| binary relations as sets of pairs, composition `○`, identity, converse `inv` | Mathlib (`Mathlib.Data.Rel`, `SetRel`) |
| reflexive-transitive closure | Mathlib (`Relation.ReflTransGen`) |
| quantales | Mathlib (`Mathlib.Algebra.Order.Quantale`) |
| the language model `Language α` | Mathlib (`Mathlib.Computability.Language`) |
| matrices, block matrices, reindexing | Mathlib (`Matrix`, `Matrix.fromBlocks`, `Matrix.reindex`) |
| categories, `SingleObj`, `RelCat`, `End` | Mathlib (`CategoryTheory`) |
| derived KA laws (sliding, denesting, bisimulation, fixpoints, ...) | **this library** |
| KAT: the class, guarded commands, Hoare logic | **this library** |
| relation algebras (Dedekind, Schröder, Tarski laws) | **this library** |
| typed (many-object) Kleene algebras | **this library** |
| the relational model of KA, KAT and relation algebra | **this library** |
| the Kleene algebra of matrices (Kozen's block construction) | **this library** |
| KA from a quantale (`a∗ = ⨆ n, a ^ n`), complete Kleene algebras | **this library** |
| decision procedures `ka` (Antimirov derivatives) and `kat` (guarded strings) | **this library** |

## Layout

```
RelationAlgebra/
  Kleene/
    Basic.lean         -- derived laws of Kleene algebra (namespace `KleeneAlgebra`)
    Quantale.lean      -- `IdemSemiring.ofQuantale`, `KleeneAlgebra.ofQuantale`
    Complete.lean      -- `CompleteKleeneAlgebra` (star-continuous KAs); relations, languages
  KAT/
    Defs.lean          -- `class KleeneAlgebraWithTests T K` (abbrev `KAT`), notation `⌜b⌝`
    Basic.lean         -- laws about tests; `KAT.ifThenElse`, `KAT.whileDo`
    Hoare.lean         -- `KAT.HoareTriple` and the rules of Hoare logic
  Converse.lean        -- Kleene algebras with converse; `class RelationAlgebra`; relations
  Typed.lean           -- `class KleeneCategory`: typed KA on Mathlib categories; `SingleObj`, `RelCat`
  Models/
    Rel.lean           -- `SetRel α α` is a KA / KAT (scoped instances in namespace `SetRel`)
    Bool.lean          -- every Kleene algebra is a KAT with the trivial tests `Bool`
    Matrix.lean        -- `Matrix n n K` is a KA when `K` is (`Matrix.kstar_fromBlocks`)
  Decide/
    Term.lean          -- regular expressions `KleeneAlgebra.Term`; soundness of the language model
    Antimirov.lean     -- partial derivatives, bisimulation checker, `Term.decideEq`, its soundness
    Tactic.lean        -- the `ka` tactic
    GuardedString.lean -- KAT terms, atoms, guarded strings, derivatives, `KTerm.decideEq`
    KATSound.lean      -- atoms of a Boolean algebra; soundness of guarded strings in complete KATs
    KATTactic.lean     -- the `kat` tactic
  Examples/
    Basic.lean         -- sanity checks and small examples
    Decide.lean        -- examples for `ka` and `kat`
```

## Design notes

**Kleene algebra.** We use Mathlib's `KleeneAlgebra` class unchanged.  Its order is the
semilattice order `a ≤ b ↔ a + b = b`, and the star axioms are Kozen's.  `Kleene/Basic.lean`
adds the theorems one actually needs when reasoning in KA: least-fixpoint characterisations,
`a∗ * a = a * a∗`, the sliding rule `a * (b * a)∗ = (a * b)∗ * a`, the denesting rules
`(a + b)∗ = a∗ * (b * a∗)∗ = (a∗ * b)∗ * a∗`, the bisimulation rules, and
`(a + b)∗ = a∗ * b∗` under commutation.

**Tests.** Following Pous, a KAT is *two-sorted*: a Boolean algebra `T` of tests and a Kleene
algebra `K`, related by a mixin class

```lean
class KleeneAlgebraWithTests (T K : Type*) [BooleanAlgebra T] [KleeneAlgebra K] where
  test : T → K
  test_bot : test ⊥ = 0
  test_top : test ⊤ = 1
  test_sup (a b : T) : test (a ⊔ b) = test a + test b
  test_inf (a b : T) : test (a ⊓ b) = test a * test b
```

so that both Mathlib hierarchies are reused as they are.  With `open scoped KAT`, `⌜b⌝`
denotes `test b`.  Guarded commands are `ifThenElse b p q = ⌜b⌝ * p + ⌜bᶜ⌝ * q` and
`whileDo b p = (⌜b⌝ * p)∗ * ⌜bᶜ⌝`; a Hoare triple is `HoareTriple b p c := ⌜b⌝ * p * ⌜cᶜ⌝ = 0`
(Kozen 2000), and the rules of Hoare logic are theorems.

**Converse and relation algebra.** Converse is Mathlib's `star`; a Kleene algebra with
converse is just `[KleeneAlgebra K] [StarRing K]`, and `star (a∗) = (star a)∗` is a theorem.
`class RelationAlgebra K extends KleeneAlgebra K, BooleanAlgebra K, Star K` adds the Dedekind
law, from which the modular laws, the Schröder rules and Tarski's law are derived.

**Typed Kleene algebra.** `class KleeneCategory C` on a Mathlib `Category` (hom-sets are
join-semilattices with bottom, composition is bilinear, endomorphisms have a star with
*rectangular* induction axioms) is Pous' many-object presentation.  Every KA is a one-object
Kleene category (`SingleObj`), `RelCat` is one, and every endomorphism monoid `End X` is a KA.

**Relations.** Mathlib's `SetRel α β` is reducibly `Set (α × β)`.  Because `Set` already has
scoped pointwise `+`/`*` instances in Mathlib, the ring-like instances on `SetRel α α` are
**scoped**: `open scoped SetRel` activates `Mul`, `Add`, `One`, `Zero`, `KStar`,
`IdemSemiring`, `IsQuantale`, `KleeneAlgebra`, `CompleteKleeneAlgebra`, `RelationAlgebra` and
`KleeneAlgebraWithTests (Set α) (SetRel α α)`.  Here `R * S = R ○ S`, `R + S = R ∪ S`, `R∗` is
`Relation.ReflTransGen`, `star R = R.inv`, and the test `s : Set α` is the sub-identity
relation `SetRel.ofSet s`.

**Matrices.** `Matrix n n K` is a Kleene algebra for every finite `n` (Kozen).  The star is
built by induction on the size along `Fin (k + 1) ≃ Fin k ⊕ Fin 1` using the `2 × 2` block
formula, transported along `Fintype.equivFin`, and since the star of a KA is unique the block
formula `Matrix.kstar_fromBlocks` holds for the resulting instance.

**Decision procedures.** `ka` and `kat` are reflective tactics.  `ka` reifies the goal into
regular expressions and runs (inside the kernel) a bisimulation search based on Antimirov
partial derivatives; the certificate is checked by a verified checker
(`KleeneAlgebra.Term.lang_eq_of_decideEq`).  `kat` does the same with guarded-string
derivatives over the `2 ^ k` atoms of the `k` primitive tests
(`KAT.KTerm.gs_eq_of_decideEq`), after unfolding `ifThenElse`, `whileDo` and `HoareTriple`.

**Scope of the soundness proofs.** The tactics are proved sound for *complete* Kleene
algebras and KATs (`CompleteKleeneAlgebra`: a Kleene algebra whose order is a complete lattice
and whose multiplication preserves arbitrary joins).  This is stronger than star-continuity.
The instances provided are relations `SetRel α α` (with tests `Set α`) and languages
`Language α` (with the trivial tests `Bool`); in particular `ka` does not (yet) apply to
matrices, whose `CompleteKleeneAlgebra` instance is not provided, nor to a goal stated for an
arbitrary `[KleeneAlgebra K]`.  The soundness statements
(`KleeneAlgebra.Term.eval_eq_of_lang_eq`, `KAT.KTerm.eval_eq_of_decideEq`) are of the form
"if the checker accepts a certificate, the equation holds"; the search is bounded by fuel, so
a failure means either an invalid equation or exhausted fuel, and no completeness of the
search is proved.  Pous' tactics are sound for *all* KAs/KATs because his library proves
Kozen's completeness theorems; that is the main remaining gap (see below).

```lean
open scoped SetRel KAT
example (R S : SetRel α α) : (R + S)∗ = R∗ * (S * R∗)∗ := by ka
example (s : Set α) (R : SetRel α α) : KAT.HoareTriple ⊤ (KAT.whileDo s R) sᶜ := by kat
```

## Building

```
lake exe cache get
lake build
```

Toolchain: Lean `v4.30.0`, Mathlib `v4.30.0` (see `lean-toolchain`, `lakefile.toml`).

## Comparison with `relation-algebra` (Rocq) and roadmap

What is here now covers the algebraic core of Pous' library (the KA / KAT / relation algebra
hierarchy, relations, languages, matrices, the typed presentation) and the two decision
procedures, on top of Mathlib.  Remaining differences and natural next steps:

1. **Completeness.** Kozen's completeness theorem for KA (w.r.t. `Language`) and
   Kozen–Smith's for KAT (w.r.t. guarded strings) would make `ka`/`kat` sound in arbitrary
   KAs/KATs, not only complete ones.  The matrix construction here is the main ingredient.
   This is the priority: abstract `[KleeneAlgebra K]` / `[KAT T K]` goals currently have no
   automation beyond the lemma library.
2. **`CompleteKleeneAlgebra (Matrix n n K)`** for complete `K`, so that `ka` applies to
   matrices over relations or languages.
3. **Typed KAT and typed matrices** in the `KleeneCategory` setting (heterogeneous relations
   `SetRel α β`, rectangular matrices as morphisms).
4. **Computable stars**: the star on `Matrix n n K` is noncomputable (it goes through
   `Fintype.equivFin`); a computable version for `Fin n` is easy to add.
5. **More of the lattice hierarchy**: residuals, `ra` decision procedure for relation
   algebra fragments, allegories.
