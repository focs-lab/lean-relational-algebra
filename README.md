# RelationAlgebra: Kleene algebra with tests in Lean 4

A small, reusable Lean 4 / Mathlib library for **Kleene algebra (KA)** and **Kleene algebra
with tests (KAT)**, in the spirit of Damien Pous'
[`relation-algebra`](https://github.com/damien-pous/relation-algebra) library for Rocq/Coq.

The guiding principle is to reuse Mathlib wherever it already has the right notion:

| Concept | Provided by |
|---|---|
| idempotent semirings, Kleene algebras, `a∗`, Kozen's induction axioms | Mathlib (`Mathlib.Algebra.Order.Kleene`) |
| Boolean algebras of tests | Mathlib (`BooleanAlgebra`) |
| binary relations as sets of pairs, composition `○`, identity | Mathlib (`Mathlib.Data.Rel`, `SetRel`) |
| reflexive-transitive closure | Mathlib (`Relation.ReflTransGen`) |
| quantales | Mathlib (`Mathlib.Algebra.Order.Quantale`) |
| the language model `Language α` | Mathlib (`Mathlib.Computability.Language`) |
| derived KA laws (sliding, denesting, bisimulation, fixpoints, ...) | **this library** |
| KAT: the class, guarded commands, Hoare logic | **this library** |
| the relational model of KA and KAT | **this library** |
| KA from a quantale (`a∗ = ⨆ n, a ^ n`) | **this library** |

## Layout

```
RelationAlgebra/
  Kleene/
    Basic.lean      -- derived laws of Kleene algebra (namespace `KleeneAlgebra`)
    Quantale.lean   -- `IdemSemiring.ofQuantale`, `KleeneAlgebra.ofQuantale`
  KAT/
    Defs.lean       -- `class KleeneAlgebraWithTests T K` (abbrev `KAT`), notation `⌜b⌝`
    Basic.lean      -- laws about tests; `KAT.ifThenElse`, `KAT.whileDo`
    Hoare.lean      -- `KAT.HoareTriple` and the rules of Hoare logic
  Models/
    Rel.lean        -- `SetRel α α` is a KA / KAT (scoped instances in namespace `SetRel`)
    Bool.lean       -- every Kleene algebra is a KAT with the trivial tests `Bool`
  Examples/
    Basic.lean      -- sanity checks and small examples
```

## Design notes

**Kleene algebra.** We use Mathlib's `KleeneAlgebra` class unchanged.  Its order is the
semilattice order `a ≤ b ↔ a + b = b`, and the star axioms are Kozen's.  The file
`Kleene/Basic.lean` adds the theorems one actually needs when reasoning in KA:

* `KleeneAlgebra.isLeast_kstar_mul : IsLeast {x | a * x + b ≤ x} (a∗ * b)`
* `KleeneAlgebra.kstar_mul_comm : a∗ * a = a * a∗`
* `KleeneAlgebra.mul_kstar_eq_kstar_mul : a * (b * a)∗ = (a * b)∗ * a` (sliding)
* `KleeneAlgebra.kstar_add : (a + b)∗ = a∗ * (b * a∗)∗` (denesting)
* `KleeneAlgebra.kstar_mul_eq_mul_kstar_of_eq : a * x = x * b → a∗ * x = x * b∗` (bisimulation)
* `KleeneAlgebra.kstar_add_of_mul_le_mul : b * a ≤ a * b → (a + b)∗ = a∗ * b∗`

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

so that both Mathlib hierarchies are reused as they are.  `test` is not required to be
injective (exactly as in `relation-algebra`).  With `open scoped KAT`, `⌜b⌝` denotes `test b`.
Guarded commands are the usual encodings `ifThenElse b p q = ⌜b⌝ * p + ⌜bᶜ⌝ * q` and
`whileDo b p = (⌜b⌝ * p)∗ * ⌜bᶜ⌝`, and a Hoare triple is `HoareTriple b p c := ⌜b⌝ * p * ⌜cᶜ⌝ = 0`
(Kozen 2000), shown equivalent to `⌜b⌝ * p ≤ p * ⌜c⌝`.  All the rules of Hoare logic (skip,
sequencing, conditional, while, consequence, iteration) are theorems.

**Relations.** Mathlib's `SetRel α β` is reducibly `Set (α × β)`.  Because `Set` already has
scoped pointwise `+`/`*` instances in Mathlib, the ring-like instances on `SetRel α α` are
**scoped**: `open scoped SetRel` activates `Mul`, `Add`, `One`, `Zero`, `KStar`,
`IdemSemiring`, `IsQuantale`, `KleeneAlgebra` and `KleeneAlgebraWithTests (Set α) (SetRel α α)`.
Here `R * S = R ○ S`, `R + S = R ∪ S`, `R∗` is `Relation.ReflTransGen`, and the test `s : Set α`
is the sub-identity relation `SetRel.ofSet s = {(a, a) | a ∈ s}`.  All of Mathlib's `Set` and
`SetRel` API stays available; `SetRel.mul_def`, `SetRel.mem_kstar`,
`SetRel.kstar_eq_iUnion_pow`, ... translate between the vocabularies.

## Building

```
lake build
```

Toolchain: Lean `v4.30.0`, Mathlib `v4.30.0` (see `lean-toolchain`, `lakefile.toml`).
Use `lake exe cache get` to download Mathlib's prebuilt binaries before the first build.

## Comparison with `relation-algebra` (Rocq) and roadmap

Pous' library is much larger.  It has a *typed* (categorical, many-object) presentation of the
whole hierarchy from lattices to relation algebras with converse, models for relations,
languages, traces and matrices, and, crucially, reflexive decision procedures (`ka`, `kat`,
`ra`) that decide equalities in KA / KAT by translating to automata.

What is here is the *algebraic core* for the single-sorted case, on top of Mathlib.  Natural
next steps, roughly in order of usefulness:

1. **More models.** Matrices over a Kleene algebra (`Matrix n n K` is a KA; needed for
   automata arguments), `Set M` for a monoid `M` via `KleeneAlgebra.ofQuantale`, guarded strings.
2. **Converse / relation algebra proper.** `SetRel.inv` already exists in Mathlib; add a
   `KleeneAlgebraWithConverse` mixin and the laws of allegories / relation algebras.
3. **Typed (heterogeneous) KA.** `SetRel α β` for `α ≠ β`, mirroring Pous' many-object setting.
4. **Decision procedures.** A `kat` tactic deciding KAT equalities by normalisation to guarded
   strings / automata, either as a verified decision procedure or via `decide`-style reflection.
5. **Completeness.** Kozen's completeness theorems for KA (w.r.t. `Language`) and KAT (w.r.t.
   guarded strings), which would also be a natural Mathlib contribution.
