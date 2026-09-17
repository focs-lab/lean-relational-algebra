# Relational algebra in Lean 4

Prove equations between programs and relations using **Kleene algebra (KA)** and
**Kleene algebra with tests (KAT)**. Built on Mathlib, this library provides proof-producing
tactics, typed and untyped completeness theorems, relational and matrix models, and Hoare rules.

This is a Lean translation and extension of **[Damien Pous’s relation-algebra library for
Rocq/Coq](https://github.com/damien-pous/relation-algebra)**. It is not a feature-for-feature
mirror; [PORTING.md](PORTING.md) records the coverage and remaining differences.

OpenAI Codex was used to translate and extend Damien Pous’s relation-algebra library from Rocq/Coq to Lean 4.

[User guide](docs/GUIDE.md) · [Examples](RelationAlgebra/Examples) ·
[Contributing](CONTRIBUTING.md) · [License](LICENSE)

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
[typed goals](RelationAlgebra/Examples/TypedDecide.lean) ·
[typed converse](RelationAlgebra/Examples/TypedRa.lean) ·
[Boolean and residual reasoning](RelationAlgebra/Examples/FullRa.lean) ·
[Paterson’s flowchart equivalence](RelationAlgebra/Examples/Paterson.lean).

<details>
<summary><strong>Use as a dependency in another project</strong></summary>

Use the same Lean toolchain (**Lean 4.30.0**) and add this entry to your `lakefile.toml`:

```toml
[[require]]
name = "relation_algebra"
git = "https://github.com/focs-lab/lean-relational-algebra.git"
rev = "b01130a20cf812c06580ab50adb444cf0268793e"
```

This pins a reviewed revision that includes the license and attribution files. Commit
the generated `lake-manifest.json` to keep the resolved dependencies reproducible.
Run `lake update`, `lake exe cache get`, and `lake build`, then import `RelationAlgebra` to use
the library.

</details>

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

Every successful tactic produces a kernel-checked proof. Algebraic completeness is proved
for KA and for typed and untyped KAT. **Search completeness is not proved:** `ka`, `kat`, and
`hkat` use fuel-bounded search, and `ra` is incomplete. A failed tactic does not show that a
goal is false. Try `kat 5000` or `hkat 10000` when the default fuel is insufficient.

`ka`, `kat`, and `ra` ignore hypotheses; `hkat` uses supported Hoare-style constraints.
Hoare triples express partial correctness, not termination. See the
[guide](docs/GUIDE.md#tactic-support) for assumptions, supported hypotheses, and resource limits.

## Models and applications

Use ordinary relations (`SetRel`, `RelCat`), rectangular matrices (`Matrix.Mat`),
computable finite relations (`FinRelCat`), relations on setoids (`SetoidRelCat`), or
languages of typed traces (`TraceCat`). The [model guide](docs/GUIDE.md#concrete-typed-models)
links to executable examples. The library also includes a free typed KAT with its
[universal property](RelationAlgebra/Examples/FreeKAT.lean).

Worked applications include [IMP](RelationAlgebra/Examples/Imp.lean),
[twelve compiler optimizations](RelationAlgebra/Examples/CompilerOpts.lean), and
[Paterson’s flowchart equivalence](RelationAlgebra/Examples/Paterson.lean).
Use the [library map](docs/GUIDE.md#library-guide) to find definitions and theorems.

## Credits and license

Damien Pous and the contributors to [relation-algebra](https://github.com/damien-pous/relation-algebra)
provided the central algebraic organization, proof developments, and automation approach.
Upstream also credits Christian Doczkal, Insa Stucke, and the Rocq development team;
Doczkal developed the finite-relation model. Pous’s
[documentation](https://perso.ens-lyon.fr/damien.pous/ra/) is a useful companion.
We also rely on the Lean and Mathlib contributors’ proof infrastructure and mathematics.

The translation and extensions are distributed under **LGPL-3.0-or-later**, following
upstream. See [LICENSE](LICENSE), the full [LGPL](COPYING.LESSER) and [GPL](COPYING) texts,
and the preserved [attribution and modification notice](NOTICE.md).
Dependencies retain their [own licenses](THIRD_PARTY.md).
[Mathematical references](docs/REFERENCES.md) identify the underlying papers.
