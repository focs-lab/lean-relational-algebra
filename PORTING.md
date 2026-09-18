# Porting `relation-algebra` to Lean 4 — coverage inventory

This file tracks coverage of Damien Pous' Rocq/Coq library
[`relation-algebra`](https://github.com/damien-pous/relation-algebra) by this Lean 4 / Mathlib
development.  It is the authoritative status document; `README.md` is the user-facing overview.

**Upstream revision used for comparison:** `2d2af3631929399bbac56f57b3e15302d8697e1c`
(2026-05-06), 49 modules in `theories/` (12 768 lines) plus `examples/` (1 022 lines) and an
OCaml plugin layer in `src/` (reification, `mrewrite`, `kat_dec`, `fold`).

**This port:** Lean 4 `v4.30.0`, Mathlib `v4.30.0`.

## How to read this file

Each row records what upstream provides, what exists here, what Mathlib already supplies, and
what is missing.  Coverage is classified by *kind*, because a class or tactic of the same name
does **not** establish equivalent coverage:

| Kind | Meaning |
|---|---|
| **D** | definitions / structures |
| **T** | proved theorems |
| **A** | executable algorithms (must compute, not just exist) |
| **X** | tactic support |
| **E** | application examples |

Status values: **done** (ported and verified), **partial** (some kinds covered, gaps listed),
**missing**, **n/a (Mathlib)** (upstream module exists only to build infrastructure Mathlib
already has), **n/a (design)** (upstream module solves a Coq-specific problem that does not
arise here).

Every "done" claim means: the Lean declaration exists, is proved without `sorry`/`admit`/new
axioms, and the file compiles in the project build.

---

## 1. Infrastructure upstream needs, that Mathlib supplies

These modules exist upstream to build basic infrastructure.  They are **not** port targets;
the Lean development uses Mathlib directly.  Listed for completeness so that the inventory
accounts for all 49 upstream modules.

| Upstream | Purpose | Lean replacement |
|---|---|---|
| `common.v`, `move.v` | tactics, utilities | Lean/Mathlib tactics; `move` is superseded by `ring_nf`-style normalisation and `gcongr` |
| `comparisons.v` | types with a comparison function | `DecidableEq`, `Ord`, `LinearOrder` |
| `positives.v` | binary positives as a `cmpType` | `ℕ`, `PNat` |
| `ordinal.v` | finite ordinals `ord n`, sets of them | `Fin n`, `Finset`, `Fintype` |
| `pair.v` | encoding `ord n × ord m` into `ord (n*m)` | `Fintype (α × β)`, `finProdFinEquiv` |
| `denum.v` | retracting countable types into positives | `Encodable`, `Denumerable` |
| `lset.v` | finite sets as lists | `List`, `Finset`, `Multiset` |
| `sups.v`, `sums.v` | finite joins/sums, ssreflect-style bigops | `Finset.sup`, `Finset.sum`, `iSup` |
| `prop.v` | `Prop` as a bounded distributive lattice | Mathlib's `Prop` order instances |
| `boolean.v` | `Bool` as a lattice and a flat monoid | `Bool.instBooleanAlgebra` for the lattice part; `Models/Bool.lean` uses `Bool` as the trivial algebra of tests.  Upstream's flat *monoid* structure on `Bool` is not reproduced |
| `powerfix.v` | bounded fixpoint operator (to avoid termination proofs) | `Nat`-fuelled recursion, used directly in `Decide/*` |
| `level.v` | Boolean tuples selecting a point in the algebraic hierarchy | **n/a (design)** — Lean's typeclass hierarchy plus Mathlib's `extends` does this natively; see §7 |
| `rewriting_aac.v` | bridge to `AAC_tactics` | no Lean counterpart needed; `ac_rfl`/`ring_nf` and `simp` cover the use cases |

`level.v` deserves a note: it is the heart of upstream's design, letting one theorem be stated
once for every sub-structure of residuated Kleene allegories.  In Lean the same effect is
obtained by stating theorems under the weakest typeclass assumptions, which is what this port
does.  **This is a design divergence, not a coverage gap**, but it means there is no file here
corresponding to `level.v`.

---

## 2. Algebraic hierarchy

| Upstream | Kinds | Lean counterpart | Mathlib provides | Status | Missing / notes |
|---|---|---|---|---|---|
| `lattice.v` | D,T | — | `Preorder`…`CompleteBooleanAlgebra`, `Order.*` | **n/a (Mathlib)** | the lattice structures themselves are all in Mathlib.  What has no counterpart is upstream's level-indexed presentation, which lets one lemma serve every sub-structure; see §7 |
| `monoid.v` (ordered monoid part) | D,T | `Kleene/Basic.lean`, `Typed.lean` | `Monoid`, `IdemSemiring`, `KleeneAlgebra` | **partial** | the untyped specialisation is complete.  Upstream states these laws *typed*, for `X n m`; only the subset needed downstream is reproved in the typed setting in `Typed.lean` |
| `monoid.v` (typed / category part) | D,T | `Typed.lean`, `TypedKAT.lean`, `TypedConverse.lean`, `TypedBoolean.lean`, `TypedResiduated.lean`, `TypedAllegory.lean` | `CategoryTheory.Category`, `End`, `SingleObj`, `RelCat` | **partial** | typed KA, KAT, converse, Boolean hom-sets, Dedekind, residuals and weak allegories, with `SingleObj`/`End` compatibility and relational/matrix models. The level-indexed hierarchy and weak residuated-allegory interface remain gaps |
| `monoid.v` (residuals) | D,T | `Residuated.lean`, `TypedResiduated.lean` | `IsQuantale` residuals `⇨ₗ`/`⇨ᵣ` | **done at the Kleene level** | untyped residuated semirings/KAs and genuinely typed residuals, without completeness. `ResiduatedKleeneCategory` uses the existing hom-set order; both adjunctions, variance, cancellation, composition and iteration laws are proved. Rectangular matrices use finite meets |
| `monoid.v` (allegory/Dedekind) | D,T | `Allegory.lean`, `TypedAllegory.lean` | — | **done for allegories; residual extension missing** | untyped and typed meet-enriched categories with converse and the modular law, deriving both modular laws and Dedekind. The typed interface requires no joins, bottom, top, complements, residuals, or star. Upstream's weak residuated-allegory layer is not ported |
| `kleene.v` | T | `Kleene/Basic.lean`, `Kleene/Iteration.lean`, `TypedIteration.lean` | `kstar_mono`, `kstar_idem`, `one_add_mul_kstar`, … | **partial overall; strict iteration done at the KA level** | `a⁺ := a * a∗`, typed endomorphism iteration, both unfolding and rectangular induction rules, monotonicity, constants, transitivity/idempotence, star interaction, sliding, bisimulation, union-of-closures, idempotent boundaries and converse. Relations and zero-one matrices have `TransGen` semantics. Upstream's statements at weaker levels and a full name-by-name audit of the remaining star API are separate |
| `kat.v` | D,T | `KAT/Defs.lean`, `KAT/Basic.lean`, `TypedKAT.lean` | `BooleanAlgebra` | **done** | both the untyped class and upstream's genuinely typed `KleeneCategoryWithTests`, with typed guarded commands and a typed Hoare triple relating *different* objects |
| `factors.v` | T | `Residuated.lean`, `TypedResiduated.lean` | — | **done at the Kleene/Boolean levels** | all nineteen statements have untyped and heterogeneous counterparts; see the correspondence below. The four top laws use `ResiduatedKleeneLattice` for scalars and `BooleanKleeneCategory` for typed hom-sets. This does not reproduce every weaker level-indexed assumption of upstream |
| `relalg.v` | D,T | `Converse.lean`, `Allegory.lean`, `Vectors.lean`, `TypedBoolean.lean`, `TypedAllegory.lean`, `TypedPoints.lean`, `TypedRelationPredicates.lean`, `Models/RelPoints.lean` | `StarRing`, lattice `IsAtom` | **covered at the interfaces below; partial at weaker levels** | typed relational predicates, vectors, points, algebraic atoms, minimality and point factorization; Boolean disjointness/complement laws and Kleene closure laws. `RelCat` maps are graphs of functions, points are singleton rows with nonempty targets, and algebraic atoms are lattice atoms/singleton pairs. The residual-only proof of `disjoint_vect_iff'` and upstream's full level-polymorphic generality remain unported |

### Typed predicates, points, and atoms correspondence

This maps the substantive points/atoms results in the
[pinned upstream `relalg.v`](https://github.com/damien-pous/relation-algebra/blob/2d2af3631929399bbac56f57b3e15302d8697e1c/theories/relalg.v)
to the `AllegoryCategory` namespace. Upstream's equality/setoid compatibility instances
are handled by Lean equality. The names here follow execution-order composition `≫`.

| Upstream | Lean counterpart |
| --- | --- |
| `is_univalent`, `is_mapping` | `Functional`, `IsMap` |
| `is_injective`, `is_total`, `is_surjective` | `Injective`, `Total`, `Surjective` |
| `is_nonempty`, `is_nonempty'` | `IsNonempty`, `IsNonemptyObject` |
| `nonempty_dom`, `nonempty_cod`, `nonempty_cnv` | `IsNonempty.dom`, `.cod`, `.converse` |
| `surjective_tx`, `tx_surjective`, `total_xt`, `xt_total` | `Surjective.top_comp`, `surjective_of_top_le`, `Total.comp_top`, `total_of_top_le` |
| `top_nonempty`, `vector'` | `top_comp_top`, `IsVector.comp_le` |
| `point_surjective`, `mapping_cnv` | `IsPoint.surjective`, `.converse_isMap` |
| `dot_univalent_cap`, `dot_cap_injective` | `Functional.comp_inf`, `Injective.inf_comp` |
| `univalent_antisym`, `surjective_injective_antisym` | `Functional.antisymm`, `Surjective.eq_of_le_injective` |
| `gen_point`, `leq_xyp`, `leq_pxq` | `IsPoint.extend`, `.le_comp_iff`, `.le_comp_iff_converse` |
| `point_lattice_atom` | `IsPoint.eq_of_nonempty_vector_le` |
| `atom_injective`, `atom_univalent`, `atom_cnv` | `IsAtom.injective`, `.functional`, `.converse` |
| `atom_of_points` (and auxiliary sandwich lemma) | `isAtom_of_points` (with a private helper) |
| `point_a_top`, `point_a'_top` | `IsAtom.row_isPoint`, `.column_isPoint` |
| `a_top_a_aux`, `a_top_a` | `IsAtom.row_inf_column`, `.comp_top_comp` |
| `atom_transitive`, `atom_mono` | `IsAtom.transitive`, `.comp_self_le_id` |
| `atom_points`, `atom_lattice_atom` | `IsAtom.exists_points`, `.eq_of_nonempty_le` |
| `disjoint_vect_iff`, `disjoint_vect_ext` | `IsVector.disjoint_iff`, `.disjoint_comp` |
| `dot_neg_inj`, `dot_neg_surj`, `dot_neg_point` | `Injective.compl_comp_le`, `Surjective.compl_comp_le`, `IsPoint.compl_comp` |
| `kernel_refl_antisym` | `kernel_eq_id` |
| reflexive, transitive, symmetric, antisymmetric, PER, preorder, order | `IsReflexive`, `IsTransitive`, `IsSymmetric`, `IsAntisymmetric`, `IsPer`, `IsPreorder`, `IsOrder`, with converse laws |
| irreflexive, linear, and closure instances | `IsIrreflexive`, `IsLinear`, `isPreorder_kstar`, `isTransitive_kplus`, `IsSymmetric.kstar`/`.kplus`, `IsReflexive.kplus`, `IsTransitive.kplus_eq`/`.kstar_eq` |

`TypedPoints` uses an allegory with top, without Boolean operations or iteration.
Its nonemptiness predicate quantifies over every pair of objects, exactly as upstream.
It is **not** defined as inequality with bottom, and algebraic `IsAtom` is **not**
defined as Mathlib's lattice atom. `Models/RelPoints` proves these equivalences for
heterogeneous relations, without assuming inhabited carriers. The regression suite
also exhibits a degenerate one-object allegory where an algebraic atom equals bottom.

Boolean and iteration additions use the canonical allegory of `RelationCategory`.
Thus the mathematical results are available, but some assume more structure than
their upstream level-indexed versions. In particular, this does not yet supply an
independent residuated-allegory interface or the residual-only `disjoint_vect_iff'`.

### Factors correspondence

The nineteen lemmas in the [pinned upstream `factors.v`](https://github.com/damien-pous/relation-algebra/blob/2d2af3631929399bbac56f57b3e15302d8697e1c/theories/factors.v)
map as follows. Scalar names are in `ResiduatedIdemSemiring` unless qualified; all typed
names are in `ResiduatedKleeneCategory`. The typed complement formulas hold for any
residual instance satisfying the adjunction, by uniqueness.

| Upstream | Scalar | Typed |
|---|---|---|
| `ldv_dotx` | `mul_ldiv` | `comp_ldiv` |
| `ldv_xdot` | `le_ldiv_mul` | `le_ldiv_comp` |
| `ldv_1x` | `one_ldiv` | `id_ldiv` |
| `ldv_0x` | `ResiduatedKleeneLattice.zero_ldiv` | `bot_ldiv` |
| `ldv_xt` | `ResiduatedKleeneLattice.ldiv_top` | `ldiv_top` |
| `str_ldv` | `ResiduatedKleeneAlgebra.kstar_ldiv_self` | `kstar_ldiv_self` |
| `ldv_rdv` | `ldiv_rdiv` | `ldiv_rdiv` |
| `ldv_unfold` | `ofRelationAlgebra_ldiv` | `ldiv_eq_compl` |
| `rdv_cancel` | `rdiv_mul_le` | `rdiv_comp_le` |
| `rdv_dotx` | `rdiv_mul` | `rdiv_comp` |
| `rdv_xdot` | `le_mul_rdiv` | `le_comp_rdiv` |
| `leq_rdv` | `le_iff_one_le_rdiv` | `le_iff_id_le_rdiv` |
| `rdv_xx` | `one_le_rdiv_self` | `id_le_rdiv_self` |
| `rdv_1x` | `rdiv_one` | `rdiv_id` |
| `rdv_0x` | `ResiduatedKleeneLattice.rdiv_zero` | `rdiv_bot` |
| `rdv_xt` | `ResiduatedKleeneLattice.top_rdiv` | `top_rdiv` |
| `rdv_trans` | `rdiv_mul_rdiv_le` | `rdiv_comp_rdiv_le` |
| `str_rdv` | `ResiduatedKleeneAlgebra.kstar_rdiv_self` | `kstar_rdiv_self` |
| `rdv_unfold` | `ofRelationAlgebra_rdiv` | `rdiv_eq_compl` |

---

## 3. Models

| Upstream | Kinds | Lean counterpart | Status | Missing / notes |
|---|---|---|---|---|
| `rel.v` (binary relations) | D,T | `Models/Rel.lean`, `Typed.lean`, `TypedKAT.lean`, `TypedConverse.lean`, `TypedBoolean.lean`, `TypedResiduated.lean` | **done at the KA/KAT/relation-algebra levels** | homogeneous `SetRel` and heterogeneous `RelCat`, including Boolean operations, converse, Dedekind and both residuals. `RelCat.Hom.mem_ldiv`/`mem_rdiv` give the universal-quantifier semantics |
| `lang.v` (word languages) | D,T | Mathlib `Language`, `Kleene/Complete.lean` | **done** | Mathlib supplies the `KleeneAlgebra`; this port adds `CompleteKleeneAlgebra` |
| `srel.v` (setoid relations) | D,T | `Models/SetoidRel.lean`, `Models/SetoidRelCategory.lean` | **done for the heterogeneous KA/KAT/relation model** | `HSetoidRel α β` respects two setoid equivalences; `SetoidRelCat` has typed KA/KAT, converse, Boolean/Dedekind structure and residuals. Identity is equivalence. The faithful, full interpretation into `RelCat` uses quotient types and preserves tests, star, Boolean operations and residuals; each hom-set is order-isomorphic. `squareOrderIso` connects the original homogeneous model |
| `fhrel.v` (finite relations) | D,T,A | `Models/FinRel.lean`, `Models/FinRelCategory.lean` | **done for the heterogeneous KA/KAT/relation model** | `FinRelCat` retains computable heterogeneous composition, converse, Boolean tests, star, strict iteration, residuals and decidable equality/inclusion. Both rectangular induction rules are proved. The full, faithful typed KAT interpretation into `RelCat` is an order isomorphism on each hom-set. Reuses the existing finite closure algorithm rather than MathComp `connect` |
| `traces.v` (finite traces) | D,T | `Models/Trace.lean`, `Models/TypedTrace.lean` | **done for the general typed model** | `TraceCat σ src tgt` has arbitrary object/action/state types, action-path typing, fusion composition, typed KA/KAT, Boolean hom-sets and restricted residuals with both adjunctions. Includes atom/action selection, restriction laws with typing hypotheses, and the one-object order isomorphism. Types constrain actions; shared states determine fusion, as upstream. No converse instance is asserted. This does not claim a full port of the trace-derivative API |
| `glang.v` (guarded string languages) | D,T | `Models/Trace.lean`, `Decide/GuardedString.lean`, `TypedKAT/GuardedString.lean`, `TypedKAT/LanguageModel.lean` | **done for the fixed-bound typed model** | `LanguageCat src tgt k` is a `KleeneCategoryWithTests` on the existing well-typed language hom-sets, with tests the sets of atoms of length `k`. Both rectangular induction rules and injectivity of tests are proved. `Term.eval_languageCat` identifies ordinary evaluation in this model with `Term.lang`. The expression quotient and its free-model universal property are implemented separately under `gregex.v` |
| `matrix.v` (typed matrices) | D,T | `Models/Matrix.lean`, `Models/MatrixExt.lean`, `Models/MatrixResidual.lean` | **done for the implemented hierarchy** | square and rectangular matrices, block star, complete-KA instance, computable star, tests, converse, Boolean/Dedekind structure and residuals. Rectangular residuals use finite meets over a `ResiduatedKleeneLattice`, with both adjunctions and empty dimensions covered. This does not reproduce upstream's weaker level-indexed hierarchy |
| `matrix_ext.v` | T | `Models/MatrixExt.lean` | **partial** | the rectangular induction and bisimulation rules, block-triangular stars, the complete-KA instance, a computable star for `Fin n`, diagonal tests and a matrix `KleeneCategory`.  Upstream's `mx_scal`/`scal_mx` homomorphism lemmas are not ported |
| `bmx.v` (Boolean matrices, rt-closure) | D,T | `Automata/ZeroOne.lean`, `Models/FinRel.lean` | **partial** | the characterisation is proved in the stronger form `Matrix.ofRel_kstar`: the star of a zero-one matrix over **any** Kleene algebra is the zero-one matrix of `Relation.ReflTransGen`.  Upstream's `bmx` type itself (square matrices over `bool` as a Kleene algebra) is not built; the closest object here is `FinRel α α` |
| `rmx.v` (matrices of regexes) | D,T | — | **not needed** | upstream uses regex-labelled matrices for its NFA layer; this port labels transitions by *relations* (`Matrix.ofRelLab`) instead, which is what the completeness proof needs |

---

## 4. Syntax, normalisation, rewriting

| Upstream | Kinds | Lean counterpart | Status | Missing / notes |
|---|---|---|---|---|
| `syntax.v` (typed monoid syntax) | D,T | `Decide/Term.lean`, `TypedKAT/Syntax.lean` | **partial** | typed KAT syntax and `TypedRA/Syntax.lean` for KA with converse are available; no residual syntax or level computation |
| `lsyntax.v` (lattice syntax) | D,T | `Decide/GuardedString.lean` (`BTerm`) | **partial** | Boolean terms are shared by the untyped checker and typed KAT syntax; no general lattice syntax |
| `normalisation.v` | D,T,A,X | `Decide/Normalise.lean`, `Decide/FullRALaws.lean`, `Decide/FullRATactic.lean`, `Decide/RaTactic.lean` | **partial** | all three commands support untyped and categorical KA/converse, intersection, complement, top, Boolean difference/implication and residuals, plus strict iteration. The richer path uses proved recursive rewrites and bounded structural inclusion (lattice, variance, adjunctions, cancellation, Dedekind/modular laws). The reflected KA core is unchanged. Full Boolean/residual expression syntax, canonicity and exact upstream algorithm parity are not supplied; the checker is incomplete |
| `rewriting.v` | X | — | **missing** | `mrewrite`: rewriting modulo associativity of composition |
| `untyping.v` | T | `TypedRA/Syntax.lean`, `TypedRA/Matrix.lean`, `TypedRA/Support.lean`, `TypedRA/Untyping.lean` | **done for semantic transport at KA with converse** | `Term.eval_le_of_erase_eval_le` and `eval_eq_of_erase_eval_eq` transfer universal untyped laws to parallel typed expressions. Both object and morphism universes are arbitrary. Upstream's level-indexed syntactic free-model results for weaker structures remain unported |
| `kat_untyping.v` | T | `TypedKAT/Syntax.lean`, `TypedKAT/GuardedString.lean`, `TypedKAT/Untyping.lean`, `TypedKAT/Semantics.lean` | **done for the semantic interface** | syntactic erasure, exact language correspondence, and action-path typing are proved. `Term.eval_eq_of_erase_eval_eq` and `eval_le_of_erase_eval_le` transport universally valid untyped laws to arbitrary typed KATs. `Term.semEq_iff_erase` and `semLE_iff_erase` expose preservation and reflection of semantic equality/inclusion for parallel expressions. Test valuations remain independent at each object; free-model packaging is under `gregex.v` |

---

## 5. Decision procedures and completeness

| Upstream | Kinds | Lean counterpart | Status | Missing / notes |
|---|---|---|---|---|
| `regex.v` | D,T | `Decide/Term.lean` | **partial** | terms, language semantics, soundness in complete KA |
| `ugregex.v` | D | `Decide/GuardedString.lean` (`KTerm`) | **partial** | |
| `ugregex_dec.v` | A,T | `Decide/Antimirov.lean`, `Decide/GuardedString.lean` | **done for its stated scope** | bisimulation search on partial derivatives, with *accepting-run* soundness; upstream likewise does not prove search completeness |
| `dfa.v` | D,T,A | `Automata/Det.lean`, `Automata/Lang.lean` | **partial** | `EpsNFA.IsDet`, the subset construction and the language of a deterministic automaton are done (D,T); the *executable* inclusion checker (A) is not — the `ka`/`kat` algorithms use derivatives instead |
| `nfa.v` | D,T,A | `Automata/Defs.lean`, `Automata/Thompson.lean` | **partial** | matricial NFAs over a Kleene algebra, Thompson's construction, epsilon-elimination, and the value theorem are done (D,T); no executable NFA layer (A) |
| `atoms.v` | D,T | `Decide/KATSound.lean` | **partial** | atoms of the free Boolean lattice, disjointness, join = `⊤`, decomposition — proved for the `kat` soundness argument |
| `gregex.v` (typed KAT syntax) | D,T | `TypedKAT/Syntax.lean`, `TypedKAT/GuardedString.lean`, `TypedKAT/Semantics.lean`, `TypedKAT/Free.lean`, `KAT/FreeTest.lean` | **done for the free KAT interface** | raw syntax, evaluation, object renaming, erasure, semantic equality/order, and the expression quotient are implemented. `FreeCat src tgt` is a typed KAT with free Boolean tests at each object. `FreeCat.existsUnique_lift` gives a unique homomorphic extension of any object map and independent test/action valuations. Equality uses all atom bounds; a single adequate bound suffices by completeness. Strict iteration is derived from composition and star; it does not add a raw syntax constructor |
| `ka_completeness.v` | T | `Decide/KACompleteness.lean` | **done** | `KleeneAlgebra.Term.completeness_eq`/`completeness_le`, for an arbitrary `[KleeneAlgebra K]` |
| `kat_completeness.v` | T | `KATCompleteness/`, `TypedKATCompleteness/` | **done for completeness** | equality and inclusion completeness are proved in both untyped and typed KATs. The typed theorem is `TypedKAT.Completeness.eval_eq_of_lang_eq`, with arbitrary object alphabets, categories, and test algebras; `eval_le_of_lang_subset` and both reflection lemmas accompany it. Upstream packages these statements through its free-model structure; the corresponding Lean quotient and universal property are now implemented under `gregex.v` |
| `kat_reification.v` | D,A | `Decide/KATReify.lean`, `Decide/TypedKATTactic.lean`, `Decide/TypedKATEnvironment.lean` | **done for KAT goals** | `kat` traverses `Expr`, reifies typed or untyped syntax, and builds valuations that evaluate definitionally to the goal. Typed actions carry endpoints and tests have separate environments at each object. The kernel checks proofs reconstructed through completeness |
| `kat_tac.v` (`ka`, `kat`, `hkat`) | X | `Decide/Tactic.lean` (`ka`), `Decide/KATTactic.lean` (`kat`), `Decide/HKATTactic.lean` (`hkat`) | **partial** | all three now work in an **arbitrary** Kleene algebra: `kat` and `hkat` synthesize `KleeneAlgebra`, not `CompleteKleeneAlgebra`.  `kat` and `hkat` also support typed categorical goals; the typed `ka` interface remains missing. Search remains fuel-bounded |

### Precise statement of the current tactic guarantees

This distinction matters and is easy to blur:

1. **Soundness when the checker accepts.** Proved. `KleeneAlgebra.Term.lang_eq_of_decideEq`
   and `KAT.KTerm.gs_eq_of_decideEq` turn an accepted certificate into an equality of
   languages / guarded-string sets; `…eval_eq_of_decideEq` transports it into the algebra.
2. **Completeness of the search.** *Not proved.* The exploration is fuel-bounded
   (`explore : ℕ → …`), so `false` means "invalid equation **or** fuel exhausted".  Upstream
   makes the same choice and says so explicitly in `ugregex_dec.v`.
3. **Algebraic completeness.** Proved for KA (`KleeneAlgebra.Term.completeness_eq`), untyped
   KAT (`KAT.Completeness.KTerm.eval_eq_of_gs_eq`), and typed KAT
   (`TypedKAT.Completeness.eval_eq_of_lang_eq`). The typed reflection lemmas can be applied
   to explicit expressions and are used by the typed branches of `kat` and `hkat`. `ka` still
   targets untyped goals. None of these completeness results assumes complete hom lattices,
   star-continuity or finite carriers.
4. **Termination and resource bounds.** The checkers terminate by construction (structural
   recursion on the fuel).  No bound relating fuel to term size is proved; upstream likewise
   uses a `powerfix`-style bounded fixpoint.

---

## 6. Applications

| Upstream | Kinds | Lean counterpart | Status |
|---|---|---|---|
| `examples/imp.v` | D,T,E | `Examples/Imp.lean` | **partial** — inductive big-step semantics, `bigStep_iff_denote`, `hoareCmd_iff`, the IMP Hoare rules, and nine program equivalences closed by `kat`.  **Not ported**: upstream's *specialised* assignment layer, namely a store type with named locations, the derived `x := e` notation, and the assignment lemmas `aff_stack`, `aff_idem`, `aff_comm`, `aff_ite`.  Concrete assignments are perfectly expressible as they stand — instantiate `σ` with a store and use `Cmd.assign (Function.update s x v)` — so what is missing is the definitions and the lemmas about them, not the expressive power. `Examples/Paterson/Model.lean` now supplies a separate five-cell assignment and substitution model for Paterson’s proof; the general IMP interface remains separate |
| `examples/compiler_opts.v` | T,E | `Examples/CompilerOpts.lean` | **done** — **all twelve** upstream optimisation statements are ported and proved, with the exact correspondence tabulated in the file.  The four that upstream proves with `mrewrite` (§3.2, §3.3, §3.4i, §3.4ii) are proved here by explicit associativity steps in `calc` plus `hkat`; for §3.4ii the route taken is shorter than upstream's.  Three of upstream's five preliminary lemmas are ported; `lemma_1'` and `lemma_1''` are unused and omitted |
| `examples/paterson.v` | D,T,E | `Examples/Paterson.lean`, `Examples/Paterson/` | **done** — `Paterson.paterson` proves the same S6A = S6E relational statement as Pous, for arbitrary `f`, `g`, and `P` on natural-valued five-cell stores. The development includes expression substitution, the four assignment laws, test commutation, agreement facts, and dead-store elimination through iteration. All assignment hypotheses are derived from updates. The larger `hkat` calls are factored into reusable abstract KAT lemmas. This is the two-scheme equivalence, not a general flowchart-to-expression translation. |

`KAT/Hypotheses.lean` ports the Hardin–Kozen hypothesis-conversion and elimination lemmas that
upstream's `hkat` uses, and `Decide/HKATTactic.lean` implements the tactic.  As upstream, only
the *soundness* of the elimination step is proved here; its *usefulness* rests on the
Hardin–Kozen theorem, which is not formalised, so a `hkat` failure establishes nothing.

---

## 7. Deliberate divergences from upstream

1. **No `level` machinery.** Upstream parameterises every structure by a tuple of Booleans so
   that one theorem covers all sub-structures.  Here, theorems are stated under the weakest
   Mathlib typeclass that supports them.  Consequence: some upstream theorems correspond to
   several Lean theorems, and vice versa.
2. **Untyped-first.** Upstream is typed (categorical) throughout, and derives untyped results
   via untyping theorems.  This port develops the untyped case first (which is what the
   tactics and applications use) and the typed case separately. Typed completeness is then
   obtained through finite matrices of morphisms, reusing the untyped theorem. Upstream proves
   typed completeness directly through its free syntax; see §8 for the construction here.
3. **Mathlib's `SetRel`, `Language`, `Matrix`, `star`, `CategoryTheory`** are reused instead
   of redefining `rel`, `lang`, `mx`, `cnv` and the typed monoid.
4. **No OCaml plugin.** Upstream's reification is an OCaml plugin; here it is a Lean
   metaprogram in `Decide/Tactic.lean` / `Decide/KATTactic.lean`.

---

## 8. Dependency-ordered plan for the remaining work

The order below follows actual dependencies, not the section order above.

```
DONE: bmx → automata (Thompson, eps-elim, determinisation, DFA languages, quotient)
        → KA completeness → `ka` for an arbitrary KleeneAlgebra
DONE: Residuated, Allegory, Trace/glang, SetoidRel, FinRel, MatrixExt, imp
DONE: untyped KAT completeness → `kat`/`hkat` for an arbitrary KleeneAlgebra
DONE: raw typed KAT syntax → typed guarded-string semantics and language erasure
DONE: finite morphism matrices + finite support → typed KAT completeness and reflection
DONE: dependent valuations + categorical reification → typed `kat`
DONE: finite matrix recovery + finite support → algebraic KAT untyping interface
DONE: typed Hoare conversions + action paths → typed `hkat`
DONE: typed language operations + bounded-atom tests → bundled guarded-string KAT model
DONE: semantic equality/order + free Boolean tests → expression quotient and universal property
DONE: concrete assignment laws + dead-store elimination + KAT → Paterson’s S6A = S6E
DONE: typed converse + row/column matrix recovery → KA-with-converse untyping
DONE: indexed reification + converse untyping → typed `ra`, `ra_normalise`, `ra_simpl`
DONE: typed Boolean hom-sets + Dedekind → Schröder and typed residuals
DONE: finite meets + scalar residuals → rectangular and square matrix residuals
DONE: recursive proved rewrites + structural inclusion → Boolean/residual `ra` support
DONE: composition + star → strict iteration, typed laws, nonempty paths, tactic preprocessing
DONE: finite and invariant relations → heterogeneous categories and quotient interpretation
DONE: arbitrary action-path typing + fusion → general typed traces and restricted residuals
DONE: weak typed allegories → relational predicates → points, atoms, minimality and factorization
DONE: typed predicates + Boolean/Kleene structure → disjointness, complement and closure laws

REMAINING, in dependency order:
  level-indexed syntactic untyping for structures below KA with converse
  full Boolean/residual expression syntax and its free-model/untyping results

INDEPENDENT GAPS found by the 2026-09-15 audit, each self-contained:
  weak residuated-allegory interface and remaining weaker-level predicate variants
  concrete assignment for IMP (upstream `imp.v`: `aff_stack`, `aff_comm`, `aff_ite`)
```

### KAT completeness, as proved here

`RelationAlgebra/KATCompleteness/` proves, for an **arbitrary** Kleene algebra with tests:

```
KAT.Completeness.KTerm.eval_eq_of_gs_eq :
  ∀ {T K} [BooleanAlgebra T] [KleeneAlgebra K] [KAT T K] (τ : ℕ → T) (ρ : ℕ → K) (k : ℕ)
    {e f : KAT.KTerm}, (∀ i ∈ e.tvars, i < k) → (∀ i ∈ f.tvars, i < k) →
    e.gs k = f.gs k → e.eval τ ρ = f.eval τ ρ
```

together with the inequational form `KTerm.eval_le_of_gs_subset` and the two reflection lemmas
`KAT.Completeness.eval_eq_of_decideEq` / `eval_le_of_decideLe` used by the tactics.  No
completeness, star-continuity, commutativity or finiteness assumption is placed on `K` or `T`.
`#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound`.

This is the untyped case. Typed completeness is also proved, in
`TypedKATCompleteness/Main.lean`; its construction is described below. The general algebraic
untyping interface is in `TypedKAT/Untyping.lean`. Both `kat` and `hkat` support typed goals.
Typed `hkat` uses the zero-conversion lemmas in `TypedKAT/Hypotheses.lean` and constructs
paths from the finite action graph: a zero hypothesis `z : A ⟶ B` contributes
`U X A ≫ z ≫ U B Y` to a goal in `X ⟶ Y`. Each contribution is proved zero, and typed
`kat` checks the augmented equation. This proves soundness; completeness of the path
construction and Hardin–Kozen elimination remains unformalised.

#### Why the obvious reduction fails, and what fixes it

An earlier revision of this file proposed sending a KAT term `e` to a matrix `Φ e` indexed by
the atoms, with entries *ordinary regular expressions over the action letters*.  That does not
work, and the star clause is not the only obstacle.  The three failures, since each one shapes
the construction that does work:

1. **Tests and the unit are not definable by regular expressions over action letters.**  If
   `Φ 1` is the diagonal matrix `D` with `D α α = ⌜α⌝`, then interpreting every primitive
   action as `0` makes every regular expression over the action letters evaluate to `0` or `1`,
   so none can denote a non-trivial restricted identity `⌜α⌝`.

2. **Adding one letter `t_α` per atom destroys faithfulness.**  The resulting language map is
   not injective on values: `1` and `∑ α, t_α` have different languages and the same value, as
   do `act p` and `act p * 1`.  Kleene algebra completeness concludes from equality of
   *languages*, which equality of guarded-string sets would then not deliver.

3. **Fusion is not concatenation in a free monoid.**  A guarded string with no actions is a
   single atom, the unit of fusion *at that atom*; guarded strings form a category with the
   atoms as objects, not a monoid.

The construction that works keeps the atoms in the matrix indices *and* records both endpoints
in each letter:

* the alphabet is the set of triples `⟨α, p, β⟩`, encoded as a natural number by
  `KAT.Completeness.code` (`RelationAlgebra/KATCompleteness/Encode.lean`);
* `KAT.Completeness.evalMat` interprets a term as a matrix indexed by the atoms, sending `p` to
  the matrix whose `(α, β)` entry is the single letter `⟨α, p, β⟩`, a test `b` to the 0/1
  diagonal matrix of the atoms satisfying `b`, and `1` to the **identity** matrix.  This is why
  obstruction 1 disappears: the unit is `1`, not `D`, and the atoms are visible in the alphabet;
* `KAT.Completeness.mem_langMat` (`LangCorrect.lean`) shows the `(α, β)` entry of that matrix is
  exactly the set of guarded strings of `e` that start at `α` and end at `β`, written as words.
  Fusion becomes concatenation because each letter carries its own source and target, which
  answers obstruction 3, and the encoding is injective on well-formed guarded strings, which
  answers obstruction 2.  Hence equal guarded-string semantics give equal language matrices
  (`langMat_eq_of_gs_eq`), hence equal matrices of *regular* languages (`regMat_eq_of_gs_eq`);
* `RelationAlgebra.RegLang.interp` (`RegLang.lean`) interprets a regular language in an
  arbitrary Kleene algebra.  Its well-definedness **is** the Kleene algebra completeness
  theorem already proved here: two terms with the same language have the same value everywhere.
  `Matrix.map_kstar` (`MapStar.lean`) shows it commutes with the matrix star, so it carries the
  regular-language matrix to the matrix `KAT.Completeness.valMat` over `K` that sends `p` to
  `⌜α⌝ * ρ p * ⌜β⌝`;
* finally the value of the term is recovered from that matrix by sandwiching it between the row
  and column vectors of atoms, `KAT.Completeness.sandwich_valMat` (`Recovery.lean`):
  `eval τ ρ e = U * valMat e * V` with `U α = V α = ⌜α⌝`.  The induction runs on
  `U * V = 1`, `V * U = D`, and the invariant `D * X = D * X * D` satisfied by everything in
  the image of the interpretation; the star case is `sandwich_kstar`, proved from the
  rectangular induction rule for matrices, with no star-continuity.
  The invariant says that `D * X` is unchanged by right multiplication by `D`; it does not
  assert `D * X = X` or `X * D = X`.  For the identity matrix it reduces to `D = D * D`,
  which holds even when `D ≠ 1`.

#### Typed completeness through finite matrices of morphisms

`TypedKAT.Completeness.eval_eq_of_lang_eq` states, for an arbitrary object alphabet `I`,
category `C` with `[KleeneCategory C] [TypedKAT C T]`, object map `o : I → C`, test valuations
`τ : ∀ X, ℕ → T (o X)`, and typed action valuation `ρ`:

```lean
(e : TypedKAT.Term src tgt X Y).lang k = f.lang k →
  e.eval o τ ρ = f.eval o τ ρ
```

The theorem additionally requires every test variable in `e` and `f` to be below `k`.
The object map need not be injective, and the same test variable number may have different
values at different objects. Neither the object alphabet, the category, the hom-sets nor the
test algebras need to be finite. The inclusion form and the equality/inequality reflection
lemmas are in the same module.

The proof has four parts:

1. `Term.restrict` reduces a pair of expressions to its finite set of mentioned objects.
   `erase_restrict` and `eval_restrict` prove that this preserves erasure and evaluation.
2. `KleeneCategory.HomMatrix o` has entries `o i ⟶ o j`. Finite joins define multiplication;
   state elimination defines the star. Both rectangular invariant principles are proved
   directly from the categorical axioms. Families of tests give diagonal matrix tests.
3. `eval_row` shows that the source row of an erased expression's matrix interpretation
   contains its original typed value at the target and bottom elsewhere. Other rows may
   contain identities, including after a star; no claim equates a local identity with the
   global matrix identity.
4. Untyped KAT completeness equates the two matrix interpretations. Reading their common
   source/target entry and undoing restriction gives the typed equation.

This route proves typed completeness without first packaging the free syntax as a KAT model.
That packaging remains useful for upstream API parity, but is not a prerequisite for this
proof. The matrix Kleene-algebra instance, recovery theorem, support theorem, completeness
theorems, and reflection lemmas all report only `propext`, `Classical.choice`, and `Quot.sound`
under `#print axioms`.

#### Algebraic KAT untyping

`TypedKAT.Term.eval_eq_of_erase_eval_eq` and `eval_le_of_erase_eval_le` take a law about
`e.erase` and `f.erase` that holds for every untyped Boolean test algebra, Kleene algebra,
and pair of valuations. They conclude equality or order between the typed evaluations of
`e, f : Term src tgt X Y`, for arbitrary object maps and independent test valuations.

The proof instantiates the law in matrices over the expressions' finite object support,
uses `eval_entry`, and undoes restriction. It does not call the derivative checker or need
an atom bound. In Lean, the quantified model universes include the object-index universe,
as required by the matrix and test-family types. No finite-object or continuity assumption
is imposed on the caller. Equality in one particular model is not a sufficient premise.

#### Untyping with converse

`TypedRA.Term` adds endpoint-reversing converse to the typed KA syntax. Its untyping
interfaces quantify over every `[KleeneAlgebra K] [StarRing K]` and action valuation,
then conclude equality or inequality in any `KleeneCategoryWithConverse`.

The matrix construction reuses the finite heterogeneous Kleene algebra. Transpose plus
entrywise converse gives its `StarRing` instance. `Term.eval_rows` simultaneously recovers
the source row and the converse of the target column. Converse swaps those invariants;
iteration preserves each by the existing row-star lemma. The matrix identity remains the
full identity, including entries away from the declared source. Finite-support restriction
then removes the finiteness assumption on syntactic objects.

This proves semantic transport at the KA-with-converse level of Pous' `untyping.v`.
It does not construct a converse expression quotient or assert upstream's level-indexed
syntactic results for weaker structures. For KA/converse goals, typed `ra` reuses `RaTerm`'s existing normalization and its
kernel-checked correctness through this theorem. Boolean/residual goals use a separate
path of typed theorem applications and simplifier rewrites, so they need no richer untyping
claim. This path normalizes under the extra operations, then tries structural inclusion
rules with backtracking (at most 16 normalization passes and 4096 rule attempts). It follows
Pous' normalization/partial-inclusion approach without claiming algorithm identity or completeness.

**Verification criteria** for each remaining item (what would justify moving it to *done*):

| Item | Criterion |
|---|---|
| `bmx` | **met**: `Matrix.ofRel_kstar` |
| automata | **met**: `RelationAlgebra.Automata.value_thompson` |
| KA completeness | **met**: `KleeneAlgebra.Term.completeness_eq`; `#print axioms` reports only `propext, Classical.choice, Quot.sound` |
| `ka` for arbitrary KA | **met**: `RelationAlgebra/Examples/Decide.lean` proves `(a+b)∗ = a∗*(b*a∗)∗` and seven other identities with only `[KleeneAlgebra K]` in scope |
| KAT completeness (untyped) | **met**: `KAT.Completeness.KTerm.eval_eq_of_gs_eq`, with only `[BooleanAlgebra T] [KleeneAlgebra K] [KAT T K]`; `RelationAlgebra/Examples/Decide.lean` closes `KAT.HoareTriple ⊤ (KAT.whileDo b p) bᶜ` by `kat` and `KAT.HoareTriple b p∗ b` from `KAT.HoareTriple b p b` by `hkat` over an abstract carrier; `#print axioms` reports only `propext, Classical.choice, Quot.sound` |
| Typed syntax and semantics | **met for the raw syntax milestone**: `TypedKAT.Term.eval`, `Term.lang`, `Term.strings_lang`, and `Term.pathTyped_of_mem_erase`; examples reject invalid composition and iteration and check heterogeneous relational evaluation. Free-model packaging is separate; typed completeness is supplied by `TypedKATCompleteness/Main.lean` |
| KAT completeness (typed) | **met**: `TypedKAT.Completeness.eval_eq_of_lang_eq` and `eval_le_of_lang_subset`, with no finite-object or continuity assumptions. `Examples/TypedCompleteness.lean` checks equality, inequality, loops, independent test valuations, object identifications, negative certificates, and the necessary variable bounds |
| Algebraic KAT untyping | **met for evaluation transport**: both equality and inequality interfaces are proved without atom bounds or fuel. `Examples/Untyping.lean` covers independent tests, object identifications, arbitrary test indices, infinite higher-universe object alphabets, concrete relations, and rejection of a single-interpretation premise |
| Typed `kat` | **met**: `Examples/TypedDecide.lean` proves heterogeneous sliding, test identities, guarded inequalities, conditionals, and loops through `kat`, with abstract categories and concrete relations. Regressions also cover binders, multiple goals, insufficient fuel, and invalid identities |
| Typed `hkat` | **met for the tactic**: `Examples/TypedHypotheses.lean` covers heterogeneous sequencing, loops, Boolean and guarded constraints, endomorphism rewrites, concrete relation constructors, binders, multiple goals, and invalid consequences. Zero hypotheses are composed with well-typed action paths before being joined. Search and elimination completeness remain unproved |
| Typed guarded-string model | **met at fixed atom bound**: `LanguageCat src tgt k` has `Category`, `KleeneCategory`, and `TypedKAT` instances. `Term.eval_languageCat` proves exact agreement with `Term.lang`. `Examples/LanguageModel.lean` covers heterogeneous rules and tactics, canonical evaluation, membership and fusion, malformed atoms, zero test variables, and actual iteration |
| `hkat` | **met for the tactic**: `RelationAlgebra/Decide/HKATTactic.lean` closes `⌜b⌝*p ≤ p*⌜b⌝ ⊢ ⌜b⌝*p∗ ≤ p∗*⌜b⌝`, which `kat` alone provably cannot (checked with `fail_if_success kat`), merges several hypotheses, and leaves other goals untouched.  Not met for Hardin–Kozen completeness, which is not formalised |
| Typed converse untyping | **met for semantic transport**: equations and inequalities in arbitrary categories, with `Examples/ConverseUntyping.lean` covering converse around iteration, infinite higher-universe objects, object identification, and rejection of a single-model premise |
| `ra`/`ra_normalise`/`ra_simpl` | **met for Boolean/residual support and partial inclusion**: `Examples/FullRa.lean` covers recursive normalization, abstract and concrete models, readable remaining goals, binders, multiple goals, and rejection of invalid laws. The richer proof path uses direct rewrites; no full-syntax untyping, canonicity or search completeness is claimed |
| Typed Boolean/residual interfaces | **met**: `RelationCategory` has typed Dedekind/Schröder laws; `ResiduatedKleeneCategory` has both adjunctions and all nineteen `factors.v` counterparts. `Examples/TypedResidual.lean` covers the abstract interfaces, heterogeneous relational membership and `End` compatibility |
| Matrix residuals | **met**: `Matrix.le_lres_iff` and `le_rres_iff`, generic `ResiduatedKleeneLattice` coefficients, `Matrix.Mat` and square instances, pointwise Boolean/Dedekind structure over a relation algebra, empty dimensions and complement-formula compatibility in `Examples/MatrixResidual.lean` |
| Strict iteration | **met at the KA level**: scalar and typed laws in `Kleene/Iteration.lean` and `TypedIteration.lean`, nonempty-path semantics in `SetRel`, `RelCat` and `Matrix.ofRel_kplus`, plus proved preprocessing in all six tactics. `Examples/Iteration.lean` checks rectangular induction/sliding, hypotheses with strict iteration, binders, multiple goals, model semantics, empty matrices, insufficient fuel and invalid identities |
| Heterogeneous concrete models | **met**: `Examples/FiniteRelations.lean`, `Examples/SetoidRelations.lean`, and `Examples/TypedTraces.lean` cover typed tactics, finite computations, quotient semantics, setoid identity, trace fusion and typing, restricted complements/residuals, and rejection of mismatched endpoints |
| `imp` | big-step semantics defined inductively, proved equal to the KAT denotation, and Hoare rules derived |
| `paterson` | **met**: `Paterson.paterson` and `Paterson.terminates_iff`; regressions cover arbitrary interpretations, nontermination with a false predicate, immediate termination with a true predicate, a concrete one-iteration execution, and the dead-store side conditions |

---

## 9. Optional work toward broader upstream parity

The build is green (`lake build`, zero warnings), no `sorry`/`admit`/new axioms anywhere, and
every headline theorem depends only on `propext`, `Classical.choice`, `Quot.sound`.

The KA/KAT release milestone is complete. These are separately scoped extensions, not
prerequisites for using or releasing the library:

1. **Weaker relation-algebra interfaces** — the independent residuated-allegory layer
   and remaining weaker-level predicate variants. Typed allegories, predicates, points,
   atoms and their minimality/factorization results are now available, alongside typed
   Boolean/Dedekind/residual interfaces and matrix residuals.
2. **Syntax and automation foundations** — full Boolean/residual expression syntax,
   and weaker level-indexed untyping. Search completeness is a further research extension;
   upstream also leaves derivative-search completeness unproved. `ra` already handles the extra
   operations by direct proved rewrites and bounded structural inclusion. IMP's specialized
   assignments and the other independent gaps in §8 can be developed separately.

## 10. Development history

The dated implementation and validation record is in [docs/DEVELOPMENT_HISTORY.md](docs/DEVELOPMENT_HISTORY.md).
