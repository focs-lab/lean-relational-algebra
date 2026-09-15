import RelationAlgebra.KAT.Hoare

/-!
# Hoare hypotheses and their elimination

A *Hoare hypothesis* is an assumption of the shape `z ≤ 0` (equivalently `z = 0`) in a Kleene
algebra with tests.  Hardin and Kozen showed that such hypotheses can be *eliminated*: to prove
`x = y` under `z ≤ 0` it suffices to prove the hypothesis-free identity

  `x + u * z * v = y + u * z * v`,

where `u` and `v` are *universal* expressions (in practice `α∗`, with `α` the sum of all the
actions occurring in the problem).  Consequently the Horn theory of KAT restricted to clauses
whose hypotheses are Hoare hypotheses reduces to the equational theory of KAT.

Moreover, several other common shapes of hypotheses can be *converted* into Hoare form —
`b = c` and `b ≤ c` between tests, `⌜b⌝ * p ≤ q * ⌜c⌝`, `q ≤ p * ⌜c⌝`, and Hoare triples — and
hypotheses of the shape `⌜c⌝ * p = ⌜c⌝` can be turned into a rewriting step.  Together this
covers a useful class of hypotheses; it is what the `hkat` tactic
(`RelationAlgebra.Decide.HKATTactic`) uses.

## Soundness and completeness

Following the vocabulary of `PORTING.md` §5, the two directions must be kept apart.

* **Soundness of the elimination step.** *Proved here*, and it is all the `hkat` tactic needs:
  `hoare_elim_eq` and `hoare_elim_le` below.  The argument is trivial — `z ≤ 0` forces `z = 0`,
  so the extra summands `u * z * v` vanish.  Every conversion lemma below is likewise proved
  from the KAT axioms, for an arbitrary `[KleeneAlgebra K]`.
* **Usefulness (Hardin–Kozen completeness) of the elimination step.** *Not proved here.*  That
  the resulting hypothesis-free identity is *provable* whenever the original implication is
  valid in all KATs is the Hardin–Kozen theorem, which this development does not formalise.  A
  failure of `hkat` therefore establishes nothing about the original goal, exactly as for `ka`
  and `kat`.

## Main declarations

* `KAT.hoare_elim_eq`, `KAT.hoare_elim_le`: elimination of a Hoare hypothesis.
* `KAT.test_eq_to_hoare`, `KAT.test_le_to_hoare`, `KAT.test_mul_le_to_hoare`,
  `KAT.mul_test_le_to_hoare`, `KAT.le_mul_test_to_hoare`, `KAT.le_test_mul_to_hoare`,
  `KAT.hoareTriple_to_hoare`, `KAT.le_zero_to_hoare`, `KAT.eq_zero_to_hoare`: conversions into
  Hoare form.
* `KAT.test_mul_eq_to_hoare`, `KAT.mul_test_eq_to_hoare`: the two hypotheses that are used as
  rewriting rules rather than as Hoare hypotheses.
* `KAT.add_le_zero`: merging two Hoare hypotheses into one.

## References

* [C. Hardin and D. Kozen, *On the elimination of hypotheses in Kleene algebra with tests*,
  TR2002-1879, Computer Science Department, Cornell University, October 2002][hardinkozen2002]
* [D. Kozen, *On Hoare logic and Kleene algebra with tests*][kozen2000]

This module ports the lemmas of `theories/kat_tac.v` in Damien Pous'
[`relation-algebra`](https://github.com/damien-pous/relation-algebra) library for Rocq/Coq
(`ab_to_hoare`, `ab'_to_hoare`, `bpqc_to_hoare`, `pbcq_to_hoare`, `qpc_to_hoare`,
`qcp_to_hoare`, `cp_c`, `pc_c`, `join_leq`, `elim_hoare_hypotheses_weq/leq`).
-/

open scoped Computability KAT

namespace KAT

/-! ### Elimination of Hoare hypotheses -/

section Elim

variable {K : Type*} [KleeneAlgebra K]

/-- Eliminating a Hoare hypothesis `z ≤ 0` from an equational goal: `u` and `v` are intended to
be universal expressions, but the statement holds for arbitrary `u` and `v`. -/
theorem hoare_elim_eq (u v z x y : K) (hz : z ≤ 0) (h : x + u * z * v = y + u * z * v) :
    x = y := by
  rw [le_antisymm hz zero_le, mul_zero, zero_mul, add_zero, add_zero] at h
  exact h

/-- Eliminating a Hoare hypothesis `z ≤ 0` from an inequational goal: `u` and `v` are intended
to be universal expressions, but the statement holds for arbitrary `u` and `v`. -/
theorem hoare_elim_le (u v z x y : K) (hz : z ≤ 0) (h : x ≤ y + u * z * v) : x ≤ y := by
  rwa [le_antisymm hz zero_le, mul_zero, zero_mul, add_zero] at h

/-- Merging two Hoare hypotheses into a single one. -/
theorem add_le_zero {x y : K} (hx : x ≤ 0) (hy : y ≤ 0) : x + y ≤ 0 := by
  rw [add_eq_sup]
  exact sup_le hx hy

/-- A hypothesis `x ≤ 0` already is a Hoare hypothesis.  This trivial restatement lets the
`hkat` tactic treat all the shapes it recognises uniformly. -/
theorem le_zero_to_hoare {x : K} (h : x ≤ 0) : x ≤ 0 := h

/-- A hypothesis `x = 0` is a Hoare hypothesis. -/
theorem eq_zero_to_hoare {x : K} (h : x = 0) : x ≤ 0 := h.le

end Elim

/-! ### Converting hypotheses into Hoare form -/

section Convert

variable {T K : Type*} [BooleanAlgebra T] [KleeneAlgebra K] [KAT T K]

/-- An equality between tests is a Hoare hypothesis (upstream `ab_to_hoare`). -/
theorem test_eq_to_hoare (b c : T) (h : b = c) : (⌜b ⊓ cᶜ⌝ + ⌜bᶜ ⊓ c⌝ : K) ≤ 0 := by
  subst h
  rw [inf_compl_eq_bot, compl_inf_eq_bot, test_bot, add_zero]

/-- An inequality between tests is a Hoare hypothesis (upstream `ab'_to_hoare`). -/
theorem test_le_to_hoare (b c : T) (h : b ≤ c) : (⌜b ⊓ cᶜ⌝ : K) ≤ 0 := by
  have hbc : b ⊓ cᶜ = ⊥ := by rw [← sdiff_eq, sdiff_eq_bot_iff]; exact h
  rw [hbc, test_bot]

/-- A commutation hypothesis `⌜b⌝ * p ≤ q * ⌜c⌝` yields a Hoare hypothesis
(upstream `bpqc_to_hoare`). -/
theorem test_mul_le_to_hoare (b c : T) (p q : K) (h : ⌜b⌝ * p ≤ q * ⌜c⌝) :
    ⌜b⌝ * p * ⌜cᶜ⌝ ≤ 0 :=
  calc ⌜b⌝ * p * ⌜cᶜ⌝ ≤ q * ⌜c⌝ * ⌜cᶜ⌝ := mul_le_mul_left h _
    _ = 0 := by rw [mul_assoc, test_mul_compl, mul_zero]

/-- A commutation hypothesis `p * ⌜b⌝ ≤ ⌜c⌝ * q` yields a Hoare hypothesis
(upstream `pbcq_to_hoare`). -/
theorem mul_test_le_to_hoare (b c : T) (p q : K) (h : p * ⌜b⌝ ≤ ⌜c⌝ * q) :
    ⌜cᶜ⌝ * p * ⌜b⌝ ≤ 0 := by
  rw [mul_assoc]
  calc ⌜cᶜ⌝ * (p * ⌜b⌝) ≤ ⌜cᶜ⌝ * (⌜c⌝ * q) := mul_le_mul_right h _
    _ = 0 := by rw [← mul_assoc, test_compl_mul, zero_mul]

/-- A hypothesis `q ≤ p * ⌜c⌝` yields a Hoare hypothesis (upstream `qpc_to_hoare`). -/
theorem le_mul_test_to_hoare (c : T) (p q : K) (h : q ≤ p * ⌜c⌝) : q * ⌜cᶜ⌝ ≤ 0 :=
  calc q * ⌜cᶜ⌝ ≤ p * ⌜c⌝ * ⌜cᶜ⌝ := mul_le_mul_left h _
    _ = 0 := by rw [mul_assoc, test_mul_compl, mul_zero]

/-- A hypothesis `q ≤ ⌜c⌝ * p` yields a Hoare hypothesis (upstream `qcp_to_hoare`). -/
theorem le_test_mul_to_hoare (c : T) (p q : K) (h : q ≤ ⌜c⌝ * p) : ⌜cᶜ⌝ * q ≤ 0 :=
  calc ⌜cᶜ⌝ * q ≤ ⌜cᶜ⌝ * (⌜c⌝ * p) := mul_le_mul_right h _
    _ = 0 := by rw [← mul_assoc, test_compl_mul, zero_mul]

/-- A hypothesis `⌜c⌝ * p = ⌜c⌝` is not turned into a Hoare hypothesis but into a *rewriting*
rule, replacing `p` by `⌜cᶜ⌝ * p + ⌜c⌝` (upstream `cp_c`). -/
theorem test_mul_eq_to_hoare (c : T) (p : K) (h : ⌜c⌝ * p = ⌜c⌝) : p = ⌜cᶜ⌝ * p + ⌜c⌝ := by
  conv_rhs => rw [← h, ← add_mul, test_compl_add, one_mul]

/-- A hypothesis `p * ⌜c⌝ = ⌜c⌝` is not turned into a Hoare hypothesis but into a *rewriting*
rule, replacing `p` by `p * ⌜cᶜ⌝ + ⌜c⌝` (upstream `pc_c`). -/
theorem mul_test_eq_to_hoare (c : T) (p : K) (h : p * ⌜c⌝ = ⌜c⌝) : p = p * ⌜cᶜ⌝ + ⌜c⌝ := by
  conv_rhs => rw [← h, ← mul_add, test_compl_add, mul_one]

/-! ### Relation to `KAT.HoareTriple` -/

variable {b c : T} {p : K}

/-- A Hoare triple is exactly a Hoare hypothesis: `{b} p {c}` iff `⌜b⌝ * p * ⌜cᶜ⌝ ≤ 0`. -/
theorem hoareTriple_iff_le_zero : HoareTriple b p c ↔ ⌜b⌝ * p * ⌜cᶜ⌝ ≤ 0 :=
  ⟨fun h ↦ (hoareTriple_def.1 h).le, fun h ↦ hoareTriple_def.2 (le_antisymm h zero_le)⟩

/-- A Hoare triple in the context is a Hoare hypothesis. -/
theorem hoareTriple_to_hoare (h : HoareTriple b p c) : ⌜b⌝ * p * ⌜cᶜ⌝ ≤ 0 :=
  hoareTriple_iff_le_zero.1 h

end Convert

end KAT
