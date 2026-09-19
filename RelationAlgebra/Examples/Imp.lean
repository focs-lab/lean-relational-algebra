import RelationAlgebra.KAT.Hoare
import RelationAlgebra.Models.Rel
import RelationAlgebra.Decide.KATTactic

/-!
# IMP: while programs, their big-step semantics, and Hoare logic from KAT

This file ports Damien Pous' `examples/imp.v` from the Rocq/Coq library
[`relation-algebra`](https://github.com/damien-pous/relation-algebra) to Lean 4.

We formalise the IMP language (whose programs are also known as *while programs*).  Commands
are given

* a **big-step operational semantics** `IMP.BigStep`, defined as an inductive relation exactly
  as in a textbook, and
* a **denotational semantics** `IMP.Cmd.denote` into the relational Kleene algebra with tests,
  mapping `skip` to `1`, sequencing to `*`, conditionals to `KAT.ifThenElse` and loops to
  `KAT.whileDo`,

and the two are proved to agree (`IMP.bigStep_iff_denote`).  Program equivalences are then
proved by the `kat` decision procedure, and the rules of Hoare logic for partial correctness
are derived from the abstract KAT rules of `RelationAlgebra.KAT.Hoare`.  The payoff is
`IMP.hoareCmd_iff`: the algebraically derived triples say exactly what the operational
semantics says they should.

## Assignments and upstream conventions

The core command `Cmd.assign (f : σ → σ)` accepts any state update. Import
`RelationAlgebra.Examples.Imp.Assignments` for upstream's named-location interface:
`Assignment.cmd update x e` updates `x` with the value of `e` in the old state.
That module supplies semantic substitution and freshness, all four upstream assignment
laws, and functional stores `Store Loc Val` with scoped `x ::= e` notation. Values may
have any type; upstream fixes natural numbers. The Hoare assignment rule uses predicate
preimage as the weakest precondition, both here and in the named-location interface.

Upstream states the `while` rule of the big-step semantics by re-using sequencing; we use the
equivalent three-premise textbook rule, which makes the induction slightly more direct.

## References

* Damien Pous, `examples/imp.v` in
  [`relation-algebra`](https://github.com/damien-pous/relation-algebra).
* [D. Pous, *Kleene Algebra with Tests and Coq Tools for While Programs*][pous2013]
* [D. Kozen, *On Hoare logic and Kleene algebra with tests*,
  Trans. Computational Logic 1(1):60–76, 2000][kozen2000]
-/

open scoped Computability KAT SetRel

namespace IMP

variable {σ : Type*}

/-! ## Syntax -/

/-- Commands of the IMP language, over an abstract state type `σ`.  Tests are subsets of the
state space, i.e. semantic predicates, so that the tests of the relational Kleene algebra with
tests can be used directly. -/
inductive Cmd (σ : Type*) where
  /-- `skip`: the command that does nothing. -/
  | skip : Cmd σ
  /-- `assign f`: replace the current state `s` by `f s`.  This abstracts `x := e`. -/
  | assign : (σ → σ) → Cmd σ
  /-- `seq p q`: run `p`, then run `q`. -/
  | seq : Cmd σ → Cmd σ → Cmd σ
  /-- `ite b p q`: run `p` if the test `b` holds in the current state, and `q` otherwise. -/
  | ite : Set σ → Cmd σ → Cmd σ → Cmd σ
  /-- `whileDo b p`: run `p` repeatedly, as long as the test `b` holds. -/
  | whileDo : Set σ → Cmd σ → Cmd σ

/-! ## Big-step semantics -/

/-- Big-step operational semantics: `BigStep c s t` means that running the command `c` from the
state `s` terminates in the state `t`. -/
inductive BigStep : Cmd σ → σ → σ → Prop where
  /-- `skip` leaves the state unchanged. -/
  | skip (s : σ) : BigStep Cmd.skip s s
  /-- `assign f` moves from `s` to `f s`. -/
  | assign (f : σ → σ) (s : σ) : BigStep (Cmd.assign f) s (f s)
  /-- `seq p q` runs `p` from `s` to some intermediate state `u`, then `q` from `u` to `t`. -/
  | seq {p q : Cmd σ} {s u t : σ} :
      BigStep p s u → BigStep q u t → BigStep (Cmd.seq p q) s t
  /-- If the guard holds, the conditional behaves like its `then` branch. -/
  | ite_true {b : Set σ} {p q : Cmd σ} {s t : σ} :
      s ∈ b → BigStep p s t → BigStep (Cmd.ite b p q) s t
  /-- If the guard fails, the conditional behaves like its `else` branch. -/
  | ite_false {b : Set σ} {p q : Cmd σ} {s t : σ} :
      s ∉ b → BigStep q s t → BigStep (Cmd.ite b p q) s t
  /-- If the guard fails, the loop terminates immediately. -/
  | whileDo_false {b : Set σ} {p : Cmd σ} {s : σ} :
      s ∉ b → BigStep (Cmd.whileDo b p) s s
  /-- If the guard holds, the loop runs its body once and then loops again. -/
  | whileDo_true {b : Set σ} {p : Cmd σ} {s u t : σ} :
      s ∈ b → BigStep p s u → BigStep (Cmd.whileDo b p) u t → BigStep (Cmd.whileDo b p) s t

/-! ## KAT denotation -/

namespace Cmd

/-- The denotation of a command as a binary relation on states, written in the language of
Kleene algebra with tests. -/
def denote : Cmd σ → SetRel σ σ
  | .skip => 1
  | .assign f => {p | p.2 = f p.1}
  | .seq p q => p.denote * q.denote
  | .ite b p q => KAT.ifThenElse b p.denote q.denote
  | .whileDo b p => KAT.whileDo b p.denote

@[simp] theorem denote_skip : (Cmd.skip : Cmd σ).denote = 1 := rfl

@[simp] theorem denote_assign (f : σ → σ) :
    (Cmd.assign f).denote = {p : σ × σ | p.2 = f p.1} := rfl

@[simp] theorem denote_seq (p q : Cmd σ) : (p.seq q).denote = p.denote * q.denote := rfl

@[simp] theorem denote_ite (b : Set σ) (p q : Cmd σ) :
    (Cmd.ite b p q).denote = KAT.ifThenElse b p.denote q.denote := rfl

@[simp] theorem denote_whileDo (b : Set σ) (p : Cmd σ) :
    (Cmd.whileDo b p).denote = KAT.whileDo b p.denote := rfl

/-- Two commands are *equivalent* when they have the same denotation.  By
`IMP.bigStep_iff_denote` this is the same as having the same big-step behaviour. -/
def Equiv (p q : Cmd σ) : Prop := p.denote = q.denote

theorem equiv_def {p q : Cmd σ} : p.Equiv q ↔ p.denote = q.denote := Iff.rfl

end Cmd

/-! ## Membership in guarded relations

Three unfolding lemmas relating the KAT operations of the relational model to their obvious
set-theoretic readings.  They carry all the work of the agreement theorem below. -/

theorem mem_test_mul {b : Set σ} {P : SetRel σ σ} {s t : σ} :
    s ~[(⌜b⌝ : SetRel σ σ) * P] t ↔ s ∈ b ∧ s ~[P] t := by
  simp only [SetRel.mem_mul, SetRel.test_def, SetRel.mem_ofSet]
  constructor
  · rintro ⟨u, ⟨rfl, hs⟩, hu⟩
    exact ⟨hs, hu⟩
  · rintro ⟨hs, h⟩
    exact ⟨s, ⟨rfl, hs⟩, h⟩

theorem mem_mul_test {b : Set σ} {P : SetRel σ σ} {s t : σ} :
    s ~[P * (⌜b⌝ : SetRel σ σ)] t ↔ s ~[P] t ∧ t ∈ b := by
  simp only [SetRel.mem_mul, SetRel.test_def, SetRel.mem_ofSet]
  constructor
  · rintro ⟨u, hu, rfl, ht⟩
    exact ⟨hu, ht⟩
  · rintro ⟨h, ht⟩
    exact ⟨t, h, rfl, ht⟩

theorem mem_ifThenElse {b : Set σ} {P Q : SetRel σ σ} {s t : σ} :
    s ~[KAT.ifThenElse b P Q] t ↔ (s ∈ b ∧ s ~[P] t) ∨ (s ∉ b ∧ s ~[Q] t) := by
  rw [KAT.ifThenElse_def]
  simp only [SetRel.mem_add, mem_test_mul, Set.mem_compl_iff]

theorem mem_whileDo {b : Set σ} {P : SetRel σ σ} {s t : σ} :
    s ~[KAT.whileDo b P] t ↔
      Relation.ReflTransGen (fun x y ↦ x ∈ b ∧ x ~[P] y) s t ∧ t ∉ b := by
  have hrel : (fun x y ↦ x ~[(⌜b⌝ : SetRel σ σ) * P] y) = fun x y ↦ x ∈ b ∧ x ~[P] y := by
    funext x y
    exact propext mem_test_mul
  rw [KAT.whileDo_def, mem_mul_test, SetRel.mem_kstar, hrel, Set.mem_compl_iff]

/-! ## Agreement between the two semantics -/

/-- **The two semantics coincide.**  A command relates `s` to `t` in the big-step operational
semantics exactly when the pair `(s, t)` belongs to its KAT denotation. -/
theorem bigStep_iff_denote (c : Cmd σ) (s t : σ) : BigStep c s t ↔ s ~[c.denote] t := by
  constructor
  · intro h
    induction h with
    | skip s => exact SetRel.mem_one.2 rfl
    | assign f s => exact rfl
    | seq _ _ ih₁ ih₂ => exact ⟨_, ih₁, ih₂⟩
    | ite_true hb _ ih => exact mem_ifThenElse.2 (Or.inl ⟨hb, ih⟩)
    | ite_false hb _ ih => exact mem_ifThenElse.2 (Or.inr ⟨hb, ih⟩)
    | whileDo_false hb => exact mem_whileDo.2 ⟨Relation.ReflTransGen.refl, hb⟩
    | whileDo_true hb _ _ ih₁ ih₂ =>
      obtain ⟨hstar, hnb⟩ := mem_whileDo.1 ih₂
      exact mem_whileDo.2 ⟨hstar.head ⟨hb, ih₁⟩, hnb⟩
  · induction c generalizing s t with
    | skip =>
      intro h
      have h' : s = t := h
      subst h'
      exact BigStep.skip s
    | assign f =>
      intro h
      have h' : t = f s := h
      subst h'
      exact BigStep.assign f s
    | seq p q ihp ihq =>
      rintro ⟨u, h₁, h₂⟩
      exact BigStep.seq (ihp _ _ h₁) (ihq _ _ h₂)
    | ite b p q ihp ihq =>
      intro h
      rw [Cmd.denote_ite, mem_ifThenElse] at h
      rcases h with ⟨hb, h⟩ | ⟨hb, h⟩
      · exact BigStep.ite_true hb (ihp _ _ h)
      · exact BigStep.ite_false hb (ihq _ _ h)
    | whileDo b p ihp =>
      intro h
      rw [Cmd.denote_whileDo, mem_whileDo] at h
      obtain ⟨hstar, hnb⟩ := h
      induction hstar using Relation.ReflTransGen.head_induction_on with
      | refl => exact BigStep.whileDo_false hnb
      | head hsu _ ih => exact BigStep.whileDo_true hsu.1 (ihp _ _ hsu.2) ih

/-! ## Program equivalences

These are the equivalences of upstream `imp.v`, all discharged by the `kat` decision
procedure after unfolding the denotation. `kat` works in arbitrary Kleene algebras with
tests; these examples use the relational interpretation of IMP commands. -/

section Equivalences

variable (b c : Set σ) (p q r : Cmd σ)

/-- Unrolling a loop once. -/
example : (Cmd.whileDo b p).Equiv (Cmd.ite b (Cmd.seq p (Cmd.whileDo b p)) Cmd.skip) := by
  simp only [Cmd.equiv_def, Cmd.denote_whileDo, Cmd.denote_ite, Cmd.denote_seq, Cmd.denote_skip]
  kat

/-- Folding a loop: iterating the body once more inside the loop changes nothing. -/
example : (Cmd.whileDo b p).Equiv (Cmd.whileDo b (Cmd.seq p (Cmd.whileDo b p))) := by
  simp only [Cmd.equiv_def, Cmd.denote_whileDo, Cmd.denote_seq]
  kat

/-- Denesting nested loops with the same guard. -/
example : (Cmd.whileDo b (Cmd.whileDo b p)).Equiv (Cmd.whileDo b p) := by
  simp only [Cmd.equiv_def, Cmd.denote_whileDo]
  kat

/-- Folding a loop, upstream's version. -/
example :
    (Cmd.whileDo b (Cmd.seq p (Cmd.ite b p Cmd.skip))).Equiv (Cmd.whileDo b p) := by
  simp only [Cmd.equiv_def, Cmd.denote_whileDo, Cmd.denote_seq, Cmd.denote_ite, Cmd.denote_skip]
  kat

/-- A conditional whose branches agree is that branch. -/
example : (Cmd.ite b p p).Equiv p := by
  simp only [Cmd.equiv_def, Cmd.denote_ite]
  kat

/-- The guard of a conditional still holds in its `then` branch. -/
example : (Cmd.ite b (Cmd.ite b p q) r).Equiv (Cmd.ite b p r) := by
  simp only [Cmd.equiv_def, Cmd.denote_ite]
  kat

/-- A conditional distributes over a following command. -/
example : (Cmd.seq (Cmd.ite b p q) r).Equiv (Cmd.ite b (Cmd.seq p r) (Cmd.seq q r)) := by
  simp only [Cmd.equiv_def, Cmd.denote_ite, Cmd.denote_seq]
  kat

/-- Eliminating dead code: the guard is false right after the loop. -/
example : (Cmd.seq (Cmd.whileDo b p) (Cmd.ite b q r)).Equiv (Cmd.seq (Cmd.whileDo b p) r) := by
  simp only [Cmd.equiv_def, Cmd.denote_seq, Cmd.denote_whileDo, Cmd.denote_ite]
  kat

/-- Eliminating dead code, with a disjunctive guard. -/
example :
    (Cmd.seq (Cmd.whileDo (c ⊔ b) p) (Cmd.ite b q r)).Equiv
      (Cmd.seq (Cmd.whileDo (c ⊔ b) p) r) := by
  simp only [Cmd.equiv_def, Cmd.denote_seq, Cmd.denote_whileDo, Cmd.denote_ite]
  kat

end Equivalences

/-! ## Hoare logic for IMP -/

/-- The partial-correctness Hoare triple `{b} c {d}` for an IMP command, defined as the KAT
triple for its denotation. -/
def HoareCmd (b : Set σ) (c : Cmd σ) (d : Set σ) : Prop := KAT.HoareTriple b c.denote d

theorem hoareCmd_def {b d : Set σ} {c : Cmd σ} :
    HoareCmd b c d ↔ KAT.HoareTriple b c.denote d := Iff.rfl

/-- In the relational model, the KAT encoding of a Hoare triple says exactly what it should. -/
theorem hoareTriple_setRel_iff {b d : Set σ} {R : SetRel σ σ} :
    KAT.HoareTriple b R d ↔ ∀ s t, s ∈ b → s ~[R] t → t ∈ d := by
  rw [KAT.hoareTriple_def, SetRel.zero_def, Set.eq_empty_iff_forall_notMem]
  constructor
  · intro h s t hs hst
    by_contra hd
    exact h (s, t) (mem_mul_test.2 ⟨mem_test_mul.2 ⟨hs, hst⟩, hd⟩)
  · rintro h ⟨s, t⟩ hmem
    obtain ⟨hst, hd⟩ := mem_mul_test.1 hmem
    obtain ⟨hs, hst⟩ := mem_test_mul.1 hst
    exact hd (h s t hs hst)

/-- **Soundness and completeness of the algebraic triple w.r.t. the operational semantics.**
The KAT-derived rules below are therefore rules about `BigStep`. -/
theorem hoareCmd_iff (b : Set σ) (c : Cmd σ) (d : Set σ) :
    HoareCmd b c d ↔ ∀ s t, s ∈ b → BigStep c s t → t ∈ d := by
  rw [hoareCmd_def, hoareTriple_setRel_iff]
  simp only [bigStep_iff_denote]

namespace HoareCmd

/-- `{b} skip {b}`. -/
theorem skip (b : Set σ) : HoareCmd b Cmd.skip b := KAT.HoareTriple.skip b

/-- The assignment axiom: the weakest precondition of `assign f` for `d` is `f ⁻¹' d`. -/
theorem assign (f : σ → σ) (d : Set σ) : HoareCmd (f ⁻¹' d) (Cmd.assign f) d := by
  rw [hoareCmd_iff]
  rintro s t hs h
  cases h
  exact hs

/-- Sequencing. -/
theorem seq {b c d : Set σ} {p q : Cmd σ} (hp : HoareCmd b p c) (hq : HoareCmd c q d) :
    HoareCmd b (Cmd.seq p q) d := KAT.HoareTriple.seq hp hq

/-- Conditional. -/
theorem ite {b c d : Set σ} {p q : Cmd σ} (hp : HoareCmd (b ⊓ c) p d)
    (hq : HoareCmd (bᶜ ⊓ c) q d) : HoareCmd c (Cmd.ite b p q) d :=
  KAT.HoareTriple.ifThenElse hp hq

/-- The `while` rule: an invariant `i` preserved by the guarded body survives the loop, and the
guard fails on exit. -/
theorem whileDo {b i : Set σ} {p : Cmd σ} (h : HoareCmd (b ⊓ i) p i) :
    HoareCmd i (Cmd.whileDo b p) (bᶜ ⊓ i) := KAT.HoareTriple.whileDo h

/-- Rule of consequence. -/
theorem consequence {b b' c c' : Set σ} {p : Cmd σ} (hb : b' ≤ b) (h : HoareCmd b p c)
    (hc : c ≤ c') : HoareCmd b' p c' := KAT.HoareTriple.consequence hb h hc

/-- Strengthening the precondition. -/
theorem strengthen_pre {b b' c : Set σ} {p : Cmd σ} (hb : b' ≤ b) (h : HoareCmd b p c) :
    HoareCmd b' p c := KAT.HoareTriple.strengthen_pre hb h

/-- Weakening the postcondition. -/
theorem weaken_post {b c c' : Set σ} {p : Cmd σ} (h : HoareCmd b p c) (hc : c ≤ c') :
    HoareCmd b p c' := KAT.HoareTriple.weaken_post h hc

/-- The usual packaged `while` rule, with an explicit invariant and a final weakening. -/
theorem whileDo' {b i a : Set σ} {p : Cmd σ} (h : HoareCmd (b ⊓ i) p i) (ha : bᶜ ⊓ i ≤ a) :
    HoareCmd i (Cmd.whileDo b p) a := (whileDo h).weaken_post ha

/-- Every terminating run of a loop ends with its guard false. -/
theorem whileDo_exit (b : Set σ) (p : Cmd σ) : HoareCmd Set.univ (Cmd.whileDo b p) bᶜ :=
  KAT.HoareTriple.whileDo_exit b p.denote

end HoareCmd

/-! ## A worked example

The countdown loop `while 0 < x do x := x - 1` over the state space `ℤ`, with the
partial-correctness specification `{0 ≤ x} countdown {x = 0}` proved from the derived rules. -/

section Countdown

/-- The body of the countdown loop: `x := x - 1`. -/
def decr : Cmd ℤ := Cmd.assign fun x ↦ x - 1

/-- The countdown loop `while 0 < x do x := x - 1`. -/
def countdown : Cmd ℤ := Cmd.whileDo {x : ℤ | 0 < x} decr

/-- `{0 ≤ x} countdown {x = 0}`, by the derived `while`, assignment and consequence rules. -/
theorem countdown_spec : HoareCmd {x : ℤ | 0 ≤ x} countdown {x : ℤ | x = 0} := by
  have hbody : HoareCmd ({x : ℤ | 0 < x} ⊓ {x : ℤ | 0 ≤ x}) decr {x : ℤ | 0 ≤ x} := by
    refine HoareCmd.strengthen_pre (fun x hx ↦ ?_) (HoareCmd.assign (fun x ↦ x - 1) _)
    obtain ⟨h₁, -⟩ := hx
    have h₁' : (0 : ℤ) < x := h₁
    change (0 : ℤ) ≤ x - 1
    omega
  refine HoareCmd.whileDo' hbody fun x hx ↦ ?_
  obtain ⟨h₁, h₂⟩ := hx
  have h₁' : ¬ (0 : ℤ) < x := h₁
  have h₂' : (0 : ℤ) ≤ x := h₂
  change x = 0
  omega

/-- The same specification, read back through the big-step semantics. -/
theorem countdown_bigStep (s t : ℤ) (hs : 0 ≤ s) (h : BigStep countdown s t) : t = 0 :=
  (hoareCmd_iff _ _ _).1 countdown_spec s t hs h

end Countdown

end IMP
