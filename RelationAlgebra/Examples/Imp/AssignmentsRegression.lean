/- SPDX-License-Identifier: LGPL-3.0-or-later
Copyright (c) 2026 Umang Mathur and contributors. See LICENSE and NOTICE.md. -/
import RelationAlgebra.Examples.Imp.Assignments
import RelationAlgebra.Decide.HKATTactic

/-!
# IMP assignment examples and side-condition regressions

The examples use the existing operational semantics and KAT interpretation. The
negative cases prove non-equivalence by evaluating stores, rather than relying on
failure of a tactic. The countdown example also proves termination, separately from
its Hoare partial-correctness specification.
-/

open IMP
open scoped IMP KAT SetRel Computability
universe u v w

namespace Examples.ImpAssignments

inductive Loc | x | y | z deriving DecidableEq
open Loc

abbrev Mem := Store Loc ℕ

/-- An expression reads the old value of the location being assigned. -/
example (s : Mem) : BigStep (x ::= (fun s ↦ s x + 1)) s (Store.update x (s x + 1) s) :=
  (Assignment.bigStep_iff _ _ _ _ _).mpr rfl

example : ((x ::= (fun s : Mem ↦ s x + 1)) ;; (x ::= (fun s ↦ s x + 1))).Equiv
    (x ::= (fun s ↦ s x + 2)) := by
  simpa [Store.esubst, Assignment.esubst, Assignment.modify, Function.comp_def,
    Nat.add_assoc] using Store.aff_stack x (fun s : Mem ↦ s x + 1) (fun s ↦ s x + 1)

example : ((x ::= (fun _ : Mem ↦ 7)) ;; (x ::= (fun _ ↦ 7))).Equiv
    (x ::= (fun _ ↦ 7)) := Store.aff_idem _ _ (Store.fresh_const _ _)

/-- The second expression reads `x`, so it must change when moved before the write. -/
theorem dependent_reordering :
    ((x ::= (fun _ : Mem ↦ 1)) ;; (y ::= (fun s ↦ s x))).Equiv
      ((y ::= (fun _ ↦ 1)) ;; (x ::= (fun _ ↦ 1))) := by
  simpa only [Store.esubst_var] using
    Store.aff_comm x y (fun _ : Mem ↦ 1) (fun s ↦ s x) (by decide) (Store.fresh_const _ _)

example : ((x ::= (fun s : Mem ↦ s z)) ;; (y ::= (fun s ↦ s z))).Equiv
    ((y ::= (fun s ↦ s z)) ;; (x ::= (fun s ↦ s z))) :=
  Store.aff_commute _ _ _ _ (by decide) (Store.fresh_var (by decide))
    (Store.fresh_var (by decide))

example (s t : Mem) :
    BigStep ((x ::= (fun _ ↦ 1)) ;; (y ::= (fun s ↦ s x))) s t ↔
      BigStep ((y ::= (fun _ ↦ 1)) ;; (x ::= (fun _ ↦ 1))) s t :=
  dependent_reordering.bigStep_iff s t

example (e : Mem → ℕ) : Store.subst x e {s | s x = s y} = {s | e s = s y} := by
  ext s
  simp [Store.subst, Assignment.subst, Assignment.modify, Store.update_of_ne,
    show y ≠ x by decide]

example (n : ℕ) : HoareCmd {s : Mem | s x = n}
    (x ::= (fun s ↦ s x + 1)) {s | s x = n + 1} := by
  apply (Assignment.hoare_iff _ _ _ _ _).mpr
  intro s hs
  change Store.update x (s x + 1) s x = n + 1
  simpa only [Store.update_same] using congrArg (· + 1) hs

/-- The named assignment rule gives precisely the weakest precondition. -/
example (loc : Loc) (e : Mem → ℕ) (b d : Set Mem) :
    HoareCmd b (loc ::= e) d ↔ b ≤ Store.subst loc e d := Assignment.hoare_iff _ _ _ _ _

/-- Assignment hypotheses feed into the existing KAT automation. -/
example (n : ℕ) : KAT.HoareTriple {s : Mem | s y = n}
    (x ::= (fun s ↦ s x + 1)).denote∗ {s | s y = n} := by
  have h : KAT.HoareTriple {s : Mem | s y = n}
      (x ::= (fun s ↦ s x + 1)).denote {s | s y = n} := by
    apply (Assignment.hoare_iff _ _ _ _ _).mpr
    intro s hs
    change Store.update x (s x + 1) s y = n
    simpa only [Store.update_of_ne _ _ (show y ≠ x by decide)] using hs
  hkat

/-- Guard substitution is needed even when either branch contains a loop. -/
example (b : Set Mem) (e : Mem → ℕ) (p q : Cmd Mem) :
    ((x ::= e) ;; Cmd.ite b (Cmd.whileDo b p) q).Equiv
      (Cmd.ite (Store.subst x e b) ((x ::= e) ;; Cmd.whileDo b p) ((x ::= e) ;; q)) :=
  Store.aff_ite _ _ _ _ _

section Generality

-- Infinite location types and arbitrary value/result universes require no finite enumeration.
example {L : Type u} {V : Type v} {B : Type w} [DecidableEq L]
    (x : L) (e : Store L V → V) (f : Store L V → B) (hf : Store.Fresh x f) :
    Store.esubst x e f = f := Assignment.esubst_of_fresh _ _ hf

example (x : ℕ) : (x ::= (fun s : Store ℕ Bool ↦ s x)).Equiv Cmd.skip := Store.assign_self x

-- Empty stores do not introduce an Inhabited or Nonempty requirement.
example : Store Empty Empty := Empty.elim

example (x : Unit) (e : Store Unit Empty → Empty) :
    ((x ::= e) ;; (x ::= e)).Equiv (x ::= e) := by
  apply Store.aff_idem
  intro _ s
  exact (s ()).elim

-- Moving through a conditional needs no overwrite or commutation assumption.
example {L : Type u} {V : Type v} {S : Type w}
    (update : L → V → S → S) (x : L) (e : S → V) (b : Set S) (p q : Cmd S) :
    (Cmd.seq (Assignment.cmd update x e) (Cmd.ite b p q)).Equiv
      (Cmd.ite (Assignment.subst update x e b)
        (Cmd.seq (Assignment.cmd update x e) p) (Cmd.seq (Assignment.cmd update x e) q)) :=
  Assignment.aff_ite _ _ _ _ _ _

end Generality

/-! ## A terminating loop over named stores -/

def clearX : Cmd Mem := Cmd.whileDo {s | 0 < s x} (x ::= (fun s ↦ s x - 1))

/-- Clear `x` while preserving the value of `y`. -/
theorem clearX_spec (n : ℕ) :
    HoareCmd {s | s y = n} clearX {s | s x = 0 ∧ s y = n} := by
  have hbody : HoareCmd ({s : Mem | 0 < s x} ⊓ {s | s y = n})
      (x ::= (fun s ↦ s x - 1)) {s | s y = n} := by
    apply (Assignment.hoare_iff _ _ _ _ _).mpr
    intro s hs
    change Store.update x (s x - 1) s y = n
    simpa only [Store.update_of_ne _ _ (show y ≠ x by decide)] using hs.2
  refine HoareCmd.whileDo' hbody fun s hs ↦ ?_
  exact ⟨Nat.eq_zero_of_not_pos hs.1, hs.2⟩

/-- Termination is proved by induction on `x`, independently of the Hoare rules. -/
theorem clearX_run (s : Mem) : BigStep clearX s (Store.update x 0 s) := by
  generalize hn : s x = n
  induction n generalizing s with
  | zero =>
    have he : Store.update x 0 s = s := by
      change Function.update s x 0 = s
      rw [← hn, Function.update_eq_self]
    rw [he]
    exact BigStep.whileDo_false (by change ¬ 0 < s x; omega)
  | succ n ih =>
    have hbody : BigStep (x ::= (fun s : Mem ↦ s x - 1)) s (Store.update x n s) := by
      apply (Assignment.bigStep_iff _ _ _ _ _).mpr
      simp [hn]
    have hrest := ih (Store.update x n s) (Store.update_same _ _ _)
    rw [Store.update_twice] at hrest
    exact BigStep.whileDo_true (by change 0 < s x; omega) hbody hrest

example (s t : Mem) (h : BigStep clearX s t) : t x = 0 ∧ t y = s y :=
  (hoareCmd_iff _ _ _).mp (clearX_spec (s y)) s t rfl h

/-! ## The side conditions cannot be dropped -/

private def zeroStore : Mem := fun _ ↦ 0

private theorem seq_assign_eq {f g h k : Mem → Mem}
    (he : (Cmd.seq (Cmd.assign f) (Cmd.assign g)).Equiv
      (Cmd.seq (Cmd.assign h) (Cmd.assign k))) : g ∘ f = k ∘ h := by
  apply Cmd.assign_equiv_iff.mp
  exact (Cmd.assign_seq f g).symm.trans (he.trans (Cmd.assign_seq h k))

/-- Increment reads its target, so repeating it is not redundant. -/
theorem increment_not_idempotent :
    ¬ ((x ::= (fun s : Mem ↦ s x + 1)) ;; (x ::= (fun s ↦ s x + 1))).Equiv
      (x ::= (fun s ↦ s x + 1)) := by
  intro he
  have hf := Cmd.assign_equiv_iff.mp ((Cmd.assign_seq _ _).symm.trans he)
  have hx := congrFun (congrFun hf zeroStore) x
  simp [Assignment.modify, Store.update, zeroStore] at hx

/-- Swapping dependent writes without substitution changes the result. -/
theorem dependent_writes_do_not_commute :
    ¬ ((x ::= (fun _ : Mem ↦ 1)) ;; (y ::= (fun s ↦ s x))).Equiv
      ((y ::= (fun s ↦ s x)) ;; (x ::= (fun _ ↦ 1))) := by
  intro he
  have hy := congrFun (congrFun (seq_assign_eq he) zeroStore) y
  simp [Assignment.modify, Store.update, zeroStore] at hy

/-- Distinct locations alone do not make the first expression fresh for the second. -/
theorem reordering_needs_freshness :
    ¬ ((x ::= (fun s : Mem ↦ s y)) ;; (y ::= (fun _ ↦ 1))).Equiv
      ((y ::= (Store.esubst x (fun s : Mem ↦ s y) (fun _ ↦ 1))) ;;
        (x ::= (fun s ↦ s y))) := by
  intro he
  have hx := congrFun (congrFun (seq_assign_eq he) zeroStore) x
  simp [Assignment.modify, Store.esubst, Assignment.esubst, Store.update,
    Function.comp_def, zeroStore] at hx

/-- Fresh constant expressions still cannot be swapped when the locations coincide. -/
theorem reordering_needs_distinct_locations :
    ¬ ((x ::= (fun _ : Mem ↦ 1)) ;; (x ::= (fun _ ↦ 2))).Equiv
      ((x ::= (fun _ ↦ 2)) ;; (x ::= (fun _ ↦ 1))) := by
  intro he
  have hx := congrFun (congrFun (seq_assign_eq he) zeroStore) x
  simp [Assignment.modify, Store.update] at hx

/-- Testing the old guard after moving the write chooses the wrong branch. -/
theorem distributing_needs_guard_substitution :
    ¬ ((x ::= (fun _ : Mem ↦ 1)) ;;
      Cmd.ite {s | s x = 1} (y ::= (fun _ ↦ 1)) (y ::= (fun _ ↦ 2))).Equiv
    (Cmd.ite {s | s x = 1}
      ((x ::= (fun _ ↦ 1)) ;; (y ::= (fun _ ↦ 1)))
      ((x ::= (fun _ ↦ 1)) ;; (y ::= (fun _ ↦ 2)))) := by
  intro he
  have hrun : BigStep ((x ::= (fun _ : Mem ↦ 1)) ;;
      Cmd.ite {s | s x = 1} (y ::= (fun _ ↦ 1)) (y ::= (fun _ ↦ 2)))
      zeroStore (Store.update y 1 (Store.update x 1 zeroStore)) :=
    BigStep.seq (BigStep.assign _ _)
      (BigStep.ite_true (Store.update_same _ _ _) (BigStep.assign _ _))
  have hbad := he.bigStep_iff _ _ |>.mp hrun
  rw [bigStep_iff_denote, Cmd.denote_ite, mem_ifThenElse] at hbad
  rcases hbad with ⟨hb, _⟩ | ⟨_, hb⟩
  · exact (by decide : ¬ zeroStore x = 1) hb
  · change ∃ s, s = Store.update x 1 zeroStore ∧
      Store.update y 1 (Store.update x 1 zeroStore) = Store.update y 2 s at hb
    obtain ⟨s, rfl, ht⟩ := hb
    have hy := congrFun ht y
    simp [Store.update] at hy

end Examples.ImpAssignments
