/- SPDX-License-Identifier: LGPL-3.0-or-later
Lean translation and extensions, 2026-09-18. See LICENSE and NOTICE.md. -/
import RelationAlgebra.Examples.Imp

/-!
# Named-variable assignments for IMP

The assignment layer of Damien Pous's `examples/imp.v`, at revision
`2d2af3631929399bbac56f57b3e15302d8697e1c`. `Assignment` works with an arbitrary
memory-update function and explicit overwrite/commutation laws, as upstream does.
The value type is arbitrary rather than fixed to natural numbers.

`Store Loc Val = Loc → Val` supplies concrete stores and proves those update laws.
`open scoped IMP` enables `x ::= e` and `p ;; q`; right-hand sides are functions of
the old store. This syntax expands to the existing `Cmd.assign` and `Cmd.seq`.
Substitution is semantic (function composition / predicate preimage), and freshness
means invariance under every update of a location, not a syntactic approximation.
-/

open scoped SetRel KAT
universe u v w z

namespace IMP

namespace Cmd
variable {σ : Type u} {p q : Cmd σ}

/-- Denotational equivalence is exactly agreement of all terminating executions. -/
theorem equiv_iff_bigStep : p.Equiv q ↔ ∀ s t, BigStep p s t ↔ BigStep q s t := by
  constructor
  · intro h s t
    rw [bigStep_iff_denote, bigStep_iff_denote, show p.denote = q.denote from h]
  · intro h
    apply Set.ext
    rintro ⟨s, t⟩
    exact (bigStep_iff_denote p s t).symm.trans ((h s t).trans (bigStep_iff_denote q s t))

theorem Equiv.bigStep_iff (h : p.Equiv q) (s t : σ) : BigStep p s t ↔ BigStep q s t :=
  equiv_iff_bigStep.mp h s t

/-- Sequential deterministic updates are ordinary function composition. -/
theorem assign_seq (f g : σ → σ) : (seq (assign f) (assign g)).Equiv (assign (g ∘ f)) := by
  ext ⟨s, t⟩
  change (∃ u, u = f s ∧ t = g u) ↔ t = g (f s)
  simp

/-- Deterministic updates are equivalent exactly when their state functions agree. -/
theorem assign_equiv_iff {f g : σ → σ} : (assign f).Equiv (assign g) ↔ f = g := by
  constructor
  · intro h
    funext s
    have hf : (s, f s) ∈ (assign f).denote := rfl
    rw [show (assign f).denote = (assign g).denote from h] at hf
    exact hf
  · rintro rfl
    rfl

end Cmd

namespace Assignment

variable {Loc : Type u} {Val : Type v} {σ : Type w} {β : Type z}
variable (update : Loc → Val → σ → σ)

/-- Evaluate the right-hand side in the old state, then update one location. -/
def modify (x : Loc) (e : σ → Val) (s : σ) : σ := update x (e s) s

/-- A named assignment is an existing IMP command. -/
def cmd (x : Loc) (e : σ → Val) : Cmd σ := Cmd.assign (modify update x e)

/-- Substitute an assignment into an expression, allowing any result type. -/
def esubst (x : Loc) (e : σ → Val) (f : σ → β) : σ → β := f ∘ modify update x e

/-- Substitute an assignment into a test by taking its preimage. -/
def subst (x : Loc) (e : σ → Val) (b : Set σ) : Set σ := (modify update x e) ⁻¹' b

/-- The expression is unaffected by changing the given location to any value. -/
def Fresh (x : Loc) (e : σ → β) : Prop := ∀ (v : Val) (s : σ), e (update x v s) = e s

@[simp] theorem esubst_apply (x : Loc) (e : σ → Val) (f : σ → β) (s : σ) :
    esubst update x e f s = f (update x (e s) s) := rfl

@[simp] theorem mem_subst (x : Loc) (e : σ → Val) (b : Set σ) (s : σ) :
    s ∈ subst update x e b ↔ update x (e s) s ∈ b := Iff.rfl

@[simp] theorem subst_compl (x : Loc) (e : σ → Val) (b : Set σ) :
    subst update x e bᶜ = (subst update x e b)ᶜ := rfl

@[simp] theorem subst_inf (x : Loc) (e : σ → Val) (b c : Set σ) :
    subst update x e (b ⊓ c) = subst update x e b ⊓ subst update x e c := rfl

theorem fresh_const (x : Loc) (c : β) : Fresh update x (fun _ : σ ↦ c) := fun _ _ ↦ rfl

theorem esubst_of_fresh {x : Loc} (e : σ → Val) {f : σ → β} (hf : Fresh update x f) :
    esubst update x e f = f := funext fun s ↦ hf (e s) s

@[simp] theorem mem_denote (x : Loc) (e : σ → Val) (s t : σ) :
    s ~[(cmd update x e).denote] t ↔ t = update x (e s) s := Iff.rfl

@[simp] theorem bigStep_iff (x : Loc) (e : σ → Val) (s t : σ) :
    BigStep (cmd update x e) s t ↔ t = update x (e s) s := by
  rw [bigStep_iff_denote, mem_denote]

/-- The assignment rule is also an exact weakest-precondition characterization. -/
theorem hoare_iff (x : Loc) (e : σ → Val) (b d : Set σ) :
    HoareCmd b (cmd update x e) d ↔ b ≤ subst update x e d := by
  rw [hoareCmd_iff]
  simp only [bigStep_iff]
  constructor
  · intro h s hs
    exact h s _ hs rfl
  · intro h s t hs he
    subst t
    exact h hs

theorem hoare (x : Loc) (e : σ → Val) (d : Set σ) :
    HoareCmd (subst update x e d) (cmd update x e) d := (hoare_iff _ _ _ _ _).mpr le_rfl

/-- Upstream `aff_stack`: two writes to one location collapse by substitution. -/
theorem aff_stack
    (overwrite : ∀ (x : Loc) (a b : Val) (s : σ), update x b (update x a s) = update x b s)
    (x : Loc) (e f : σ → Val) :
    (Cmd.seq (cmd update x e) (cmd update x f)).Equiv
      (cmd update x (esubst update x e f)) := by
  have h := Cmd.assign_seq (modify update x e) (modify update x f)
  have he : modify update x f ∘ modify update x e = modify update x (esubst update x e f) := by
    funext s
    exact overwrite x (e s) (f (update x (e s) s)) s
  simpa only [he] using h

/-- Upstream `aff_idem`: a repeated assignment is redundant when its expression is fresh. -/
theorem aff_idem
    (overwrite : ∀ (x : Loc) (a b : Val) (s : σ), update x b (update x a s) = update x b s)
    (x : Loc) (e : σ → Val) (he : Fresh update x e) :
    (Cmd.seq (cmd update x e) (cmd update x e)).Equiv (cmd update x e) := by
  simpa only [esubst_of_fresh update e he] using aff_stack update overwrite x e e

/-- Upstream `aff_comm`: reorder writes, substituting into the moved right-hand side.
Only `e` must be fresh for `y`; `f` may read `x`. -/
theorem aff_comm
    (commute : ∀ (x y : Loc) (a b : Val) (s : σ), x ≠ y →
      update y b (update x a s) = update x a (update y b s))
    (x y : Loc) (e f : σ → Val) (hxy : x ≠ y) (he : Fresh update y e) :
    (Cmd.seq (cmd update x e) (cmd update y f)).Equiv
      (Cmd.seq (cmd update y (esubst update x e f)) (cmd update x e)) := by
  change (Cmd.seq (Cmd.assign _) (Cmd.assign _)).denote =
    (Cmd.seq (Cmd.assign _) (Cmd.assign _)).denote
  rw [show (Cmd.seq (Cmd.assign _) (Cmd.assign _)).denote = _ from
    Cmd.assign_seq (modify update x e) (modify update y f)]
  rw [show (Cmd.seq (Cmd.assign _) (Cmd.assign _)).denote = _ from
    Cmd.assign_seq (modify update y (esubst update x e f)) (modify update x e)]
  congr 2
  funext s
  change update y (f (update x (e s) s)) (update x (e s) s) =
    update x (e (update y (f (update x (e s) s)) s)) (update y (f (update x (e s) s)) s)
  rw [he]
  exact commute x y _ _ s hxy

/-- The relational fact used to combine assignment reasoning with KAT. -/
theorem denote_mul_test (x : Loc) (e : σ → Val) (b : Set σ) :
    (cmd update x e).denote * ⌜b⌝ = ⌜subst update x e b⌝ * (cmd update x e).denote := by
  ext ⟨s, t⟩
  simp only [mem_mul_test, mem_test_mul, mem_denote, mem_subst]
  constructor
  · rintro ⟨rfl, hb⟩
    exact ⟨hb, rfl⟩
  · rintro ⟨hb, rfl⟩
    exact ⟨rfl, hb⟩

/-- Upstream `aff_ite`: move an assignment into both branches, substituting the guard.
No overwrite or commutation law is needed. -/
theorem aff_ite (x : Loc) (e : σ → Val) (b : Set σ) (p q : Cmd σ) :
    (Cmd.seq (cmd update x e) (Cmd.ite b p q)).Equiv
      (Cmd.ite (subst update x e b) (Cmd.seq (cmd update x e) p)
        (Cmd.seq (cmd update x e) q)) := by
  simp only [Cmd.equiv_def, Cmd.denote_seq, Cmd.denote_ite, KAT.ifThenElse,
    mul_add, ← mul_assoc]
  rw [denote_mul_test, denote_mul_test, subst_compl]

end Assignment

/-- A store maps named locations to values. No finiteness or inhabitedness is required. -/
abbrev Store (Loc : Type u) (Val : Type v) := Loc → Val

namespace Store

variable {Loc : Type u} {Val : Type v} {β : Type w} [DecidableEq Loc]

/-- Change exactly one location. -/
def update (x : Loc) (v : Val) (s : Store Loc Val) : Store Loc Val := Function.update s x v

@[simp] theorem update_same (s : Store Loc Val) (x : Loc) (v : Val) : update x v s x = v :=
  Function.update_self (β := fun _ ↦ Val) x v s

@[simp] theorem update_of_ne (s : Store Loc Val) (v : Val) {x y : Loc} (h : y ≠ x) :
    update x v s y = s y := Function.update_of_ne (β := fun _ ↦ Val) h v s

theorem update_twice (x : Loc) (a b : Val) (s : Store Loc Val) :
    update x b (update x a s) = update x b s :=
  Function.update_idem (β := fun _ ↦ Val) a b s

theorem update_comm (x y : Loc) (a b : Val) (s : Store Loc Val) (hxy : x ≠ y) :
    update y b (update x a s) = update x a (update y b s) :=
  Function.update_comm (β := fun _ ↦ Val) hxy a b s

/-- `x ::= e`, where `e` is evaluated in the old store. -/
abbrev assign (x : Loc) (e : Store Loc Val → Val) : Cmd (Store Loc Val) :=
  Assignment.cmd update x e

abbrev esubst (x : Loc) (e : Store Loc Val → Val) (f : Store Loc Val → β) : Store Loc Val → β :=
  Assignment.esubst update x e f

abbrev subst (x : Loc) (e : Store Loc Val → Val) (b : Set (Store Loc Val)) : Set (Store Loc Val) :=
  Assignment.subst update x e b

abbrev Fresh (x : Loc) (e : Store Loc Val → β) : Prop := Assignment.Fresh update x e

/-- Reading a distinct location is unaffected by the update. -/
theorem fresh_var {x y : Loc} (hxy : x ≠ y) : Fresh x (fun s : Store Loc Val ↦ s y) :=
  fun _ _ ↦ update_of_ne _ _ hxy.symm

theorem fresh_const (x : Loc) (v : β) : Fresh x (fun _ : Store Loc Val ↦ v) :=
  Assignment.fresh_const update x v

@[simp] theorem esubst_var (x : Loc) (e : Store Loc Val → Val) :
    esubst x e (fun s ↦ s x) = e := by
  funext s
  exact update_same s x (e s)

@[simp] theorem esubst_var_of_ne {x y : Loc} (hxy : x ≠ y) (e : Store Loc Val → Val) :
    esubst x e (fun s ↦ s y) = (fun s ↦ s y) :=
  Assignment.esubst_of_fresh update e (fresh_var hxy)

theorem aff_stack (x : Loc) (e f : Store Loc Val → Val) :
    (Cmd.seq (assign x e) (assign x f)).Equiv (assign x (esubst x e f)) :=
  Assignment.aff_stack update update_twice x e f

theorem aff_idem (x : Loc) (e : Store Loc Val → Val) (he : Fresh x e) :
    (Cmd.seq (assign x e) (assign x e)).Equiv (assign x e) :=
  Assignment.aff_idem update update_twice x e he

theorem aff_comm (x y : Loc) (e f : Store Loc Val → Val) (hxy : x ≠ y) (he : Fresh y e) :
    (Cmd.seq (assign x e) (assign y f)).Equiv
      (Cmd.seq (assign y (esubst x e f)) (assign x e)) :=
  Assignment.aff_comm update update_comm x y e f hxy he

/-- Independent writes commute without changing either expression. -/
theorem aff_commute (x y : Loc) (e f : Store Loc Val → Val) (hxy : x ≠ y)
    (he : Fresh y e) (hf : Fresh x f) :
    (Cmd.seq (assign x e) (assign y f)).Equiv (Cmd.seq (assign y f) (assign x e)) := by
  simpa only [Assignment.esubst_of_fresh update e hf] using aff_comm x y e f hxy he

theorem aff_ite (x : Loc) (e : Store Loc Val → Val) (b : Set (Store Loc Val))
    (p q : Cmd (Store Loc Val)) :
    (Cmd.seq (assign x e) (Cmd.ite b p q)).Equiv
      (Cmd.ite (subst x e b) (Cmd.seq (assign x e) p) (Cmd.seq (assign x e) q)) :=
  Assignment.aff_ite update x e b p q

/-- Writing back the current value changes nothing. -/
theorem assign_self (x : Loc) : (assign x (fun s : Store Loc Val ↦ s x)).Equiv Cmd.skip := by
  ext ⟨s, t⟩
  change t = Function.update s x (s x) ↔ s = t
  simp [Function.update_eq_self, eq_comm]

/-- The Hoare assignment rule with substitution written explicitly. -/
theorem hoare_assign (x : Loc) (e : Store Loc Val → Val) (b : Set (Store Loc Val)) :
    HoareCmd (subst x e b) (assign x e) b := Assignment.hoare update x e b

end Store

/-- Scoped imperative assignment; `:=` remains Lean's declaration syntax. -/
scoped infix:60 " ::= " => Store.assign
scoped infixr:55 " ;; " => Cmd.seq

end IMP
