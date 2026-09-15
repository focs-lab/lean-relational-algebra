import RelationAlgebra.Automata.Thompson
import RelationAlgebra.Automata.Minimal

/-!
# Completeness of Kleene algebra

**Kozen's completeness theorem**: two regular expressions denoting the same language are equal
in *every* Kleene algebra, under every valuation.

```
theorem KleeneAlgebra.Term.completeness_eq {e f : Term} (h : e.lang = f.lang)
    {K : Type*} [KleeneAlgebra K] (ρ : ℕ → K) : e.eval ρ = f.eval ρ
```

No completeness, star-continuity, commutativity or finiteness assumption is made on `K`.  This
is what removes the `CompleteKleeneAlgebra` restriction from the `ka` tactic.

## The proof

Assembled from the four preceding files, following Kozen's argument:

1. `RelationAlgebra.Automata.value_thompson` — Thompson's construction gives, for each term `e`,
   a finite automaton with epsilon-transitions whose value in an arbitrary Kleene algebra is
   `e.eval ρ`.
2. `RelationAlgebra.Automata.EpsNFA.value_epsElim` — epsilon-transitions are eliminated without
   changing the value, using `Matrix.ofRel_kstar` and the denesting law.
3. `RelationAlgebra.Automata.EpsNFA.value_det` — the subset construction gives a deterministic
   automaton with the same value, by the rectangular bisimulation rule.
4. `RelationAlgebra.Automata.value_eq_langOf` — instantiated at the Kleene algebra
   `Language ℕ`, step 1-3 identify the language accepted by that deterministic automaton with
   `e.lang`.
5. `RelationAlgebra.Automata.value_eq_of_langOf_eq` — two deterministic automata accepting the
   same language have the same value in every Kleene algebra, because both map homomorphically
   onto a common automaton of language-equivalence classes.

## References

* [D. Kozen, *A completeness theorem for Kleene algebras and the algebra of regular events*,
  Information and Computation 110(2):366-390, 1994][kozen1994]
* Damien Pous, `relation-algebra`, `theories/ka_completeness.v`.
-/

open scoped Computability
open RelationAlgebra.Automata

namespace KleeneAlgebra.Term

/-- The deterministic automaton of a regular expression: Thompson's automaton, with
epsilon-transitions eliminated, then determinised. -/
def detAut (e : Term) : EpsNFA (Finset (thompson e).States) :=
  EpsNFA.det (thompson e).aut.epsElim

open Classical in
/-- The initial state of `detAut e`. -/
noncomputable def detInit (e : Term) : Finset (thompson e).States :=
  Finset.univ.filter (thompson e).aut.epsElim.start

open Classical in
/-- The transition function of `detAut e`. -/
noncomputable def detNext (e : Term) (a : ℕ) (S : Finset (thompson e).States) :
    Finset (thompson e).States :=
  Finset.univ.filter fun j => ∃ i ∈ S, (thompson e).aut.epsElim.step a i j

theorem detAut_isDet (e : Term) : (detAut e).IsDet (detInit e) (detNext e) :=
  EpsNFA.det_isDet _

/-- The deterministic automaton of `e` denotes `e`, in every Kleene algebra. -/
theorem value_detAut {K : Type*} [KleeneAlgebra K] (Γ : Finset ℕ) (ρ : ℕ → K) (e : Term)
    (he : ∀ a ∈ e.vars, a ∈ Γ) : (detAut e).value Γ ρ = e.eval ρ := by
  rw [detAut, ← EpsNFA.value_det Γ ρ _ (EpsNFA.epsElim_epsFree _),
    EpsNFA.value_epsElim, value_thompson Γ ρ e he]

/-- In the language model, the deterministic automaton of `e` accepts exactly `e.lang`. -/
theorem langOf_detAut (Γ : Finset ℕ) (e : Term) (he : ∀ a ∈ e.vars, a ∈ Γ) :
    langOf (detAut e) (detNext e) Γ (detInit e) = e.lang := by
  rw [← value_eq_langOf _ Γ (detAut_isDet e), value_detAut Γ letterVal e he]
  rfl

/-- **Kozen's completeness theorem for Kleene algebra.**  Regular expressions with the same
language are equal in every Kleene algebra. -/
theorem completeness_eq {e f : Term} (h : e.lang = f.lang) {K : Type*} [KleeneAlgebra K]
    (ρ : ℕ → K) : e.eval ρ = f.eval ρ := by
  classical
  set Γ : Finset ℕ := (e.vars ++ f.vars).toFinset with hΓ
  have he : ∀ a ∈ e.vars, a ∈ Γ := by
    intro a ha
    simp [hΓ, List.mem_toFinset, ha]
  have hf : ∀ a ∈ f.vars, a ∈ Γ := by
    intro a ha
    simp [hΓ, List.mem_toFinset, ha]
  have hlang : langOf (detAut e) (detNext e) Γ (detInit e)
      = langOf (detAut f) (detNext f) Γ (detInit f) := by
    rw [langOf_detAut Γ e he, langOf_detAut Γ f hf, h]
  have := value_eq_of_langOf_eq Γ ρ (detAut_isDet e) (detAut_isDet f) hlang
  rw [← value_detAut Γ ρ e he, ← value_detAut Γ ρ f hf, this]

/-- **Completeness for inequalities.** -/
theorem completeness_le {e f : Term} (h : e.lang ≤ f.lang) {K : Type*} [KleeneAlgebra K]
    (ρ : ℕ → K) : e.eval ρ ≤ f.eval ρ := by
  have hadd : (Term.add e f).lang = f.lang := by
    rw [lang_add]
    exact add_eq_right_iff_le.2 h
  have := completeness_eq hadd ρ
  rw [eval] at this
  exact add_eq_right_iff_le.1 this

/-! ### Consequences for the decision procedure -/

/-- Soundness of the Antimirov checker in an **arbitrary** Kleene algebra. -/
theorem eval_eq_of_decideEq' {K : Type*} [KleeneAlgebra K] {e f : Term} {fuel : ℕ}
    (h : Term.decideEq e f fuel = true) (ρ : ℕ → K) : e.eval ρ = f.eval ρ :=
  completeness_eq (lang_eq_of_decideEq h) ρ

/-- Soundness of the Antimirov checker for inequalities, in an **arbitrary** Kleene algebra. -/
theorem eval_le_of_decideLe' {K : Type*} [KleeneAlgebra K] {e f : Term} {fuel : ℕ}
    (h : Term.decideLe e f fuel = true) (ρ : ℕ → K) : e.eval ρ ≤ f.eval ρ :=
  completeness_le (lang_le_of_decideLe h) ρ

end KleeneAlgebra.Term
