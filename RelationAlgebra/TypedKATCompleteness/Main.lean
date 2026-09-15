import RelationAlgebra.TypedKATCompleteness.Finite
import RelationAlgebra.TypedKATCompleteness.Support

/-!
# Completeness of typed Kleene algebra with tests

Equal guarded-string languages give equal interpretations in every typed KAT. The object
alphabet, semantic category, hom-sets, and Boolean test algebras are unrestricted.

The proof restricts each pair of expressions to its finite object support, interprets its
erasure in the Kleene algebra of heterogeneous matrices, applies untyped KAT completeness,
and recovers the entry at the original source and target. Unlike a star-continuous model
argument, this uses only the rectangular Kleene induction axioms.

This proves the typed form of the Kozen–Smith completeness theorem, corresponding to Damien
Pous's `relation-algebra/theories/kat_completeness.v`. The proof here reuses the existing
untyped theorem through the finite additive completion of a Kleene category.
-/

open CategoryTheory

universe u v w z

namespace TypedKAT.Completeness

variable {I : Type u} {src tgt : ℕ → I} {X Y : I}
  {C : Type v} [Category.{w} C] [KleeneCategory C]
  {T : C → Type z} [∀ A, BooleanAlgebra (T A)] [TypedKAT C T]
  (o : I → C) (τ : ∀ A, ℕ → T (o A)) (ρ : ∀ a, o (src a) ⟶ o (tgt a))

/-- **Typed KAT completeness.** Equal guarded-string languages imply equal values in any
typed KAT, provided the finite atom bound covers the test variables of both expressions. -/
theorem eval_eq_of_lang_eq {e f : Term src tgt X Y} (k : ℕ)
    (he : ∀ a ∈ e.tvars, a < k) (hf : ∀ a ∈ f.tvars, a < k)
    (h : e.lang k = f.lang k) : e.eval o τ ρ = f.eval o τ ρ := by
  classical
  let s := e.objects ∪ f.objects
  have heS : e.objects ⊆ s := Finset.subset_union_left
  have hfS : f.objects ⊆ s := Finset.subset_union_right
  let d : s := ⟨X, heS (e.source_mem_objects)⟩
  let e' := e.restrict d heS
  let f' := f.restrict d hfS
  have he' : ∀ a ∈ e'.tvars, a < k := by simpa [e', Term.tvars] using he
  have hf' : ∀ a ∈ f'.tvars, a < k := by simpa [f', Term.tvars] using hf
  have h' : e'.lang k = f'.lang k := by
    apply (Term.lang_eq_iff e' f' k).2
    simpa [e', f'] using (Term.lang_eq_iff e f k).1 h
  have hv := eval_eq_of_lang_eq_finite (fun i : s ↦ o i.val) (fun i ↦ τ i.val)
    (Term.restrictActions d o ρ) k he' hf' h'
  simpa only [e', f', Term.eval_restrict] using hv

/-- The inequational form of typed completeness. -/
theorem eval_le_of_lang_subset {e f : Term src tgt X Y} (k : ℕ)
    (he : ∀ a ∈ e.tvars, a < k) (hf : ∀ a ∈ f.tvars, a < k)
    (h : (e.lang k).strings ⊆ (f.lang k).strings) : e.eval o τ ρ ≤ f.eval o τ ρ := by
  have hadd : (e.add f).lang k = f.lang k := by
    apply Language.ext
    exact Set.union_eq_self_of_subset_left h
  have hb : ∀ a ∈ (e.add f).tvars, a < k := by
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · exact he a ha
    · exact hf a ha
  exact sup_eq_right.1 (eval_eq_of_lang_eq o τ ρ k hb hf hadd)

/-- Reflection for typed equality goals. Certificate search is still fuel-bounded. -/
theorem eval_eq_of_decideEq {e f : Term src tgt X Y} {k fuel : ℕ}
    (he : e.tvarsBelow k = true) (hf : f.tvarsBelow k = true)
    (h : KAT.KTerm.decideEq k e.erase f.erase fuel = true) : e.eval o τ ρ = f.eval o τ ρ :=
  eval_eq_of_lang_eq o τ ρ k (KAT.KTerm.tvars_lt_of_tvarsBelow he)
    (KAT.KTerm.tvars_lt_of_tvarsBelow hf) (Term.lang_eq_of_decideEq h)

/-- Reflection for typed inequality goals. This theorem is a proof interface, not a tactic. -/
theorem eval_le_of_decideLe {e f : Term src tgt X Y} {k fuel : ℕ}
    (he : e.tvarsBelow k = true) (hf : f.tvarsBelow k = true)
    (h : KAT.KTerm.decideLe k e.erase f.erase fuel = true) : e.eval o τ ρ ≤ f.eval o τ ρ := by
  apply eval_le_of_lang_subset o τ ρ k (KAT.KTerm.tvars_lt_of_tvarsBelow he)
    (KAT.KTerm.tvars_lt_of_tvarsBelow hf)
  simpa only [Term.strings_lang] using KAT.KTerm.gs_le_of_decideLe h

end TypedKAT.Completeness
