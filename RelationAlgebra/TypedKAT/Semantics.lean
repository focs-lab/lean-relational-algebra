import RelationAlgebra.TypedKAT.LanguageModel
import Mathlib.Algebra.Order.BigOperators.Group.List
import RelationAlgebra.TypedKATCompleteness.Main

/-!
# Semantic equality and order for typed KAT expressions

`Term.SemEq` and `Term.SemLE` compare languages at every finite atom bound. They do not
identify out-of-range test variables with false. By typed completeness, either relation
holds exactly when its corresponding language comparison holds at any bound covering both
expressions, and it transports to every typed KAT interpretation, in arbitrary universes.

These are the semantic relations used in the expression quotient, corresponding to
`gregex.v` in Damien Pous's `relation-algebra`. `semEq_iff_erase` and `semLE_iff_erase`
package erasure preservation and reflection of these relations.
-/

open CategoryTheory

universe u v w z

namespace KAT.KTerm

/-- Untyped semantic equality, with no fixed bound on test variables. -/
def SemEq (e f : KTerm) : Prop := ∀ k, e.gs k = f.gs k

/-- Untyped semantic inclusion, with no fixed bound on test variables. -/
def SemLE (e f : KTerm) : Prop := ∀ k, e.gs k ⊆ f.gs k

end KAT.KTerm

namespace TypedKAT.Term

variable {I : Type u} {src tgt : ℕ → I} {W X Y Z : I}

/-- Equality of languages at every atom bound. -/
def SemEq (e f : Term src tgt X Y) : Prop := ∀ k, e.lang k = f.lang k

/-- Inclusion of languages at every atom bound. -/
def SemLE (e f : Term src tgt X Y) : Prop := ∀ k, e.lang k ≤ f.lang k

/-- The semantic equivalence relation on each hom-set of expressions. -/
def semanticSetoid : Setoid (Term src tgt X Y) where
  r := SemEq
  iseqv := ⟨fun _ _ ↦ rfl, fun h k ↦ (h k).symm, fun h g k ↦ (h k).trans (g k)⟩

/-- Erasure preserves and reflects semantic equality of parallel typed expressions. -/
theorem semEq_iff_erase {e f : Term src tgt X Y} : e.SemEq f ↔ e.erase.SemEq f.erase :=
  forall_congr' fun k ↦ lang_eq_iff e f k

/-- Erasure preserves and reflects semantic inclusion of parallel typed expressions. -/
theorem semLE_iff_erase {e f : Term src tgt X Y} : e.SemLE f ↔ e.erase.SemLE f.erase := by
  simp only [SemLE, KAT.KTerm.SemLE, Language.le_def, strings_lang]

section Evaluation

variable {C : Type v} [Category.{w} C] [KleeneCategory C]
  {T : C → Type z} [∀ A, BooleanAlgebra (T A)] [TypedKAT C T]
  (o : I → C) (τ : ∀ A, ℕ → T (o A)) (ρ : ∀ a, o (src a) ⟶ o (tgt a))

/-- Semantic equality is respected by every typed interpretation. -/
theorem SemEq.eval_eq {e f : Term src tgt X Y} (h : e.SemEq f) :
    e.eval o τ ρ = f.eval o τ ρ := by
  let k := (e.tvars ++ f.tvars).sum + 1
  apply Completeness.eval_eq_of_lang_eq o τ ρ k _ _ (h k)
  · intro i hi
    exact Nat.lt_succ_of_le (List.le_sum_of_mem (List.mem_append_left _ hi))
  · intro i hi
    exact Nat.lt_succ_of_le (List.le_sum_of_mem (List.mem_append_right _ hi))

/-- Semantic inclusion is respected by every typed interpretation. -/
theorem SemLE.eval_le {e f : Term src tgt X Y} (h : e.SemLE f) :
    e.eval o τ ρ ≤ f.eval o τ ρ := by
  let k := (e.tvars ++ f.tvars).sum + 1
  apply Completeness.eval_le_of_lang_subset o τ ρ k _ _ (h k)
  · intro i hi
    exact Nat.lt_succ_of_le (List.le_sum_of_mem (List.mem_append_left _ hi))
  · intro i hi
    exact Nat.lt_succ_of_le (List.le_sum_of_mem (List.mem_append_right _ hi))

end Evaluation

/-- One adequate atom bound suffices to prove semantic equality at all bounds. -/
theorem semEq_iff_lang_eq {e f : Term src tgt X Y} (k : ℕ)
    (he : ∀ i ∈ e.tvars, i < k) (hf : ∀ i ∈ f.tvars, i < k) :
    e.SemEq f ↔ e.lang k = f.lang k := by
  refine ⟨fun h ↦ h k, fun h n ↦ ?_⟩
  simpa only [eval_languageCat] using
    (Completeness.eval_eq_of_lang_eq
      (T := fun _ : LanguageCat src tgt n ↦ Set (BoundedAtom n))
      LanguageCat.ofObject (fun _ ↦ LanguageCat.testVar) LanguageCat.action k he hf h)

/-- One adequate atom bound suffices to prove semantic inclusion at all bounds. -/
theorem semLE_iff_lang_le {e f : Term src tgt X Y} (k : ℕ)
    (he : ∀ i ∈ e.tvars, i < k) (hf : ∀ i ∈ f.tvars, i < k) :
    e.SemLE f ↔ e.lang k ≤ f.lang k := by
  refine ⟨fun h ↦ h k, fun h n ↦ ?_⟩
  simpa only [eval_languageCat] using
    (Completeness.eval_le_of_lang_subset
      (T := fun _ : LanguageCat src tgt n ↦ Set (BoundedAtom n))
      LanguageCat.ofObject (fun _ ↦ LanguageCat.testVar) LanguageCat.action k he hf h)

/-- Semantic equivalence is a congruence for choice. -/
theorem SemEq.add {e e' f f' : Term src tgt X Y} (he : e.SemEq e') (hf : f.SemEq f') :
    (e.add f).SemEq (e'.add f') := fun k ↦ congrArg₂ Language.add (he k) (hf k)

/-- Semantic equivalence is a congruence for typed composition. -/
theorem SemEq.comp {e e' : Term src tgt X Y} {f f' : Term src tgt Y Z}
    (he : e.SemEq e') (hf : f.SemEq f') : (e.comp f).SemEq (e'.comp f') :=
  fun k ↦ congrArg₂ Language.comp (he k) (hf k)

/-- Semantic equivalence is a congruence for iteration. -/
theorem SemEq.star {e f : Term src tgt X X} (h : e.SemEq f) : e.star.SemEq f.star :=
  fun k ↦ congrArg Language.star (h k)

end TypedKAT.Term
