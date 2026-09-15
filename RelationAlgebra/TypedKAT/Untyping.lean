import RelationAlgebra.TypedKATCompleteness.Finite
import RelationAlgebra.TypedKATCompleteness.Support

/-!
# Algebraic untyping for Kleene algebra with tests

A universally valid untyped equation or inequality between the erasures of two expressions
also holds under every typed interpretation of those expressions. Both expressions must
have the same source and target. Tests retain independent valuations at each object, even
when the object map identifies different syntactic objects.

The public interfaces are `TypedKAT.Term.eval_eq_of_erase_eval_eq` and
`TypedKAT.Term.eval_le_of_erase_eval_le`. Their hypotheses quantify over the untyped test
algebra, Kleene algebra, and both valuations. Equality in just one model or valuation is
insufficient. No atom bound, fuel, finiteness, or continuity assumption is needed.

The proof restricts the expressions to their finite object support, instantiates the
untyped law in the existing algebra of heterogeneous matrices, and reads the source/target
entry. The universe maxima in the hypothesis account for those matrices and their families
of tests; they impose no smallness assumption on the object alphabet or semantic category.

This supplies the transport direction of the KAT untyping interface in Damien Pous's
`relation-algebra` (`theories/kat_untyping.v`). Free-model and equivalence-relation packaging
are separate from this evaluation interface.
-/

open CategoryTheory KleeneCategory

universe u v w z

namespace TypedKAT.Term

variable {I : Type u} {src tgt : ℕ → I} {X Y : I}
  {C : Type v} [Category.{w} C] [KleeneCategory C]
  {T : C → Type z} [∀ A, BooleanAlgebra (T A)] [TypedKAT C T]
  (o : I → C) (τ : ∀ A, ℕ → T (o A)) (ρ : ∀ a, o (src a) ⟶ o (tgt a))

private theorem eval_le_of_erase_eval_le_finite [Finite I] {e f : Term src tgt X Y}
    (h : ∀ {B : Type (max u z)} {K : Type (max u w)}
      [BooleanAlgebra B] [KleeneAlgebra K] [KAT B K]
      (σ : ℕ → B) (π : ℕ → K), e.erase.eval σ π ≤ f.erase.eval σ π) :
    e.eval o τ ρ ≤ f.eval o τ ρ := by
  classical
  letI := Fintype.ofFinite I
  have hm : Completeness.evalMatrix o τ ρ e ≤ Completeness.evalMatrix o τ ρ f :=
    h (fun a i ↦ τ i a) (fun a ↦ HomMatrix.single (src a) (tgt a) (ρ a))
  simpa only [Completeness.eval_entry] using hm X Y

/-- A universally valid inequality between erased expressions holds in every typed KAT.
The untyped law must quantify over both algebras and both valuations; it is instantiated
with matrices of morphisms and families of tests at the finitely many objects used. -/
theorem eval_le_of_erase_eval_le {e f : Term src tgt X Y}
    (h : ∀ {B : Type (max u z)} {K : Type (max u w)}
      [BooleanAlgebra B] [KleeneAlgebra K] [KAT B K]
      (σ : ℕ → B) (π : ℕ → K), e.erase.eval σ π ≤ f.erase.eval σ π) :
    e.eval o τ ρ ≤ f.eval o τ ρ := by
  classical
  let s := e.objects ∪ f.objects
  have he : e.objects ⊆ s := Finset.subset_union_left
  have hf : f.objects ⊆ s := Finset.subset_union_right
  let d : s := ⟨X, he (e.source_mem_objects)⟩
  let e' := e.restrict d he
  let f' := f.restrict d hf
  have h' : ∀ {B : Type (max u z)} {K : Type (max u w)}
      [BooleanAlgebra B] [KleeneAlgebra K] [KAT B K]
      (σ : ℕ → B) (π : ℕ → K), e'.erase.eval σ π ≤ f'.erase.eval σ π := by
    intro B K _ _ _ σ π
    simpa only [e', f', erase_restrict] using h σ π
  have hv := eval_le_of_erase_eval_le_finite (fun i : s ↦ o i.val) (fun i ↦ τ i.val)
    (restrictActions d o ρ) h'
  simpa only [e', f', eval_restrict] using hv

/-- A universally valid equation between erased expressions holds in every typed KAT.
The object alphabet and interpretations are arbitrary; no atom bound or fuel is required. -/
theorem eval_eq_of_erase_eval_eq {e f : Term src tgt X Y}
    (h : ∀ {B : Type (max u z)} {K : Type (max u w)}
      [BooleanAlgebra B] [KleeneAlgebra K] [KAT B K]
      (σ : ℕ → B) (π : ℕ → K), e.erase.eval σ π = f.erase.eval σ π) :
    e.eval o τ ρ = f.eval o τ ρ := by
  apply le_antisymm
  · exact eval_le_of_erase_eval_le o τ ρ (fun σ π ↦ (h σ π).le)
  · exact eval_le_of_erase_eval_le o τ ρ (fun σ π ↦ (h σ π).ge)

end TypedKAT.Term
