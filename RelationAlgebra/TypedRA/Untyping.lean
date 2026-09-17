import RelationAlgebra.TypedRA.Matrix
import RelationAlgebra.TypedRA.Support

/-!
# Untyping for Kleene algebra with converse

Universally valid untyped equations and inequalities transfer to parallel typed
expressions. The hypothesis ranges over **all** Kleene algebras with converse and
all action valuations; equality in one chosen model is insufficient. The category,
its hom-sets, and the syntactic object alphabet may be infinite.

This is the semantic transport counterpart of Damien Pous' `erase_faithful_weq`
and `erase_faithful_leq` in [`theories/untyping.v`](https://github.com/damien-pous/relation-algebra/blob/2d2af3631929399bbac56f57b3e15302d8697e1c/theories/untyping.v),
at the Kleene-with-converse level.
Upstream also treats weaker levels of its hierarchy; those are not asserted here.
The proof restricts to finite object support, interprets erasure in matrices with
converse, and recovers the typed value from its declared entry.
-/

open CategoryTheory KleeneCategory

universe u v w

namespace TypedRA.Term

variable {I : Type u} {src tgt : ℕ → I} {X Y : I}
  {C : Type v} [Category.{w} C] [KleeneCategory C]
  [KleeneCategoryWithConverse C]
  (o : I → C) (ρ : ∀ a, o (src a) ⟶ o (tgt a))

private theorem eval_le_of_erase_eval_le_finite [Finite I] {e f : Term src tgt X Y}
    (h : ∀ {K : Type (max u w)}
      [KleeneAlgebra K] [StarRing K]
      (π : ℕ → K), e.erase.eval π ≤ f.erase.eval π) :
    e.eval o ρ ≤ f.eval o ρ := by
  classical
  letI := Fintype.ofFinite I
  have hm : evalMatrix o ρ e ≤ evalMatrix o ρ f :=
    h (fun a ↦ HomMatrix.single (src a) (tgt a) (ρ a))
  simpa only [eval_entry] using hm X Y

/-- A universally valid inequality in Kleene algebras with converse holds for parallel
typed expressions. The law is instantiated with finite matrices of morphisms. -/
theorem eval_le_of_erase_eval_le {e f : Term src tgt X Y}
    (h : ∀ {K : Type (max u w)}
      [KleeneAlgebra K] [StarRing K]
      (π : ℕ → K), e.erase.eval π ≤ f.erase.eval π) :
    e.eval o ρ ≤ f.eval o ρ := by
  classical
  let s := e.objects ∪ f.objects
  have he : e.objects ⊆ s := Finset.subset_union_left
  have hf : f.objects ⊆ s := Finset.subset_union_right
  let d : s := ⟨X, he (e.source_mem_objects)⟩
  let e' := e.restrict d he
  let f' := f.restrict d hf
  have h' : ∀ {K : Type (max u w)}
      [KleeneAlgebra K] [StarRing K]
      (π : ℕ → K), e'.erase.eval π ≤ f'.erase.eval π := by
    intro K _ _ π
    simpa only [e', f', erase_restrict] using h π
  have hv := eval_le_of_erase_eval_le_finite (fun i : s ↦ o i.val)
    (restrictActions d o ρ) h'
  simpa only [e', f', eval_restrict] using hv

/-- A universally valid equation in Kleene algebras with converse holds for parallel
typed expressions.
The object alphabet and interpretations are arbitrary; no atom bound or fuel is required. -/
theorem eval_eq_of_erase_eval_eq {e f : Term src tgt X Y}
    (h : ∀ {K : Type (max u w)}
      [KleeneAlgebra K] [StarRing K]
      (π : ℕ → K), e.erase.eval π = f.erase.eval π) :
    e.eval o ρ = f.eval o ρ := by
  apply le_antisymm
  · exact eval_le_of_erase_eval_le o ρ (fun π ↦ (h π).le)
  · exact eval_le_of_erase_eval_le o ρ (fun π ↦ (h π).ge)

/-- Kernel-checked structural equality transfers through untyping. -/
theorem eval_eq_of_normEq {e f : Term src tgt X Y}
    (h : RaTerm.normEq e.erase f.erase = true) : e.eval o ρ = f.eval o ρ :=
  eval_eq_of_erase_eval_eq o ρ (fun π ↦ RaTerm.eval_eq_of_normEq' h π)

/-- Kernel-checked structural inclusion transfers through untyping. -/
theorem eval_le_of_normLe {e f : Term src tgt X Y}
    (h : RaTerm.normLe e.erase f.erase = true) : e.eval o ρ ≤ f.eval o ρ :=
  eval_le_of_erase_eval_le o ρ (fun π ↦ RaTerm.eval_le_of_normLe' h π)

/-- Readback of a normal form is justified by a proved untyped normalization. -/
theorem eval_eq_of_erase_norm {e f : Term src tgt X Y}
    (h : f.erase = e.erase.norm) : f.eval o ρ = e.eval o ρ :=
  eval_eq_of_erase_eval_eq o ρ (fun π ↦ by rw [h]; exact RaTerm.eval_norm π e.erase)

/-- Readback of the lighter simplification is justified by its untyped correctness proof. -/
theorem eval_eq_of_erase_simplify {e f : Term src tgt X Y}
    (h : f.erase = e.erase.simplify) : f.eval o ρ = e.eval o ρ :=
  eval_eq_of_erase_eval_eq o ρ (fun π ↦ by rw [h]; exact RaTerm.eval_simplify π e.erase)

end TypedRA.Term
