import RelationAlgebra.TypedKATCompleteness.Main

/-!
# Typed completeness regressions

The object alphabet below is `ℕ`, so these examples exercise the reduction to finite
support rather than assuming a finite object type. Interpretations range over arbitrary
typed KATs. The derivative checker supplies certificates; the new completeness theorem
reconstructs their typed proofs. No typed tactic reifier is used here.
-/

open CategoryTheory TypedKAT
open scoped Computability

namespace TypedKAT.CompletenessExamples

private abbrev src (a : ℕ) : ℕ := if a = 0 then 0 else 1
private abbrev tgt (a : ℕ) : ℕ := if a = 0 then 1 else 0

private def slideLeft : Term src tgt 0 1 := .comp (.act 0) (.star (.comp (.act 1) (.act 0)))
private def slideRight : Term src tgt 0 1 := .comp (.star (.comp (.act 0) (.act 1))) (.act 0)

private def splitSource : Term src tgt 0 1 :=
  .add (.comp (.test (.tvar 0)) (.act 0)) (.comp (.test (.not (.tvar 0))) (.act 0))

private def splitTarget : Term src tgt 0 1 :=
  .add (.comp (.act 0) (.test (.tvar 0))) (.comp (.act 0) (.test (.not (.tvar 0))))

private def guarded : Term src tgt 0 1 :=
  .comp (.test (.tvar 0)) (.comp (.act 0) (.test (.not (.tvar 0))))

section Abstract

variable {C : Type*} [Category C] [KleeneCategory C]
  {T : C → Type*} [∀ X, BooleanAlgebra (T X)] [TypedKAT C T]
  (o : ℕ → C) (τ : ∀ X, ℕ → T (o X)) (ρ : ∀ a, o (src a) ⟶ o (tgt a))

/-- Typed sliding, proved through completeness over an infinite object alphabet. -/
theorem sliding : slideLeft.eval o τ ρ = slideRight.eval o τ ρ :=
  Completeness.eval_eq_of_decideEq o τ ρ (k := 0) (fuel := 100)
    (by decide) (by decide) (by decide)

/-- The same predicate name is interpreted independently at the two endpoints. -/
theorem split_source_target : splitSource.eval o τ ρ = splitTarget.eval o τ ρ :=
  Completeness.eval_eq_of_decideEq o τ ρ (k := 1) (fuel := 100)
    (by decide) (by decide) (by decide)

/-- Guarding at different objects refines an arbitrary heterogeneous action. -/
theorem guarded_le : guarded.eval o τ ρ ≤ (Term.act (src := src) (tgt := tgt) 0).eval o τ ρ :=
  Completeness.eval_le_of_decideLe o τ ρ (k := 1) (fuel := 100)
    (by decide) (by decide) (by decide)

/-- Conditional branches may be heterogeneous. -/
example : (Term.ifThenElse (.tvar 0) (.act 0) (.act 0) : Term src tgt 0 1).eval o τ ρ = ρ 0 := by
  exact Completeness.eval_eq_of_decideEq o τ ρ (e := .ifThenElse (.tvar 0) (.act 0) (.act 0))
    (f := .act 0) (k := 1) (fuel := 100) (by decide) (by decide) (by decide)

/-- Loop unrolling uses tests at the loop object and a composable round-trip body. -/
example : (Term.whileDo (.tvar 0) (.comp (.act 0) (.act 1)) : Term src tgt 0 0).eval o τ ρ =
    (Term.ifThenElse (.tvar 0)
      (.comp (.comp (.act 0) (.act 1)) (.whileDo (.tvar 0) (.comp (.act 0) (.act 1))))
      .one : Term src tgt 0 0).eval o τ ρ :=
  Completeness.eval_eq_of_decideEq o τ ρ (k := 1) (fuel := 100)
    (by decide) (by decide) (by decide)

/-- The object map is allowed to identify distinct syntactic objects. -/
example (X : C) (τ : ∀ _ : ℕ, ℕ → T X) (ρ : ∀ _ : ℕ, X ⟶ X) :
    splitSource.eval (fun _ ↦ X) τ ρ = splitTarget.eval (fun _ ↦ X) τ ρ :=
  split_source_target _ τ ρ

end Abstract

/-! Checks for false equations and missing test bounds. -/

example : KAT.KTerm.decideEq 1 guarded.erase KAT.KTerm.zero 100 = false := by decide

example : KAT.KTerm.decideEq 0 (KAT.KTerm.act 0) (KAT.KTerm.act 1) 100 = false := by decide

/-- With no atom bits, an out-of-range variable evaluates to false in the language model.
The bound hypothesis is therefore necessary for the completeness interface. -/
example : KAT.KTerm.decideEq 0 (.test (.tvar 0)) .zero 100 = true := by decide

example : (Term.test (.tvar 0) : Term src tgt 0 0).tvarsBelow 0 = false := by decide

/-! A loop's matrix has identities at unused objects, while its own row recovers its star. -/

section Matrix

open KleeneCategory HomMatrix

variable {C : Type*} [Category C] [KleeneCategory C] (o : Fin 2 → C) (p : o 0 ⟶ o 0)

example : (single 0 0 p : HomMatrix o)∗ 0 0 = p∗ := by
  simpa using row_kstar (A := single 0 0 p) (x := 0) (a := p) (single_row 0 0 p) 0

example : (single 0 0 p : HomMatrix o)∗ 1 1 = 𝟙 (o 1) := by
  have h : ∀ j, (single 0 0 p : HomMatrix o) 1 j = row 1 (⊥ : o 1 ⟶ o 1) j := by
    intro j
    simp [single]
  simpa using row_kstar h 1

end Matrix
end TypedKAT.CompletenessExamples
