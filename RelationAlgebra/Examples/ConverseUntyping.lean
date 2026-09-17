import RelationAlgebra.TypedRA.Untyping

/-!
# Untyping with converse: scope and regressions

These proofs invoke the universal untyped premise directly, independently of the typed
tactic. In particular, sliding uses an induction law outside `ra`'s structural fragment.
-/

open CategoryTheory TypedRA KleeneCategoryWithConverse
open scoped Computability KleeneCategoryWithConverse SetRel

universe u v w

namespace ConverseUntypingExamples

private def forward {I : Type u} (X Y : I) : Term (fun _ ↦ X) (fun _ ↦ Y) X Y :=
  .comp (.act 0) (.star (.comp (.conv (.act 0)) (.act 0)))

private def backward {I : Type u} (X Y : I) : Term (fun _ ↦ X) (fun _ ↦ Y) X Y :=
  .comp (.star (.comp (.act 0) (.conv (.act 0)))) (.act 0)

section Abstract
variable {I : Type u} {X Y : I} {C : Type v} [Category.{w} C] [KleeneCategory C]
  [KleeneCategoryWithConverse C] (o : I → C) (ρ : ∀ _ : ℕ, o X ⟶ o Y)

/-- Both star and converse occur in the transported equation. -/
theorem sliding : (forward X Y).eval o ρ = (backward X Y).eval o ρ := by
  apply Term.eval_eq_of_erase_eval_eq
  intro K _ _ π
  change π 0 * (Star.star (π 0) * π 0)∗ = (π 0 * Star.star (π 0))∗ * π 0
  exact KleeneAlgebra.mul_kstar_eq_kstar_mul _ _

/-- The column invariant is exercised by an outer converse. -/
theorem converse_sliding : (Term.conv (forward X Y)).eval o ρ =
    (Term.conv (backward X Y)).eval o ρ := by
  apply Term.eval_eq_of_erase_eval_eq
  intro K _ _ π
  change Star.star (π 0 * (Star.star (π 0) * π 0)∗) =
    Star.star ((π 0 * Star.star (π 0))∗ * π 0)
  exact congrArg Star.star (KleeneAlgebra.mul_kstar_eq_kstar_mul _ _)

theorem inclusion : (Term.conv (Term.act 0) : Term (fun _ ↦ X) (fun _ ↦ Y) Y X).eval o ρ ≤
    (Term.conv (forward X Y)).eval o ρ := by
  apply Term.eval_le_of_erase_eval_le
  intro K _ _ π
  change Star.star (π 0) ≤ Star.star (π 0 * (Star.star (π 0) * π 0)∗)
  exact KleeneAlgebra.star_mono KleeneAlgebra.le_mul_kstar

example : (Term.conv (.zero : Term (fun _ ↦ X) (fun _ ↦ Y) X Y)).eval o ρ = ⊥ := by
  change _ = (Term.zero : Term (fun _ ↦ X) (fun _ ↦ Y) Y X).eval o ρ
  apply Term.eval_eq_of_erase_eval_eq
  intro K _ _ π
  change Star.star (0 : K) = 0
  exact star_zero _

/-- Object identification is allowed even in the presence of converse. -/
example (A : C) (actions : ℕ → (A ⟶ A)) :
    (forward X Y).eval (fun _ ↦ A) actions = (backward X Y).eval (fun _ ↦ A) actions :=
  sliding (X := X) (Y := Y) (fun _ ↦ A) actions

end Abstract

/-- No finiteness or small-universe assumption on the syntactic object alphabet. -/
example {C : Type v} [Category.{w} C] [KleeneCategory C] [KleeneCategoryWithConverse C]
    (o : ULift.{u} ℕ → C) (ρ : ∀ _ : ℕ, o (ULift.up 0) ⟶ o (ULift.up 1)) :
    (Term.conv (forward (ULift.up 0) (ULift.up 1))).eval o ρ =
      (Term.conv (backward (ULift.up 0) (ULift.up 1))).eval o ρ := converse_sliding o ρ

private def relObjects (n : ℕ) : RelCat := if n = 0 then ℕ else Bool

theorem relations (ρ : ∀ _ : ℕ, relObjects 0 ⟶ relObjects 1) :
    (forward 0 1).eval relObjects ρ = (backward 0 1).eval relObjects ρ := sliding _ ρ

/-- A fact about one valuation does not meet the universal premise. -/
example {C : Type v} [Category.{w} C] [KleeneCategory C] [KleeneCategoryWithConverse C]
    (o : ℕ → C) (ρ : ∀ _ : ℕ, o 0 ⟶ o 1) :
    (Term.act 0 : Term (fun _ ↦ 0) (fun _ ↦ 1) 0 1).eval o ρ = ρ 0 := by
  have h : RaTerm.eval (K := SetRel ℕ ℕ) (fun _ ↦ 0) (.var 0) =
      RaTerm.eval (K := SetRel ℕ ℕ) (fun _ ↦ 0) .zero := rfl
  fail_if_success have : (Term.act 0 : Term (fun _ ↦ 0) (fun _ ↦ 1) 0 1).eval o ρ =
      (Term.zero : Term (fun _ ↦ 0) (fun _ ↦ 1) 0 1).eval o ρ :=
    Term.eval_eq_of_erase_eval_eq o ρ h
  rfl

/-- Ill-typed compositions, stars, and un-reversed converses are rejected by elaboration. -/
example : True := by
  fail_if_success have := (Term.comp (.act 0) (.act 0) :
    Term (fun _ ↦ (0 : ℕ)) (fun _ ↦ 1) 0 1)
  fail_if_success have := (Term.star (.act 0) :
    Term (fun _ ↦ (0 : ℕ)) (fun _ ↦ 1) 0 0)
  fail_if_success have := (Term.conv (.act 0) :
    Term (fun _ ↦ (0 : ℕ)) (fun _ ↦ 1) 0 1)
  trivial

end ConverseUntypingExamples
