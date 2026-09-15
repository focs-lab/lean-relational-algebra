import RelationAlgebra.TypedKAT.Untyping
import RelationAlgebra.Decide.KATTactic

/-!
# Transporting untyped KAT laws to typed interpretations

The law supplied to untyping is proved over an arbitrary untyped KAT. The examples below
use the ordinary `kat` tactic for that premise, then transfer it to heterogeneous
morphisms. No guarded-string bound or search fuel appears in the untyping interface.
-/

open CategoryTheory TypedKAT
open scoped Computability

universe u v w z

namespace TypedKAT.UntypingExamples

private abbrev source {I : Type u} (X Y : I) (a : ℕ) : I := if a = 0 then X else Y
private abbrev target {I : Type u} (X Y : I) (a : ℕ) : I := if a = 0 then Y else X

private def slideLeft {I : Type u} (X Y : I) : Term (source X Y) (target X Y) X Y :=
  .comp (.act 0) (.star (.comp (.act 1) (.act 0)))

private def slideRight {I : Type u} (X Y : I) : Term (source X Y) (target X Y) X Y :=
  .comp (.star (.comp (.act 0) (.act 1))) (.act 0)

private def splitSource {I : Type u} (X Y : I) : Term (source X Y) (target X Y) X Y :=
  .add (.comp (.test (.tvar 0)) (.act 0)) (.comp (.test (.not (.tvar 0))) (.act 0))

private def splitTarget {I : Type u} (X Y : I) : Term (source X Y) (target X Y) X Y :=
  .add (.comp (.act 0) (.test (.tvar 0))) (.comp (.act 0) (.test (.not (.tvar 0))))

private def guarded {I : Type u} (X Y : I) : Term (source X Y) (target X Y) X Y :=
  .comp (.test (.tvar 0)) (.comp (.act 0) (.test (.not (.tvar 0))))

section Abstract

variable {I : Type u} {X Y : I} {C : Type v} [Category.{w} C] [KleeneCategory C]
  {T : C → Type z} [∀ A, BooleanAlgebra (T A)] [TypedKAT C T]
  (o : I → C) (τ : ∀ A, ℕ → T (o A))
  (ρ : ∀ a, o (source X Y a) ⟶ o (target X Y a))

/-- Sliding transported from a universally valid untyped law. All universes are independent. -/
theorem sliding : (slideLeft X Y).eval o τ ρ = (slideRight X Y).eval o τ ρ := by
  apply Term.eval_eq_of_erase_eval_eq
  intro B K _ _ _ σ π
  change π 0 * (π 1 * π 0)∗ = (π 0 * π 1)∗ * π 0
  kat

/-- The same test index is interpreted independently at the source and target. -/
theorem split_source_target : (splitSource X Y).eval o τ ρ = (splitTarget X Y).eval o τ ρ := by
  apply Term.eval_eq_of_erase_eval_eq
  intro B K _ _ _ σ π
  change KAT.test (σ 0) * π 0 + KAT.test ((σ 0)ᶜ) * π 0 =
    π 0 * KAT.test (σ 0) + π 0 * KAT.test ((σ 0)ᶜ)
  kat

/-- Guarding a heterogeneous action gives the inequational interface a nontrivial use. -/
theorem guarded_le : (guarded X Y).eval o τ ρ ≤ ρ 0 := by
  change (guarded X Y).eval o τ ρ ≤ (Term.act 0).eval o τ ρ
  apply Term.eval_le_of_erase_eval_le
  intro B K _ _ _ σ π
  change KAT.test (σ 0) * (π 0 * KAT.test ((σ 0)ᶜ)) ≤ π 0
  kat

/-- A test variable need not have a small index: there is no atom-bound premise. -/
example (n : ℕ) :
    (Term.add (Term.test (.tvar n)) (Term.test (.not (.tvar n))) :
      Term (source X Y) (target X Y) X X).eval o τ ρ = 𝟙 (o X) := by
  change _ = (Term.one : Term (source X Y) (target X Y) X X).eval o τ ρ
  apply Term.eval_eq_of_erase_eval_eq
  intro B K _ _ _ σ π
  change KAT.test (σ n) + KAT.test ((σ n)ᶜ) = 1
  kat

/-- Arbitrary zero and identity expressions use the support of their endpoints. -/
example : (Term.comp (.zero : Term (source X Y) (target X Y) X Y) .one).eval o τ ρ = ⊥ := by
  change _ = (Term.zero : Term (source X Y) (target X Y) X Y).eval o τ ρ
  apply Term.eval_eq_of_erase_eval_eq
  intro B K _ _ _ σ π
  change (0 : K) * 1 = 0
  exact zero_mul 1

/-- Identifying syntactic objects does not force their test valuations to coincide. -/
example (A : C) (tests : ∀ _ : I, ℕ → T A) (actions : ∀ _ : ℕ, A ⟶ A) :
    (splitSource X Y).eval (fun _ ↦ A) tests actions =
      (splitTarget X Y).eval (fun _ ↦ A) tests actions :=
  split_source_target _ tests actions

end Abstract

/-! The support proof must work over infinite and higher-universe object alphabets. -/

section LargeAlphabet

variable {C : Type v} [Category.{w} C] [KleeneCategory C]
  {T : C → Type z} [∀ A, BooleanAlgebra (T A)] [TypedKAT C T]
  (o : ULift.{u} ℕ → C) (τ : ∀ A, ℕ → T (o A))
  (ρ : ∀ a, o (source (ULift.up 0) (ULift.up 1) a) ⟶
    o (target (ULift.up 0) (ULift.up 1) a))

example : (slideLeft (ULift.up 0) (ULift.up 1)).eval o τ ρ =
    (slideRight (ULift.up 0) (ULift.up 1)).eval o τ ρ := sliding o τ ρ

example : (guarded (ULift.up 0) (ULift.up 1)).eval o τ ρ ≤ ρ 0 := guarded_le o τ ρ

end LargeAlphabet

/-! A concrete heterogeneous relational interpretation. -/

private def relObjects (n : ℕ) : RelCat := if n = 0 then ℕ else Bool

example (τ : ∀ n, ℕ → Set (relObjects n))
    (ρ : ∀ a, relObjects (source 0 1 a) ⟶ relObjects (target 0 1 a)) :
    (splitSource 0 1).eval relObjects τ ρ = (splitTarget 0 1).eval relObjects τ ρ :=
  split_source_target _ τ ρ

/-! One interpretation does not establish a universal untyped law. -/

example {C : Type v} [Category.{w} C] [KleeneCategory C]
    {T : C → Type z} [∀ A, BooleanAlgebra (T A)] [TypedKAT C T]
    (o : ℕ → C) (τ : ∀ A, ℕ → T (o A))
    (ρ : ∀ a, o (source 0 1 a) ⟶ o (target 0 1 a)) :
    (Term.act 0).eval o τ ρ = ρ 0 := by
  have h : KAT.KTerm.eval (K := _root_.Language ℕ) (T := Bool) (fun _ ↦ false) (fun _ ↦ 0)
      (.act 0) = KAT.KTerm.eval (K := _root_.Language ℕ) (T := Bool) (fun _ ↦ false) (fun _ ↦ 0)
      .zero := rfl
  fail_if_success have : (Term.act 0).eval o τ ρ =
      (Term.zero : Term (source 0 1) (target 0 1) 0 1).eval o τ ρ :=
    Term.eval_eq_of_erase_eval_eq o τ ρ h
  rfl

end TypedKAT.UntypingExamples
