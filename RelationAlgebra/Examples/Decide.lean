import RelationAlgebra.Decide.Tactic
import RelationAlgebra.Decide.KATTactic

/-!
# Examples for the `ka` and `kat` tactics
-/

open scoped Computability

section Relations

open scoped SetRel

variable {α : Type*} (R S T : SetRel α α)

example : (R + S)∗ = R∗ * (S * R∗)∗ := by ka

example : R * (S * R)∗ = (R * S)∗ * R := by ka

example : R∗ * R∗ ≤ R∗ := by ka

example : (R∗)∗ = R∗ := by ka

example : (R + S + T)∗ = (R∗ * (S + T))∗ * R∗ := by ka

example : R * S ≤ (R + S)∗ := by ka

example : 1 + R * R∗ = R∗ := by ka

example : R * 0 + S = S := by ka

end Relations

section Languages

variable {σ : Type*} (a b : Language σ)

example : (a + b)∗ = (a∗ * b∗)∗ := by ka

example : a * (b * a)∗ = (a * b)∗ * a := by ka

end Languages

/-! ### The `kat` tactic -/

section KATRelations

open scoped KAT SetRel

variable {α : Type*} (s t : Set α) (R S : SetRel α α)

example : (⌜s⌝ : SetRel α α) * ⌜t⌝ = ⌜t⌝ * ⌜s⌝ := by kat

example : (⌜s⌝ : SetRel α α) * ⌜sᶜ⌝ = 0 := by kat

example : ⌜s ⊔ t⌝ * R = ⌜s⌝ * R + ⌜t⌝ * R := by kat

example : KAT.ifThenElse s R S = KAT.ifThenElse sᶜ S R := by kat

example : KAT.ifThenElse s (KAT.ifThenElse s R S) R = KAT.ifThenElse s R R := by kat

example : KAT.whileDo s R = KAT.ifThenElse s (R * KAT.whileDo s R) 1 := by kat

/-- `while b do p` is `while b do (p; while b do p)`. -/
example : KAT.whileDo s R = KAT.whileDo s (R * KAT.whileDo s R) := by kat

example : KAT.HoareTriple ⊤ (KAT.whileDo s R) sᶜ := by kat

example : ⌜s⌝ * R ≤ R + ⌜t⌝ := by kat

/-- `\` and `⇨` on tests are normalised before reification. -/
example : ⌜s \ t⌝ * R = ⌜s⌝ * ⌜tᶜ⌝ * R := by kat

example : ⌜s ⇨ t⌝ = (⌜sᶜ⌝ : SetRel α α) + ⌜t⌝ := by kat

/-- The preprocessing alone may close the goal. -/
example : KAT.HoareTriple s R t = (⌜s⌝ * R * ⌜tᶜ⌝ = 0) := by kat

-- `kat` acts on the main goal only; other goals are left alone.
set_option linter.style.multiGoal false in
example (R : SetRel ℕ ℕ) : R = R ∧ True := by
  constructor
  kat
  trivial

end KATRelations

section KATLanguages

open scoped KAT

variable {σ : Type*} (a b : Language σ)

/-- Trivial (`Bool`) tests. -/
example : KAT.ifThenElse (⊤ : Bool) a b = a := by kat

example (c : Bool) : KAT.ifThenElse c a a = a := by kat

end KATLanguages
