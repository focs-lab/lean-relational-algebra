import RelationAlgebra.Decide.Tactic
import RelationAlgebra.Decide.KATTactic
import RelationAlgebra.Decide.HKATTactic

/-!
# Examples for the `ka` and `kat` tactics
-/

open scoped Computability

section AbstractKleeneAlgebra

/-! ### `ka` in an arbitrary Kleene algebra

Since `ka` rests on Kozen's completeness theorem it needs no completeness assumption on the
algebra: these goals are stated for an abstract `[KleeneAlgebra K]`. -/

variable {K : Type*} [KleeneAlgebra K] (a b c : K)

example : (a + b)∗ = a∗ * (b * a∗)∗ := by ka

example : a * (b * a)∗ = (a * b)∗ * a := by ka

example : (a∗)∗ = a∗ := by ka

example : 1 + a * a∗ = a∗ := by ka

example : (a + b + c)∗ = (a∗ * (b + c))∗ * a∗ := by ka

example : a∗ * a∗ ≤ a∗ := by ka

example : a * b ≤ (a + b)∗ := by ka

example : (a * b)∗ * a = a * (b * a)∗ := by ka

/-- `ka` rejects an identity that is not valid in all Kleene algebras. -/
example : True := by
  have : ¬ (∀ (K : Type) (_ : KleeneAlgebra K) (x y : K), x * y = y * x) := by
    intro h
    have := h (Language Bool) inferInstance {[true]} {[false]}
    have hmem : [true, false] ∈ ({[true]} * {[false]} : Language Bool) :=
      Language.mem_mul.2 ⟨[true], rfl, [false], rfl, rfl⟩
    rw [this] at hmem
    obtain ⟨u, hu, v, hv, huv⟩ := Language.mem_mul.1 hmem
    rw [show u = [false] from hu, show v = [true] from hv] at huv
    exact absurd huv (by decide)
  trivial

end AbstractKleeneAlgebra

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

section KATAbstract

/-! ### `kat` and `hkat` in an *arbitrary* Kleene algebra with tests

Since `KAT.Completeness.eval_eq_of_decideEq`, the two tactics no longer need the carrier to be a
complete Kleene algebra: an arbitrary `KleeneAlgebra` carrying a `KleeneAlgebraWithTests`
instance is enough, and the test algebra is an arbitrary `BooleanAlgebra`. -/

open scoped Computability KAT

example {T K : Type*} [BooleanAlgebra T] [KleeneAlgebra K] [KAT T K]
    (b : T) (p : K) : KAT.HoareTriple ⊤ (KAT.whileDo b p) bᶜ := by kat

example {T K : Type*} [BooleanAlgebra T] [KleeneAlgebra K] [KAT T K]
    (b : T) (p : K) (h : KAT.HoareTriple b p b) : KAT.HoareTriple b p∗ b := by hkat

/-- An inequality in an abstract KAT. -/
example {T K : Type*} [BooleanAlgebra T] [KleeneAlgebra K] [KAT T K]
    (b c : T) (p : K) : ⌜b⌝ * p ≤ p + ⌜c⌝ := by kat

/-- `\` and `⇨` are normalised before reification, in an abstract KAT too. -/
example {T K : Type*} [BooleanAlgebra T] [KleeneAlgebra K] [KAT T K]
    (b c : T) (p : K) : ⌜b \ c⌝ * p = ⌜b⌝ * ⌜cᶜ⌝ * p := by kat

example {T K : Type*} [BooleanAlgebra T] [KleeneAlgebra K] [KAT T K] (b c : T) :
    (⌜b ⇨ c⌝ : K) = ⌜bᶜ⌝ + ⌜c⌝ := by kat

/-- Loop unrolling, with the guard an abstract test. -/
example {T K : Type*} [BooleanAlgebra T] [KleeneAlgebra K] [KAT T K] (b : T) (p : K) :
    KAT.whileDo b p = KAT.ifThenElse b (p * KAT.whileDo b p) 1 := by kat

/-- Binders introduced by the tactic itself, over an abstract carrier. -/
example {T K : Type*} [BooleanAlgebra T] [KleeneAlgebra K] [KAT T K] :
    ∀ p q : K, p ≤ 0 → q ≤ 0 → p + q = 0 := by hkat

-- Several goals: `kat` acts on the main goal only.
set_option linter.style.multiGoal false in
example {T K : Type*} [BooleanAlgebra T] [KleeneAlgebra K] [KAT T K] (b : T) (p : K) :
    ⌜b⌝ * p = ⌜b⌝ * ⌜b⌝ * p ∧ True := by
  constructor
  kat
  trivial

-- Invalid identities are rejected, not proved.
set_option linter.unusedVariables false in
example {T K : Type*} [BooleanAlgebra T] [KleeneAlgebra K] [KAT T K] (p q : K) (b : T) :
    True := by
  fail_if_success (have : p * q = q * p := by kat)
  fail_if_success (have : p ≤ q := by kat)
  fail_if_success (have : (⌜b⌝ : K) = 1 := by kat)
  trivial

end KATAbstract

section KATLanguages

open scoped KAT

variable {σ : Type*} (a b : Language σ)

/-- Trivial (`Bool`) tests. -/
example : KAT.ifThenElse (⊤ : Bool) a b = a := by kat

example (c : Bool) : KAT.ifThenElse c a a = a := by kat

end KATLanguages
