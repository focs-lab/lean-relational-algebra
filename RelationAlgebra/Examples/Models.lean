import RelationAlgebra.Models.Trace
import RelationAlgebra.Models.SetoidRel
import RelationAlgebra.Models.FinRel
import RelationAlgebra.Models.MatrixExt
import RelationAlgebra.Decide.Tactic

/-!
# Regression examples across the models

Since `ka` rests on Kozen's completeness theorem
(`KleeneAlgebra.Term.completeness_eq`), it applies to every Kleene algebra: the abstract one,
the concrete models of this library, and matrices over any of them.  These examples pin that
down, and double as a check that the various scoped instance sets are coherent.

The `kat` tactic is not exercised here; it still requires a `CompleteKleeneAlgebra`, so its
examples live in `RelationAlgebra.Examples.Decide`.
-/

open scoped Computability SetRel KAT TraceLang

/-! ### An abstract Kleene algebra -/

example {K : Type*} [KleeneAlgebra K] (a b : K) : (a + b)∗ = a∗ * (b * a∗)∗ := by ka

example {K : Type*} [KleeneAlgebra K] (a b : K) : a * (b * a)∗ = (a * b)∗ * a := by ka

example {K : Type*} [KleeneAlgebra K] (a b c : K) :
    ((a + b)∗ * c)∗ = 1 + (a + b + c)∗ * c := by ka

example {K : Type*} [KleeneAlgebra K] (a b c : K) :
    a * b * c * (a * b * c)∗ * a = a * (b * c * a)∗ * b * c * a := by ka

example {K : Type*} [KleeneAlgebra K] (a b c : K) :
    (a + b + c + a * b)∗ = (a + b + c)∗ := by ka

/-! ### Matrices over an abstract Kleene algebra -/

example {K : Type*} [KleeneAlgebra K] (M N : Matrix (Fin 2) (Fin 2) K) :
    M * (N * M)∗ = (M * N)∗ * M := by ka

example {K : Type*} [KleeneAlgebra K] (M : Matrix (Fin 3) (Fin 3) K) :
    (M∗)∗ = M∗ := by ka

/-! ### Relations -/

example {α : Type*} (R S : SetRel α α) : (R + S)∗ = (R∗ * S∗)∗ := by ka

/-! ### Trace languages -/

example {σ α : Type*} (x y : TraceLang σ α) : (x + y)∗ = x∗ * (y * x∗)∗ := by ka

/-! ### Setoid relations -/

example {α : Type*} [Setoid α] (R : SetoidRel α) : R∗ * R∗ = R∗ := by ka

/-! ### Finite relations -/

example {α : Type*} [Fintype α] [DecidableEq α] (R : FinRel α α) : 1 + R * R∗ = R∗ := by ka

/-! ### Languages -/

example {σ : Type*} (a b : Language σ) : (a + b)∗ = a∗ * (b * a∗)∗ := by ka

/-! ### `ka` rejects a non-identity

`ka` proves only identities valid in every Kleene algebra.  Commutativity of multiplication is
not one, as the language model witnesses. -/
example : ¬ ∀ (K : Type) (_ : KleeneAlgebra K) (x y : K), x * y = y * x := by
  intro h
  have hcomm := h (Language Bool) inferInstance {[true]} {[false]}
  have hmem : [true, false] ∈ ({[true]} * {[false]} : Language Bool) :=
    Language.mem_mul.2 ⟨[true], rfl, [false], rfl, rfl⟩
  rw [hcomm] at hmem
  obtain ⟨u, hu, v, hv, huv⟩ := Language.mem_mul.1 hmem
  rw [show u = [false] from hu, show v = [true] from hv] at huv
  exact absurd huv (by decide)
