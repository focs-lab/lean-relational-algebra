import RelationAlgebra.KAT.Defs

/-!
# The trivial tests

Every Kleene algebra `K` is a Kleene algebra with tests over the two-element Boolean algebra
`Bool`, with `test true = 1` and `test false = 0`.  In particular Mathlib's `Language α` is a
KAT this way.
-/

open scoped Computability

/-- Every Kleene algebra has the trivial tests `{0, 1}`. -/
instance Bool.instKAT (K : Type*) [KleeneAlgebra K] : KleeneAlgebraWithTests Bool K where
  test b := cond b 1 0
  test_bot := rfl
  test_top := rfl
  test_sup a b := by cases a <;> cases b <;> simp
  test_inf a b := by cases a <;> cases b <;> simp

theorem KAT.test_bool {K : Type*} [KleeneAlgebra K] (b : Bool) :
    (KAT.test b : K) = cond b 1 0 := rfl
