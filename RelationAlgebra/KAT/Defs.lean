import Mathlib.Algebra.Order.Kleene
import Mathlib.Order.BooleanAlgebra.Basic

/-!
# Kleene algebra with tests

A *Kleene algebra with tests* (KAT, Kozen 1997) is a Kleene algebra `K` together with a Boolean
algebra `T` of *tests* embedded in `K` in such a way that `⊔ ↦ +`, `⊓ ↦ *`, `⊤ ↦ 1` and `⊥ ↦ 0`.
Tests model assertions / guards, and complement `bᶜ` models negation, so that `while` programs
can be expressed in KAT (see `RelationAlgebra.KAT.Basic`) and Hoare logic can be encoded
(see `RelationAlgebra.KAT.Hoare`).

## Design

We follow the two-sorted presentation used by Pous' `relation-algebra` library for Rocq/Coq:
the tests form a separate type `T` carrying a `BooleanAlgebra` instance, and the KAT structure
is a *mixin* `KleeneAlgebraWithTests T K` on top of `[BooleanAlgebra T] [KleeneAlgebra K]`
providing the embedding `test : T → K`.  This lets us reuse Mathlib's `BooleanAlgebra` and
`KleeneAlgebra` hierarchies unchanged.  We do not require `test` to be injective: it is a
lattice homomorphism, exactly as in Pous' `kat.laws`.

## Main declarations

* `KleeneAlgebraWithTests T K` (abbreviated `KAT T K`): the class.
* `KAT.test`: the embedding of tests, with scoped notation `⌜b⌝` (in scope `KAT`).

## References

* [D. Kozen, *Kleene algebra with tests*][kozen1997]
* [D. Pous, *Kleene Algebra with Tests and Coq tools for while programs*][pous2013]
-/

open scoped Computability

/-- A Kleene algebra with tests: a Boolean algebra `T` of tests embedded into a Kleene algebra
`K` by a map `test` sending `⊥, ⊤, ⊔, ⊓` to `0, 1, +, *`. -/
class KleeneAlgebraWithTests (T : Type*) (K : Type*) [BooleanAlgebra T] [KleeneAlgebra K] where
  /-- The embedding of tests into the Kleene algebra. -/
  test : T → K
  test_bot : test ⊥ = 0
  test_top : test ⊤ = 1
  test_sup (a b : T) : test (a ⊔ b) = test a + test b
  test_inf (a b : T) : test (a ⊓ b) = test a * test b

/-- `KAT T K` abbreviates `KleeneAlgebraWithTests T K`. -/
abbrev KAT := KleeneAlgebraWithTests

namespace KAT

export KleeneAlgebraWithTests (test test_bot test_top test_sup test_inf)

attribute [simp] test_bot test_top test_sup test_inf

/-- `⌜b⌝` is the test `b` regarded as an element of the Kleene algebra. -/
scoped notation:max "⌜" b "⌝" => KleeneAlgebraWithTests.test b

end KAT
