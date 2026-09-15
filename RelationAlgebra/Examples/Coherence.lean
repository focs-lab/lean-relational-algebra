import RelationAlgebra.Models.FinRel
import RelationAlgebra.Models.MatrixExt
import RelationAlgebra.Models.Trace
import RelationAlgebra.Models.SetoidRel

/-!
# Instance-coherence regressions

Several types in this library carry more than one algebraic structure: a `KleeneAlgebra`, a
`CompleteKleeneAlgebra` refining it, a `RelationAlgebra` refining it again, and a `KAT`
instance on top.  If one of those were built independently rather than from the others, the
library would silently contain two different Kleene stars on the same type and theorems proved
about one would not apply to the other.

Each `example` below pins a refinement down to `rfl`, so that a future change introducing such
a diamond fails the build instead of passing unnoticed.
-/

open scoped Computability SetRel KAT TraceLang

/-- Complete Kleene algebras of matrices refine the plain matrix Kleene algebra. -/
example {α n : Type*} [Fintype n] [DecidableEq n] :
    (Matrix.instCompleteKleeneAlgebra :
        CompleteKleeneAlgebra (Matrix n n (SetRel α α))).toKleeneAlgebra
      = Matrix.instKleeneAlgebra := rfl

/-- The relation algebra of relations refines their Kleene algebra. -/
example {α : Type*} :
    (SetRel.instRelationAlgebra : RelationAlgebra (SetRel α α)).toKleeneAlgebra
      = SetRel.instKleeneAlgebra := rfl

/-- The matrix star is the supremum of the powers when the coefficients are complete. -/
example {α : Type*} (M : Matrix (Fin 2) (Fin 2) (SetRel α α)) :
    M∗ = ⨆ i : ℕ, M ^ i := Matrix.kstar_eq_iSup_pow M

/-- The computable star on `Fin n`-indexed matrices agrees with the general one. -/
example {K : Type*} [KleeneAlgebra K] (M : Matrix (Fin 3) (Fin 3) K) :
    Matrix.kstarFin M = M∗ := Matrix.kstarFin_eq M

/-- The computable finite-relation model agrees with the reference relational model, star
included. -/
example {α : Type*} [Fintype α] [DecidableEq α] (R : FinRel α α) :
    FinRel.toSetRel (R∗) = (FinRel.toSetRel R)∗ := FinRel.toSetRel_kstar R
