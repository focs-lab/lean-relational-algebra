import RelationAlgebra.Kleene.Iteration
import RelationAlgebra.Automata.ZeroOne

/-!
# Nonempty paths in zero-one matrices

Strict iteration of a zero-one adjacency matrix computes transitive closure, including
cycles and excluding paths of length zero. Coefficients may be any Kleene algebra;
no Boolean, complete-lattice or nontriviality assumption is needed.
-/

open scoped Computability

namespace Matrix

variable {K : Type*} [KleeneAlgebra K] {n : Type*} [Fintype n] [DecidableEq n]

theorem ofRel_kplus (r : n → n → Prop) :
    (ofRel K r)⁺ = ofRel K (Relation.TransGen r) := by
  rw [KleeneAlgebra.kplus_eq_mul_kstar, ofRel_kstar, ofRel_comp]
  exact ofRel_congr fun _ _ ↦ (Relation.TransGen.head'_iff (r := r)).symm

end Matrix
