import RelationAlgebra.Kleene.Basic
import RelationAlgebra.Models.Rel
import Mathlib.Computability.Language

/-!
# Complete (star-continuous) Kleene algebras

A *complete Kleene algebra* is a Kleene algebra whose order is a complete lattice and whose
multiplication distributes over arbitrary joins, i.e. a unital quantale whose Kleene star is
the one of the lattice.  In such an algebra `a∗ = ⨆ n, a ^ n`
(`CompleteKleeneAlgebra.kstar_eq_iSup_pow`), and more generally every element denoted by a
regular expression is the join of the values of the words of its language.  This is the
setting in which the `ka` decision procedure of `RelationAlgebra.Decide` is sound.

Relations (`SetRel α α`) and languages (`Language α`) are complete Kleene algebras.
-/

open scoped Computability

/-- A complete Kleene algebra: a Kleene algebra which is a complete lattice (for the same order)
and in which multiplication distributes over arbitrary joins. -/
class CompleteKleeneAlgebra (K : Type*) extends KleeneAlgebra K, CompleteLattice K where
  mul_sSup_distrib (x : K) (s : Set K) : x * sSup s = ⨆ y ∈ s, x * y
  sSup_mul_distrib (s : Set K) (y : K) : sSup s * y = ⨆ x ∈ s, x * y

namespace CompleteKleeneAlgebra

variable {K : Type*} [CompleteKleeneAlgebra K]

instance (priority := 100) toIsQuantale : IsQuantale K where
  mul_sSup_distrib := CompleteKleeneAlgebra.mul_sSup_distrib
  sSup_mul_distrib := CompleteKleeneAlgebra.sSup_mul_distrib

theorem mul_iSup {ι : Sort*} (x : K) (f : ι → K) : x * ⨆ i, f i = ⨆ i, x * f i := by
  rw [← sSup_range, mul_sSup_distrib, iSup_range]

theorem iSup_mul {ι : Sort*} (f : ι → K) (y : K) : (⨆ i, f i) * y = ⨆ i, f i * y := by
  rw [← sSup_range, sSup_mul_distrib, iSup_range]

theorem bot_eq_zero : (⊥ : K) = 0 := le_antisymm bot_le zero_le

/-- In a complete Kleene algebra the star is the supremum of the powers. -/
theorem kstar_eq_iSup_pow (a : K) : a∗ = ⨆ n : ℕ, a ^ n := by
  apply le_antisymm
  · refine kstar_le_of_mul_le_right (le_iSup_of_le 0 (pow_zero a).ge) ?_
    rw [mul_iSup]
    exact iSup_le fun n ↦ le_iSup_of_le (n + 1) (pow_succ' a n).ge
  · exact iSup_le fun _ ↦ pow_le_kstar

end CompleteKleeneAlgebra

namespace SetRel

variable {α : Type*}

/-- Relations form a complete Kleene algebra. -/
scoped instance instCompleteKleeneAlgebra : CompleteKleeneAlgebra (SetRel α α) where
  __ := instKleeneAlgebra
  __ := (inferInstance : CompleteLattice (Set (α × α)))
  mul_sSup_distrib := IsQuantale.mul_sSup_distrib
  sSup_mul_distrib := IsQuantale.sSup_mul_distrib

end SetRel

namespace Language

variable {α : Type*}

/-- Languages form a complete Kleene algebra. -/
instance instCompleteKleeneAlgebra : CompleteKleeneAlgebra (Language α) where
  __ := (inferInstance : KleeneAlgebra (Language α))
  __ := (inferInstance : CompleteLattice (Language α))
  mul_sSup_distrib l s := by simp only [sSup_eq_iSup, Language.mul_iSup]
  sSup_mul_distrib s l := by simp only [sSup_eq_iSup, Language.iSup_mul]

end Language
