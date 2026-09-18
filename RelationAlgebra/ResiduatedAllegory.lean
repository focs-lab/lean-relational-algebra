/- SPDX-License-Identifier: LGPL-3.0-or-later
Lean translation and extensions, 2026-09-18. See LICENSE and NOTICE.md. -/
import RelationAlgebra.Allegory
import RelationAlgebra.Residuated

/-!
# Residuals on a scalar allegory

The one-object `AL+DIV` fragment of Pous's `monoid.v`. Residuals are specified on
an existing allegory's order and multiplication; no joins, bounds, Boolean
complements, or Kleene star are required. The typed interface and the `End` /
`SingleObj` bridges are in `TypedResiduatedAllegory`.
-/

/-- Multiplication in an existing allegory has right adjoints in both arguments. -/
class ResiduatedAllegory (K : Type*) [Allegory K] where
  ldiv : K → K → K
  rdiv : K → K → K
  ldiv_spec (a b c : K) : b ≤ ldiv a c ↔ a * b ≤ c
  rdiv_spec (a b c : K) : a ≤ rdiv c b ↔ a * b ≤ c

namespace ResiduatedAllegory

scoped infixr:65 " ⇘ " => ldiv
scoped infixl:66 " ⇙ " => rdiv

variable {K : Type*} [Allegory K] [ResiduatedAllegory K]

theorem gc_mul_ldiv (a : K) : GaloisConnection (a * ·) (ldiv a) :=
  fun _ _ ↦ (ldiv_spec _ _ _).symm

theorem gc_mul_rdiv (b : K) : GaloisConnection (· * b) (fun c ↦ c ⇙ b) :=
  fun _ _ ↦ (rdiv_spec _ _ _).symm

theorem mul_ldiv_le (a c : K) : a * (a ⇘ c) ≤ c := (ldiv_spec _ _ _).mp le_rfl

theorem rdiv_mul_le (b c : K) : (c ⇙ b) * b ≤ c := (rdiv_spec _ _ _).mp le_rfl

theorem ldiv_le_ldiv {a a' c c' : K} (ha : a' ≤ a) (hc : c ≤ c') : a ⇘ c ≤ a' ⇘ c' :=
  (ldiv_spec _ _ _).mpr (((Allegory.mul_mono_left ha _).trans (mul_ldiv_le a c)).trans hc)

theorem rdiv_le_rdiv {b b' c c' : K} (hb : b' ≤ b) (hc : c ≤ c') : c ⇙ b ≤ c' ⇙ b' :=
  (rdiv_spec _ _ _).mpr (((Allegory.mul_mono_right hb _).trans (rdiv_mul_le b c)).trans hc)

@[simp] theorem star_ldiv (a c : K) : star (a ⇘ c) = star c ⇙ star a := by
  apply eq_of_forall_le_iff
  intro b
  rw [← Allegory.star_le_star_iff, Allegory.star_star, ldiv_spec, rdiv_spec,
    ← Allegory.star_le_star_iff, Allegory.star_mul, Allegory.star_star]

@[simp] theorem star_rdiv (c b : K) : star (c ⇙ b) = star b ⇘ star c := by
  apply eq_of_forall_le_iff
  intro a
  rw [← Allegory.star_le_star_iff, Allegory.star_star, rdiv_spec, ldiv_spec,
    ← Allegory.star_le_star_iff, Allegory.star_mul, Allegory.star_star]

end ResiduatedAllegory

/-- Forget the stronger structure, using the canonical relation-algebra residuals. -/
noncomputable instance (priority := 100) RelationAlgebra.toResiduatedAllegory
    {K : Type*} [RelationAlgebra K] : ResiduatedAllegory K where
  ldiv := (ResiduatedIdemSemiring.ofRelationAlgebra K).ldiv
  rdiv := (ResiduatedIdemSemiring.ofRelationAlgebra K).rdiv
  ldiv_spec := (ResiduatedIdemSemiring.ofRelationAlgebra K).ldiv_spec
  rdiv_spec := (ResiduatedIdemSemiring.ofRelationAlgebra K).rdiv_spec
