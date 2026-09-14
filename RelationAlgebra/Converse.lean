import Mathlib.Algebra.Star.Basic
import Mathlib.Order.BooleanAlgebra.Basic
import RelationAlgebra.Kleene.Basic
import RelationAlgebra.Models.Rel

/-!
# Converse, Kleene algebras with converse, and relation algebras

This file adds the *converse* operation `a ↦ aᵒ` (the transpose of a relation) to the Kleene
algebra hierarchy, following Damien Pous' Rocq library `relation-algebra` and Tarski's
axiomatisation of relation algebras.

## Design

* **Converse is Mathlib's `star`.**  Mathlib already has a hierarchy of involutive
  star operations (`Star`, `InvolutiveStar`, `StarMul`, `StarAddMonoid`, `StarRing` in
  `Mathlib.Algebra.Star.Basic`), whose axioms are precisely those of converse:
  `star (star a) = a`, `star (a * b) = star b * star a` and `star (a + b) = star a + star b`.
  We therefore do **not** introduce a new "converse" class: a *Kleene algebra with converse* is
  just a type with `[KleeneAlgebra K] [StarRing K]`.  The remaining law of Pous'
  `KleeneAlgebraWithConverse`, namely `star (a∗) = (star a)∗`, is derivable
  (`KleeneAlgebra.star_kstar`), as is monotonicity of `star` (`KleeneAlgebra.star_mono`).

* **Relation algebras.**  A `RelationAlgebra` is a Kleene algebra whose order is a Boolean
  algebra, equipped with an involutive, anti-multiplicative and additive converse satisfying
  the *Dedekind law*
  ```
  (a * b) ⊓ c ≤ (a ⊓ c * star b) * (b ⊓ star a * c).
  ```
  Every `RelationAlgebra` is a `StarRing`, so the results of the first section apply.  From
  Dedekind's law we derive the one-sided modular laws, the Schröder rules, Tarski's law and the
  usual interaction of converse with the Boolean operations (`star_compl`, `star_inf`,
  `star_top`, ...).

* **The relational model.**  Binary relations `SetRel α α` form a relation algebra with
  `star R = R.inv` (Mathlib's `SetRel.inv`), on top of the scoped Kleene algebra instance of
  `RelationAlgebra.Models.Rel` and the Boolean algebra of sets.  As there, the instance is
  scoped: use `open scoped SetRel`.

## References

* [A. Tarski, *On the calculus of relations*, J. Symb. Logic 6 (1941)]
* [D. Pous, *Relation Algebra and KAT in Coq*, <https://github.com/damien-pous/relation-algebra>]
* [D. Kozen, *A completeness theorem for Kleene algebras and the algebra of regular events*]
-/

open scoped Computability

/-! ### Kleene algebras with converse -/

namespace KleeneAlgebra

variable {K : Type*} [KleeneAlgebra K] [StarRing K] {a b : K}

/-- Converse is monotone: this follows from additivity, since `a ≤ b ↔ a + b = b`. -/
theorem star_mono : Monotone (star : K → K) := fun _ _ h ↦
  add_eq_right_iff_le.1 <| by rw [← star_add, add_eq_right_iff_le.2 h]

theorem star_le_star_iff : star a ≤ star b ↔ a ≤ b :=
  ⟨fun h ↦ by simpa using star_mono h, fun h ↦ star_mono h⟩

theorem star_le_iff : star a ≤ b ↔ a ≤ star b := by
  rw [← star_le_star_iff, star_star]

theorem le_star_iff : a ≤ star b ↔ star a ≤ b := star_le_iff.symm

theorem star_sup (a b : K) : star (a ⊔ b) = star a ⊔ star b := by
  simp only [← add_eq_sup, star_add]

theorem star_bot : star (⊥ : K) = ⊥ := by rw [bot_eq_zero, star_zero]

theorem kstar_star_le : (star a)∗ ≤ star (a∗) := by
  refine kstar_le_of_mul_le_right (by simpa using star_mono (one_le_kstar (a := a))) ?_
  rw [← star_mul]
  exact star_mono kstar_mul_le_kstar

/-- Converse commutes with the Kleene star: `(a∗)ᵒ = (aᵒ)∗`.  This is the remaining axiom of a
"Kleene algebra with converse", here derived from the `StarRing` laws. -/
theorem star_kstar (a : K) : star (a∗) = (star a)∗ := by
  refine le_antisymm ?_ kstar_star_le
  have h : a∗ ≤ star ((star a)∗) := by simpa using (kstar_star_le (a := star a))
  simpa using star_mono h

theorem kstar_star (a : K) : (star a)∗ = star (a∗) := (star_kstar a).symm

end KleeneAlgebra

/-! ### Relation algebras -/

/-- A **relation algebra** (Tarski) is a Kleene algebra whose order is a Boolean algebra,
equipped with a converse `star` that is involutive, anti-multiplicative and additive, and
satisfies the Dedekind (modular) law
`(a * b) ⊓ c ≤ (a ⊓ c * star b) * (b ⊓ star a * c)`.

The Kleene-algebra order, join and bottom coincide with those of the Boolean algebra.  Note that
Tarski's original axioms are stated without the Kleene star; here `star` and `∗` coexist, with
`∗` denoting the reflexive-transitive closure and `star` the converse. -/
class RelationAlgebra (K : Type*) extends KleeneAlgebra K, BooleanAlgebra K, Star K where
  /-- Converse is an involution. -/
  star_involutive : Function.Involutive (star : K → K)
  /-- Converse reverses composition. -/
  star_mul (a b : K) : star (a * b) = star b * star a
  /-- Converse is additive. -/
  star_add (a b : K) : star (a + b) = star a + star b
  /-- The Dedekind (modular) law. -/
  dedekind (a b c : K) : (a * b) ⊓ c ≤ (a ⊓ c * star b) * (b ⊓ star a * c)

namespace RelationAlgebra

variable {K : Type*} [RelationAlgebra K] {a b c : K}

/-- The converse of a relation algebra makes it a `StarRing` (hence an `InvolutiveStar`,
a `StarMul` and a `StarAddMonoid`), so that `KleeneAlgebra.star_mono`,
`KleeneAlgebra.star_kstar`, ... apply. -/
instance (priority := 100) toStarRing : StarRing K where
  star_involutive := RelationAlgebra.star_involutive
  star_mul := RelationAlgebra.star_mul
  star_add := RelationAlgebra.star_add

/-! #### Modular laws -/

/-- The left-handed modular law `(a b) ⊓ c ≤ (a ⊓ c bᵒ) b`. -/
theorem mul_inf_le_inf_mul (a b c : K) : (a * b) ⊓ c ≤ (a ⊓ c * star b) * b :=
  (dedekind a b c).trans (mul_le_mul_right inf_le_left _)

/-- The right-handed modular law `(a b) ⊓ c ≤ a (b ⊓ aᵒ c)`. -/
theorem mul_inf_le_mul_inf (a b c : K) : (a * b) ⊓ c ≤ a * (b ⊓ star a * c) :=
  (dedekind a b c).trans (mul_le_mul_left inf_le_left _)

/-- Every element is "partially reflexive": `a ≤ a aᵒ a`. -/
theorem le_mul_star_mul (a : K) : a ≤ a * star a * a :=
  calc a = (a * 1) ⊓ a := by rw [mul_one, inf_idem]
    _ ≤ a * (1 ⊓ star a * a) := mul_inf_le_mul_inf a 1 a
    _ ≤ a * (star a * a) := mul_le_mul_right inf_le_right _
    _ = a * star a * a := (mul_assoc _ _ _).symm

/-! #### Schröder rules and Tarski's law -/

theorem star_mul_compl_le_compl (h : a * b ≤ c) : star a * cᶜ ≤ bᶜ := by
  rw [le_compl_iff_disjoint_right, disjoint_iff_inf_le]
  calc (star a * cᶜ) ⊓ b ≤ star a * (cᶜ ⊓ star (star a) * b) := mul_inf_le_mul_inf _ _ _
    _ = star a * (cᶜ ⊓ a * b) := by rw [star_star]
    _ ≤ star a * (cᶜ ⊓ c) := mul_le_mul_right (inf_le_inf_left _ h) _
    _ = ⊥ := by rw [compl_inf_eq_bot, bot_eq_zero, mul_zero]

theorem compl_mul_star_le_compl (h : a * b ≤ c) : cᶜ * star b ≤ aᶜ := by
  rw [le_compl_iff_disjoint_right, disjoint_iff_inf_le]
  calc (cᶜ * star b) ⊓ a ≤ (cᶜ ⊓ a * star (star b)) * star b := mul_inf_le_inf_mul _ _ _
    _ = (cᶜ ⊓ a * b) * star b := by rw [star_star]
    _ ≤ (cᶜ ⊓ c) * star b := mul_le_mul_left (inf_le_inf_left _ h) _
    _ = ⊥ := by rw [compl_inf_eq_bot, bot_eq_zero, zero_mul]

/-- The first **Schröder rule**: `a b ≤ c ↔ aᵒ cᶜ ≤ bᶜ`. -/
theorem schroeder_left : a * b ≤ c ↔ star a * cᶜ ≤ bᶜ :=
  ⟨star_mul_compl_le_compl, fun h ↦ by simpa using star_mul_compl_le_compl h⟩

/-- The second **Schröder rule**: `a b ≤ c ↔ cᶜ bᵒ ≤ aᶜ`. -/
theorem schroeder_right : a * b ≤ c ↔ cᶜ * star b ≤ aᶜ :=
  ⟨compl_mul_star_le_compl, fun h ↦ by simpa using compl_mul_star_le_compl h⟩

/-- **Tarski's law**: `aᵒ (a b)ᶜ ≤ bᶜ`. -/
theorem tarski (a b : K) : star a * (a * b)ᶜ ≤ bᶜ :=
  star_mul_compl_le_compl le_rfl

/-- The mirror image of Tarski's law: `(a b)ᶜ bᵒ ≤ aᶜ`. -/
theorem tarski' (a b : K) : (a * b)ᶜ * star b ≤ aᶜ :=
  compl_mul_star_le_compl le_rfl

/-! #### Converse and the Boolean operations

Since `star` is a monotone involution, it is an order automorphism, and hence preserves all
the lattice structure. -/

theorem star_inf (a b : K) : star (a ⊓ b) = star a ⊓ star b := by
  have key : ∀ x y : K, star (x ⊓ y) ≤ star x ⊓ star y := fun x y ↦
    le_inf (KleeneAlgebra.star_mono inf_le_left) (KleeneAlgebra.star_mono inf_le_right)
  refine (key a b).antisymm ?_
  have h := KleeneAlgebra.star_mono (key (star a) (star b))
  simpa using h

theorem star_top : star (⊤ : K) = ⊤ :=
  -- `_root_`: the class inherits `BooleanAlgebra`'s (unprotected) field `le_top`.
  le_antisymm _root_.le_top (KleeneAlgebra.le_star_iff.2 _root_.le_top)

theorem star_bot : star (⊥ : K) = ⊥ := KleeneAlgebra.star_bot

theorem star_sup (a b : K) : star (a ⊔ b) = star a ⊔ star b := KleeneAlgebra.star_sup a b

/-- Converse commutes with complement. -/
theorem star_compl (a : K) : star aᶜ = (star a)ᶜ := by
  refine (compl_unique ?_ ?_).symm
  · rw [← star_inf, inf_compl_eq_bot, star_bot]
  · rw [← star_sup, sup_compl_eq_top, star_top]

theorem star_sdiff (a b : K) : star (a \ b) = star a \ star b := by
  rw [sdiff_eq, sdiff_eq, star_inf, star_compl]

/-- Converse commutes with the Kleene star (restated from `KleeneAlgebra.star_kstar`). -/
theorem star_kstar (a : K) : star (a∗) = (star a)∗ := KleeneAlgebra.star_kstar a

theorem star_le_star_iff : star a ≤ star b ↔ a ≤ b := KleeneAlgebra.star_le_star_iff

end RelationAlgebra

/-! ### The relational model -/

namespace SetRel

variable {α : Type*} {R : SetRel α α} {a b : α}

/-- Binary relations on `α` form a relation algebra, with converse `star R = R.inv`. -/
scoped instance instRelationAlgebra : RelationAlgebra (SetRel α α) where
  __ := instKleeneAlgebra
  __ := (inferInstance : BooleanAlgebra (Set (α × α)))
  star := inv
  star_involutive _ := inv_inv
  star_mul := inv_comp
  star_add _ _ := Set.preimage_union
  dedekind R S T := by
    rintro ⟨a, c⟩ ⟨⟨b, hab, hbc⟩, hac⟩
    exact ⟨b, ⟨hab, c, hac, hbc⟩, hbc, a, hab, hac⟩

theorem star_def (R : SetRel α α) : star R = R.inv := rfl

@[simp] theorem mem_star : a ~[star R] b ↔ b ~[R] a := Iff.rfl

end SetRel
