import RelationAlgebra.Allegory

/-!
# Vectors, points, and order-theoretic predicates in a relation algebra

This file continues the port of upstream `theories/relalg.v` begun in
`RelationAlgebra/Converse.lean` (Dedekind, Schröder, Tarski) and
`RelationAlgebra/Allegory.lean` (functional, total, injective, surjective, maps), with the
remaining standard predicates on the elements of a relation algebra:

* `Allegory.IsVector x` : `x * ⊤ = x`, a *vector* (a left ideal; in the relational model, a
  relation of the form `s ×ˢ Set.univ`);
* `Allegory.IsPoint p` : a nonempty injective vector, i.e. a single element of the carrier
  seen as a relation;
* the order-theoretic predicates `IsReflexive`, `IsIrreflexive`, `IsTransitive`,
  `IsSymmetric`, `IsAntisymmetric`, and the combinations `IsPer`, `IsPreorder`, `IsOrder`.

Each predicate is proved equivalent to its pointwise meaning in the relational model, which is
what validates the abstract definitions.

## References

* Damien Pous, `relation-algebra`, `theories/relalg.v`.
* A. Tarski, *On the calculus of relations*, Journal of Symbolic Logic 6(3), 1941.
-/

open scoped Computability

namespace Allegory

variable {K : Type*} [RelationAlgebra K] {x y p : K}

/-! ### Vectors -/

/-- A *vector* absorbs right multiplication by `⊤`.  In the relational model these are the
relations of the form `s ×ˢ Set.univ`. -/
def IsVector (x : K) : Prop := x * ⊤ = x

theorem le_mul_top (x : K) : x ≤ x * ⊤ := by
  conv_lhs => rw [← mul_one x]
  exact mul_le_mul_right _root_.le_top x

theorem isVector_iff : IsVector x ↔ x * ⊤ ≤ x :=
  ⟨fun h ↦ h.le, fun h ↦ h.antisymm (le_mul_top x)⟩

theorem IsVector.mul_top (h : IsVector x) : x * ⊤ = x := h

@[simp] theorem isVector_zero : IsVector (0 : K) := by simp [IsVector]

@[simp] theorem isVector_top : IsVector (⊤ : K) := isVector_iff.2 _root_.le_top

theorem IsVector.add (hx : IsVector x) (hy : IsVector y) : IsVector (x + y) := by
  rw [IsVector, add_mul, hx, hy]

theorem IsVector.mul_left (h : IsVector y) (x : K) : IsVector (x * y) := by
  rw [IsVector, mul_assoc, h]

theorem IsVector.inf (hx : IsVector x) (hy : IsVector y) : IsVector (x ⊓ y) := by
  refine isVector_iff.2 (_root_.le_inf ?_ ?_)
  · exact le_trans (mul_le_mul_left _root_.inf_le_left _) hx.le
  · exact le_trans (mul_le_mul_left _root_.inf_le_right _) hy.le

/-! ### Points -/

/-- A *point* is a nonempty injective vector: in the relational model, `{a} ×ˢ Set.univ` for a
single element `a`. -/
structure IsPoint (p : K) : Prop where
  /-- A point is a vector. -/
  isVector : IsVector p
  /-- A point is injective. -/
  injective : Injective p
  /-- A point is nonempty. -/
  nonempty : ⊤ * p = ⊤

theorem IsPoint.mul_top (h : IsPoint p) : p * ⊤ = p := h.isVector

/-! ### Order-theoretic predicates -/

/-- `x` is reflexive. -/
def IsReflexive (x : K) : Prop := 1 ≤ x

/-- `x` is irreflexive. -/
def IsIrreflexive (x : K) : Prop := x ⊓ 1 = 0

/-- `x` is transitive. -/
def IsTransitive (x : K) : Prop := x * x ≤ x

/-- `x` is symmetric. -/
def IsSymmetric (x : K) : Prop := star x = x

/-- `x` is antisymmetric. -/
def IsAntisymmetric (x : K) : Prop := x ⊓ star x ≤ 1

/-- `x` is a partial equivalence relation. -/
structure IsPer (x : K) : Prop where
  /-- A partial equivalence relation is symmetric. -/
  symmetric : IsSymmetric x
  /-- A partial equivalence relation is transitive. -/
  transitive : IsTransitive x

/-- `x` is a preorder. -/
structure IsPreorder (x : K) : Prop where
  /-- A preorder is reflexive. -/
  reflexive : IsReflexive x
  /-- A preorder is transitive. -/
  transitive : IsTransitive x

/-- `x` is a partial order. -/
structure IsOrder (x : K) : Prop where
  /-- A partial order is a preorder. -/
  isPreorder : IsPreorder x
  /-- A partial order is antisymmetric. -/
  antisymmetric : IsAntisymmetric x

@[simp] theorem isSymmetric_one : IsSymmetric (1 : K) := star_one

@[simp] theorem isSymmetric_top : IsSymmetric (⊤ : K) := RelationAlgebra.star_top

theorem IsSymmetric.inf (hx : IsSymmetric x) (hy : IsSymmetric y) : IsSymmetric (x ⊓ y) := by
  rw [IsSymmetric, RelationAlgebra.star_inf, hx, hy]

theorem IsSymmetric.add (hx : IsSymmetric x) (hy : IsSymmetric y) : IsSymmetric (x + y) := by
  rw [IsSymmetric, RelationAlgebra.star_add, hx, hy]

/-- A reflexive and transitive element is its own Kleene star. -/
theorem IsPreorder.kstar_eq (h : IsPreorder x) : x∗ = x := by
  refine kstar_eq_self.2 ⟨le_antisymm h.transitive ?_, h.reflexive⟩
  conv_lhs => rw [← mul_one x]
  exact mul_le_mul_right h.reflexive x

/-- The Kleene star of any element is a preorder. -/
theorem isPreorder_kstar (x : K) : IsPreorder (x∗) :=
  ⟨one_le_kstar, (kstar_mul_kstar x).le⟩

end Allegory

/-! ### The relational model -/

namespace SetRel

open scoped SetRel
open Allegory

variable {α : Type*} {R : SetRel α α}

theorem isVector_iff_forall : IsVector R ↔ ∀ a b c, a ~[R] b → a ~[R] c := by
  constructor
  · intro h a b c hab
    have hmem : a ~[R * (⊤ : SetRel α α)] c := ⟨b, hab, trivial⟩
    rwa [h] at hmem
  · intro h
    refine le_antisymm ?_ (Allegory.le_mul_top R)
    rintro ⟨a, c⟩ ⟨b, hab, -⟩
    exact h a b c hab

theorem isReflexive_iff : IsReflexive R ↔ ∀ a, a ~[R] a :=
  ⟨fun h a ↦ @h (a, a) rfl, fun h ↦ by
    rintro ⟨a, b⟩ (hab : a = b)
    exact hab ▸ h a⟩

theorem isTransitive_iff : IsTransitive R ↔ ∀ a b c, a ~[R] b → b ~[R] c → a ~[R] c :=
  ⟨fun h a b c hab hbc ↦ @h (a, c) ⟨b, hab, hbc⟩, fun h ↦ by
    rintro ⟨a, c⟩ ⟨b, hab, hbc⟩
    exact h a b c hab hbc⟩

theorem isSymmetric_iff : IsSymmetric R ↔ ∀ a b, a ~[R] b → b ~[R] a := by
  constructor
  · intro h a b hab
    have hmem : b ~[star R] a := hab
    rwa [h] at hmem
  · intro h
    ext ⟨a, b⟩
    exact ⟨fun hab ↦ h b a hab, fun hab ↦ h a b hab⟩

theorem isAntisymmetric_iff : IsAntisymmetric R ↔ ∀ a b, a ~[R] b → b ~[R] a → a = b :=
  ⟨fun h a b hab hba ↦ @h (a, b) ⟨hab, hba⟩, fun h ↦ by
    rintro ⟨a, b⟩ ⟨hab, hba⟩
    exact h a b hab hba⟩

theorem isIrreflexive_iff : IsIrreflexive R ↔ ∀ a, ¬ a ~[R] a := by
  constructor
  · intro h a haa
    have hmem : (a, a) ∈ (R ⊓ 1 : SetRel α α) := ⟨haa, rfl⟩
    rw [h] at hmem
    exact hmem
  · intro h
    ext ⟨a, b⟩
    refine ⟨fun hab ↦ ?_, fun hab ↦ absurd hab (by simp)⟩
    obtain ⟨hR, (hab' : a = b)⟩ := hab
    exact absurd (hab' ▸ hR) (h a)

end SetRel
