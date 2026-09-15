import RelationAlgebra.KAT.Basic
import RelationAlgebra.Models.MatrixExt
import RelationAlgebra.Models.Rel
import RelationAlgebra.Typed

/-!
# Typed Kleene algebra with tests

`RelationAlgebra.KAT.Defs` develops Kozen's Kleene algebra with tests in its *untyped*
(single-sorted) form: one Kleene algebra `K`, one Boolean algebra `T` of tests.  Damien Pous'
Rocq library `relation-algebra` is instead *typed* throughout: its `theories/kat.v` defines a
KAT as a Kleene **category** (`monoid.ops`) together with a family of Boolean algebras
`tst : ob kar → lattice.ops`, one for each object, and an injection
`inj : tst n → kar n n` of the tests at `n` into the *endomorphisms* of `n`.  This file is the
Lean counterpart of that class, on top of the `KleeneCategory` of `RelationAlgebra.Typed`.

## What the typing buys

The point of the typed presentation is that programs may change the state *space*.  A morphism
`p : X ⟶ Y` is a computation taking an `X`-state to a `Y`-state; the tests `T X` and `T Y` that
can be asserted before and after it live in *different* Boolean algebras.  Consequently the
typed Hoare triple

  `TypedKAT.HoareTriple (b : T X) (p : X ⟶ Y) (c : T Y) : Prop := ⌞b⌟ ≫ p ≫ ⌞cᶜ⌟ = ⊥`

genuinely relates two objects, and `TypedKAT.HoareTriple.seq` composes
`{b} p {c}` with `{c} q {d}` for `p : X ⟶ Y`, `q : Y ⟶ Z`, `b : T X`, `c : T Y`, `d : T Z`.
The untyped `KAT.HoareTriple` of `RelationAlgebra.KAT.Hoare` cannot say this: there, `p` and `q`
must be elements of one and the same Kleene algebra and `b`, `c`, `d` of one and the same
Boolean algebra.  The same remark applies to `TypedKAT.ifThenElse`, whose guard lives at the
source object while the two branches are arbitrary parallel morphisms `X ⟶ Y`.  Only
`TypedKAT.whileDo` is forced back to a single object, since a loop body must be iterable.

## Main declarations

* `KleeneCategoryWithTests C T` (abbreviated `TypedKAT C T`): the class, for a category `C`
  with `[KleeneCategory C]` and a family of Boolean algebras `T : C → Type w`.
* `TypedKAT.test`, with scoped notation `⌞b⌟` in the scope `TypedKAT`.  This is deliberately
  *different* from the untyped `⌜b⌝` of `RelationAlgebra.KAT.Defs` (scope `KAT`), so that both
  scopes may be open at once.
* the typed basic laws `TypedKAT.test_mono`, `TypedKAT.test_le_id`, `TypedKAT.test_comp_self`,
  `TypedKAT.test_comp_comm`, `TypedKAT.test_comp_compl`, `TypedKAT.test_sup_compl`,
  `TypedKAT.test_kstar`;
* the typed guarded commands `TypedKAT.ifThenElse`, `TypedKAT.whileDo` and the unfolding law
  `TypedKAT.whileDo_unfold`;
* the typed Hoare triple `TypedKAT.HoareTriple` and its rules, in `TypedKAT.HoareTriple`.

## The typed/untyped correspondence

Two instances justify the untyped-first organisation of this port:

* `CategoryTheory.SingleObj.instKleeneCategoryWithTests`: every untyped KAT `KAT T K` is a
  typed KAT on the one-object category `CategoryTheory.SingleObj K`, with the constant family
  of tests `fun _ ↦ T`;
* `CategoryTheory.End.instKleeneAlgebraWithTests`: conversely, at every object `X` of a typed
  KAT the endomorphisms form an untyped KAT `KAT (T X) (CategoryTheory.End X)`, on top of the
  `KleeneAlgebra (End X)` instance of `RelationAlgebra.Typed`.

So the two notions carry exactly the same information about a *single* object, and the typed
theory is the untyped theory plus the rectangular morphisms.

## A typed model

`CategoryTheory.RelCat.instKleeneCategoryWithTests`: heterogeneous relations, with `T X` the
subsets of `X` and `⌞s⌟` the sub-identity relation on `s`.  Here `p : X ⟶ Y` really is a
relation between two different types, and `TypedKAT.HoareTriple s p t` unfolds to the expected
partial-correctness statement (`CategoryTheory.RelCat.hoareTriple_iff`).

`Matrix.Mat.instKleeneCategoryWithTests`: rectangular matrices over an untyped KAT, with the
tests at dimension `n` the diagonal matrices of tests.

## References

* [D. Kozen, *Kleene algebra with tests*, TOPLAS 19(3):427-443, 1997][kozen1997]: the KAT
  framework.
* [D. Kozen, *On Hoare logic and Kleene algebra with tests*, 2000][kozen2000]: the encoding of
  partial correctness.
* Damien Pous, the Rocq library `relation-algebra`, file `theories/kat.v`, of which this file
  is the Lean counterpart; the `KleeneCategory` base comes from `theories/monoid.v`.
-/

open scoped Computability
open CategoryTheory

universe u v w

namespace KleeneCategory

variable {C : Type u} [Category.{v} C] [KleeneCategory C] {X : C}

/-- Unrolling the star from the left: `𝟙 X ⊔ f ≫ f∗ = f∗`. -/
theorem id_sup_comp_kstar (f : X ⟶ X) : 𝟙 X ⊔ f ≫ f∗ = f∗ :=
  one_add_kstar_mul (a := End.of f)

/-- Unrolling the star from the right: `𝟙 X ⊔ f∗ ≫ f = f∗`. -/
theorem id_sup_kstar_comp (f : X ⟶ X) : 𝟙 X ⊔ f∗ ≫ f = f∗ :=
  one_add_mul_kstar (a := End.of f)

/-- The star of the zero morphism is the identity. -/
@[simp] theorem kstar_bot : (⊥ : X ⟶ X)∗ = 𝟙 X := kstar_zero (α := End X)

end KleeneCategory

/-- A **typed Kleene algebra with tests**: a `KleeneCategory` together with, at each object `X`,
a Boolean algebra `T X` of tests embedded in the endomorphisms `X ⟶ X` of that object, sending
`⊥, ⊤, ⊔, ⊓` to `⊥, 𝟙 X, ⊔, ≫`.  This is Pous' `kat.ops`/`kat.laws` (`theories/kat.v`). -/
class KleeneCategoryWithTests (C : Type u) [Category.{v} C] [KleeneCategory C]
    (T : C → Type w) [∀ X : C, BooleanAlgebra (T X)] where
  /-- The embedding of the tests at `X` into the endomorphisms of `X`. -/
  test {X : C} : T X → (X ⟶ X)
  /-- The false test is the zero morphism. -/
  test_bot {X : C} : test (⊥ : T X) = ⊥
  /-- The true test is the identity. -/
  test_top {X : C} : test (⊤ : T X) = 𝟙 X
  /-- Disjunction of tests is join of morphisms. -/
  test_sup {X : C} (a b : T X) : test (a ⊔ b) = test a ⊔ test b
  /-- Conjunction of tests is composition of morphisms. -/
  test_inf {X : C} (a b : T X) : test (a ⊓ b) = test a ≫ test b

/-- `TypedKAT C T` abbreviates `KleeneCategoryWithTests C T`. -/
abbrev TypedKAT := KleeneCategoryWithTests

namespace TypedKAT

export KleeneCategoryWithTests (test test_bot test_top test_sup test_inf)

attribute [simp] KleeneCategoryWithTests.test_bot KleeneCategoryWithTests.test_top
  KleeneCategoryWithTests.test_sup KleeneCategoryWithTests.test_inf

/-- `⌞b⌟` is the test `b` regarded as an endomorphism of its object.  Distinct on purpose from
the untyped `⌜b⌝` of `RelationAlgebra.KAT.Defs`, so that the scopes `KAT` and `TypedKAT` can be
open simultaneously. -/
scoped notation:max "⌞" b "⌟" => KleeneCategoryWithTests.test b

section Basic

variable {C : Type u} [Category.{v} C] [KleeneCategory C] {T : C → Type w}
  [∀ X : C, BooleanAlgebra (T X)] [TypedKAT C T] {X Y Z : C}

/-! ### Basic laws about tests -/

theorem test_mono : Monotone (test : T X → (X ⟶ X)) := by
  intro a b h
  have hab : (⌞a ⊔ b⌟ : X ⟶ X) = ⌞b⌟ := by rw [sup_eq_right.2 h]
  rw [test_sup] at hab
  exact sup_eq_right.1 hab

theorem test_le_test {a b : T X} (h : a ≤ b) : (⌞a⌟ : X ⟶ X) ≤ ⌞b⌟ := test_mono h

@[simp] theorem test_le_id (a : T X) : (⌞a⌟ : X ⟶ X) ≤ 𝟙 X := by
  have h : (⌞a⌟ : X ⟶ X) ≤ ⌞(⊤ : T X)⌟ := test_mono le_top
  rwa [test_top] at h

@[simp] theorem test_comp_self (a : T X) : (⌞a⌟ : X ⟶ X) ≫ ⌞a⌟ = ⌞a⌟ := by
  rw [← test_inf, inf_idem]

/-- Tests at the same object commute. -/
theorem test_comp_comm (a b : T X) : (⌞a⌟ : X ⟶ X) ≫ ⌞b⌟ = ⌞b⌟ ≫ ⌞a⌟ := by
  rw [← test_inf, ← test_inf, inf_comm]

theorem test_comp_left_comm (a b : T X) (p : X ⟶ Y) : ⌞a⌟ ≫ ⌞b⌟ ≫ p = ⌞b⌟ ≫ ⌞a⌟ ≫ p := by
  rw [← Category.assoc, test_comp_comm, Category.assoc]

theorem comp_test_right_comm (p : Y ⟶ X) (a b : T X) : (p ≫ ⌞a⌟) ≫ ⌞b⌟ = (p ≫ ⌞b⌟) ≫ ⌞a⌟ := by
  rw [Category.assoc, test_comp_comm, Category.assoc]

@[simp] theorem test_comp_compl (a : T X) : (⌞a⌟ : X ⟶ X) ≫ ⌞aᶜ⌟ = ⊥ := by
  rw [← test_inf, inf_compl_eq_bot, test_bot]

@[simp] theorem test_compl_comp (a : T X) : (⌞aᶜ⌟ : X ⟶ X) ≫ ⌞a⌟ = ⊥ := by
  rw [← test_inf, compl_inf_eq_bot, test_bot]

@[simp] theorem test_sup_compl (a : T X) : (⌞a⌟ : X ⟶ X) ⊔ ⌞aᶜ⌟ = 𝟙 X := by
  rw [← test_sup, sup_compl_eq_top, test_top]

@[simp] theorem test_compl_sup (a : T X) : (⌞aᶜ⌟ : X ⟶ X) ⊔ ⌞a⌟ = 𝟙 X := by
  rw [← test_sup, compl_sup_eq_top, test_top]

@[simp] theorem test_kstar (a : T X) : (⌞a⌟ : X ⟶ X)∗ = 𝟙 X :=
  KleeneCategory.kstar_eq_id_iff.2 (test_le_id a)

theorem test_comp_le (a : T X) (p : X ⟶ Y) : ⌞a⌟ ≫ p ≤ p :=
  (KleeneCategory.comp_le_comp_left (test_le_id a) p).trans_eq (Category.id_comp p)

theorem comp_test_le (p : Y ⟶ X) (a : T X) : p ≫ ⌞a⌟ ≤ p :=
  (KleeneCategory.comp_le_comp_right (test_le_id a) p).trans_eq (Category.comp_id p)

theorem test_comp_le_test_comp {a b : T X} (h : a ≤ b) (p : X ⟶ Y) : ⌞a⌟ ≫ p ≤ ⌞b⌟ ≫ p :=
  KleeneCategory.comp_le_comp_left (test_le_test h) p

theorem comp_test_le_comp_test (p : Y ⟶ X) {a b : T X} (h : a ≤ b) : p ≫ ⌞a⌟ ≤ p ≫ ⌞b⌟ :=
  KleeneCategory.comp_le_comp_right (test_le_test h) p

@[simp] theorem test_comp_sup_test_compl_comp (a : T X) (p : X ⟶ Y) :
    ⌞a⌟ ≫ p ⊔ ⌞aᶜ⌟ ≫ p = p := by
  rw [← KleeneCategory.sup_comp, test_sup_compl, Category.id_comp]

@[simp] theorem comp_test_sup_comp_test_compl (p : Y ⟶ X) (a : T X) :
    p ≫ ⌞a⌟ ⊔ p ≫ ⌞aᶜ⌟ = p := by
  rw [← KleeneCategory.comp_sup, test_sup_compl, Category.comp_id]

/-! ### Guarded commands

The conditional is typed: its guard is a test at the source object, and its two branches are
arbitrary parallel morphisms `X ⟶ Y`.  The loop necessarily stays at one object. -/

/-- `if b then p else q`, encoded as `⌞b⌟ ≫ p ⊔ ⌞bᶜ⌟ ≫ q`.  The guard `b` is a test at the
source object `X`; the branches may go to any object `Y`. -/
def ifThenElse (b : T X) (p q : X ⟶ Y) : X ⟶ Y := ⌞b⌟ ≫ p ⊔ ⌞bᶜ⌟ ≫ q

/-- `while b do p`, encoded as `(⌞b⌟ ≫ p)∗ ≫ ⌞bᶜ⌟`.  A loop body must be iterable, so this is
the one place where the typed theory is forced back to a single object. -/
def whileDo (b : T X) (p : X ⟶ X) : X ⟶ X := (⌞b⌟ ≫ p)∗ ≫ ⌞bᶜ⌟

theorem ifThenElse_def (b : T X) (p q : X ⟶ Y) : ifThenElse b p q = ⌞b⌟ ≫ p ⊔ ⌞bᶜ⌟ ≫ q := rfl

theorem whileDo_def (b : T X) (p : X ⟶ X) : whileDo b p = (⌞b⌟ ≫ p)∗ ≫ ⌞bᶜ⌟ := rfl

@[simp] theorem ifThenElse_self (b : T X) (p : X ⟶ Y) : ifThenElse b p p = p :=
  test_comp_sup_test_compl_comp b p

theorem ifThenElse_compl (b : T X) (p q : X ⟶ Y) : ifThenElse bᶜ p q = ifThenElse b q p := by
  rw [ifThenElse_def, ifThenElse_def, compl_compl, sup_comm]

@[simp] theorem ifThenElse_top (p q : X ⟶ Y) : ifThenElse (⊤ : T X) p q = p := by
  simp [ifThenElse_def]

@[simp] theorem ifThenElse_bot (p q : X ⟶ Y) : ifThenElse (⊥ : T X) p q = q := by
  simp [ifThenElse_def]

@[simp] theorem test_comp_ifThenElse (b : T X) (p q : X ⟶ Y) :
    ⌞b⌟ ≫ ifThenElse b p q = ⌞b⌟ ≫ p := by
  rw [ifThenElse_def, KleeneCategory.comp_sup, ← Category.assoc, ← Category.assoc,
    test_comp_self, test_comp_compl, KleeneCategory.bot_comp, sup_bot_eq]

@[simp] theorem test_compl_comp_ifThenElse (b : T X) (p q : X ⟶ Y) :
    ⌞bᶜ⌟ ≫ ifThenElse b p q = ⌞bᶜ⌟ ≫ q := by
  rw [ifThenElse_def, KleeneCategory.comp_sup, ← Category.assoc, ← Category.assoc,
    test_compl_comp, test_comp_self, KleeneCategory.bot_comp, bot_sup_eq]

theorem ifThenElse_comp (b : T X) (p q : X ⟶ Y) (r : Y ⟶ Z) :
    ifThenElse b p q ≫ r = ifThenElse b (p ≫ r) (q ≫ r) := by
  simp only [ifThenElse_def, KleeneCategory.sup_comp, Category.assoc]

/-- Unfolding a `while` loop once. -/
theorem whileDo_unfold (b : T X) (p : X ⟶ X) :
    whileDo b p = ifThenElse b (p ≫ whileDo b p) (𝟙 X) := by
  rw [ifThenElse_def, Category.comp_id, whileDo_def]
  conv_lhs => rw [← KleeneCategory.id_sup_comp_kstar (⌞b⌟ ≫ p)]
  rw [KleeneCategory.sup_comp, Category.id_comp, sup_comm]
  simp only [Category.assoc]

@[simp] theorem whileDo_comp_test_compl (b : T X) (p : X ⟶ X) :
    whileDo b p ≫ ⌞bᶜ⌟ = whileDo b p := by
  rw [whileDo_def, Category.assoc, test_comp_self]

@[simp] theorem test_compl_comp_whileDo (b : T X) (p : X ⟶ X) :
    ⌞bᶜ⌟ ≫ whileDo b p = ⌞bᶜ⌟ := by
  rw [whileDo_unfold, test_compl_comp_ifThenElse, Category.comp_id]

@[simp] theorem whileDo_bot (p : X ⟶ X) : whileDo (⊥ : T X) p = 𝟙 X := by
  rw [whileDo_def, test_bot, KleeneCategory.bot_comp, KleeneCategory.kstar_bot,
    Category.id_comp, compl_bot, test_top]

/-! ### Hoare triples -/

/-- The typed partial-correctness Hoare triple `{b} p {c}`, encoded as `⌞b⌟ ≫ p ≫ ⌞cᶜ⌟ = ⊥`.

Unlike the untyped `KAT.HoareTriple`, this relates **two objects**: the precondition `b` is a
test at the source `X`, the postcondition `c` a test at the target `Y`, and `p : X ⟶ Y` may
change the state space. -/
def HoareTriple (b : T X) (p : X ⟶ Y) (c : T Y) : Prop := ⌞b⌟ ≫ p ≫ ⌞cᶜ⌟ = ⊥

theorem hoareTriple_def {b : T X} {p : X ⟶ Y} {c : T Y} :
    HoareTriple b p c ↔ ⌞b⌟ ≫ p ≫ ⌞cᶜ⌟ = ⊥ := Iff.rfl

/-- `{b} p {c}` iff `⌞b⌟ ≫ p ≤ p ≫ ⌞c⌟`. -/
theorem hoareTriple_iff_le {b : T X} {p : X ⟶ Y} {c : T Y} :
    HoareTriple b p c ↔ ⌞b⌟ ≫ p ≤ p ≫ ⌞c⌟ := by
  rw [hoareTriple_def]
  constructor
  · intro h
    calc ⌞b⌟ ≫ p = ⌞b⌟ ≫ p ≫ (⌞c⌟ ⊔ ⌞cᶜ⌟) := by rw [test_sup_compl, Category.comp_id]
      _ = ⌞b⌟ ≫ p ≫ ⌞c⌟ ⊔ ⌞b⌟ ≫ p ≫ ⌞cᶜ⌟ := by
          rw [KleeneCategory.comp_sup, KleeneCategory.comp_sup]
      _ = ⌞b⌟ ≫ p ≫ ⌞c⌟ := by rw [h, sup_bot_eq]
      _ ≤ p ≫ ⌞c⌟ := test_comp_le b (p ≫ ⌞c⌟)
  · intro h
    refine le_antisymm ?_ bot_le
    calc ⌞b⌟ ≫ p ≫ ⌞cᶜ⌟ = (⌞b⌟ ≫ p) ≫ ⌞cᶜ⌟ := (Category.assoc _ _ _).symm
      _ ≤ (p ≫ ⌞c⌟) ≫ ⌞cᶜ⌟ := KleeneCategory.comp_le_comp_left h _
      _ = p ≫ ⌞c⌟ ≫ ⌞cᶜ⌟ := Category.assoc _ _ _
      _ = ⊥ := by rw [test_comp_compl, KleeneCategory.comp_bot]

/-- `{b} p {c}` iff `⌞b⌟ ≫ p = ⌞b⌟ ≫ p ≫ ⌞c⌟`. -/
theorem hoareTriple_iff_eq {b : T X} {p : X ⟶ Y} {c : T Y} :
    HoareTriple b p c ↔ ⌞b⌟ ≫ p = ⌞b⌟ ≫ p ≫ ⌞c⌟ := by
  rw [hoareTriple_def]
  constructor
  · intro h
    calc ⌞b⌟ ≫ p = ⌞b⌟ ≫ p ≫ (⌞c⌟ ⊔ ⌞cᶜ⌟) := by rw [test_sup_compl, Category.comp_id]
      _ = ⌞b⌟ ≫ p ≫ ⌞c⌟ ⊔ ⌞b⌟ ≫ p ≫ ⌞cᶜ⌟ := by
          rw [KleeneCategory.comp_sup, KleeneCategory.comp_sup]
      _ = ⌞b⌟ ≫ p ≫ ⌞c⌟ := by rw [h, sup_bot_eq]
  · intro h
    rw [← hoareTriple_def, hoareTriple_iff_le, h]
    exact test_comp_le b (p ≫ ⌞c⌟)

namespace HoareTriple

/-! #### The rules of Hoare logic, typed -/

/-- `{b} 𝟙 X {b}`. -/
theorem skip (b : T X) : HoareTriple b (𝟙 X) b := by
  rw [hoareTriple_def, Category.id_comp, test_comp_compl]

/-- The empty program satisfies every specification. -/
theorem bot_prog (b : T X) (c : T Y) : HoareTriple b (⊥ : X ⟶ Y) c := by
  rw [hoareTriple_def, KleeneCategory.bot_comp, KleeneCategory.comp_bot]

/-- A false precondition proves anything. -/
theorem bot_pre (p : X ⟶ Y) (c : T Y) : HoareTriple (⊥ : T X) p c := by
  rw [hoareTriple_def, test_bot, KleeneCategory.bot_comp]

/-- A trivial postcondition is always established. -/
theorem top_post (b : T X) (p : X ⟶ Y) : HoareTriple b p (⊤ : T Y) := by
  rw [hoareTriple_def, compl_top, test_bot, KleeneCategory.comp_bot, KleeneCategory.comp_bot]

/-- `{b} ⌞c⌟ {b ⊓ c}`: running a test as a program asserts it. -/
theorem test (b c : T X) : HoareTriple b (⌞c⌟ : X ⟶ X) (b ⊓ c) := by
  rw [hoareTriple_def, ← Category.assoc, ← test_inf, test_comp_compl]

/-- Sequential composition, across three objects. -/
theorem seq {b : T X} {p : X ⟶ Y} {c : T Y} {q : Y ⟶ Z} {d : T Z}
    (hp : HoareTriple b p c) (hq : HoareTriple c q d) : HoareTriple b (p ≫ q) d := by
  rw [hoareTriple_iff_le] at hp hq ⊢
  calc ⌞b⌟ ≫ p ≫ q = (⌞b⌟ ≫ p) ≫ q := (Category.assoc _ _ _).symm
    _ ≤ (p ≫ ⌞c⌟) ≫ q := KleeneCategory.comp_le_comp_left hp q
    _ = p ≫ ⌞c⌟ ≫ q := Category.assoc _ _ _
    _ ≤ p ≫ q ≫ ⌞d⌟ := KleeneCategory.comp_le_comp_right hq p
    _ = (p ≫ q) ≫ ⌞d⌟ := (Category.assoc _ _ _).symm

/-- Nondeterministic choice. -/
theorem sup {b : T X} {p q : X ⟶ Y} {c : T Y}
    (hp : HoareTriple b p c) (hq : HoareTriple b q c) : HoareTriple b (p ⊔ q) c := by
  rw [hoareTriple_def] at hp hq ⊢
  rw [KleeneCategory.sup_comp, KleeneCategory.comp_sup, hp, hq, sup_bot_eq]

/-- The conditional, with the guard at the source object. -/
theorem ifThenElse {b c : T X} {p q : X ⟶ Y} {d : T Y}
    (hp : HoareTriple (b ⊓ c) p d) (hq : HoareTriple (bᶜ ⊓ c) q d) :
    HoareTriple c (TypedKAT.ifThenElse b p q) d := by
  rw [hoareTriple_def, test_inf] at hp hq
  simp only [← Category.assoc] at hp hq
  rw [hoareTriple_def, ifThenElse_def, KleeneCategory.sup_comp, KleeneCategory.comp_sup]
  simp only [← Category.assoc]
  rw [test_comp_comm c b, test_comp_comm c bᶜ, hp, hq, sup_bot_eq]

/-- Iteration: an invariant of `p` is an invariant of `p∗`. -/
theorem kstar {b : T X} {p : X ⟶ X} (h : HoareTriple b p b) : HoareTriple b p∗ b := by
  rw [hoareTriple_iff_le] at h ⊢
  exact KleeneCategory.comp_kstar_le_kstar_comp_of_le h

/-- The `while` rule. -/
theorem whileDo {b c : T X} {p : X ⟶ X} (h : HoareTriple (b ⊓ c) p c) :
    HoareTriple c (TypedKAT.whileDo b p) (bᶜ ⊓ c) := by
  rw [hoareTriple_iff_le, test_inf] at h ⊢
  have key : ⌞c⌟ ≫ ⌞b⌟ ≫ p ≤ (⌞b⌟ ≫ p) ≫ ⌞c⌟ := by
    have e : (⌞c⌟ : X ⟶ X) ≫ ⌞b⌟ ≫ p = ⌞b⌟ ≫ (⌞b⌟ ≫ ⌞c⌟) ≫ p := by
      rw [Category.assoc, ← Category.assoc ⌞b⌟ ⌞b⌟ (⌞c⌟ ≫ p), test_comp_self,
        ← Category.assoc, ← Category.assoc, test_comp_comm]
    rw [e]
    exact (KleeneCategory.comp_le_comp_right h ⌞b⌟).trans_eq (Category.assoc _ _ _).symm
  calc ⌞c⌟ ≫ TypedKAT.whileDo b p = (⌞c⌟ ≫ (⌞b⌟ ≫ p)∗) ≫ ⌞bᶜ⌟ := by
        rw [whileDo_def, Category.assoc]
    _ ≤ ((⌞b⌟ ≫ p)∗ ≫ ⌞c⌟) ≫ ⌞bᶜ⌟ :=
        KleeneCategory.comp_le_comp_left
          (KleeneCategory.comp_kstar_le_kstar_comp_of_le key) ⌞bᶜ⌟
    _ = (⌞b⌟ ≫ p)∗ ≫ ⌞bᶜ⌟ ≫ ⌞c⌟ := by
        rw [Category.assoc, test_comp_comm]
    _ = TypedKAT.whileDo b p ≫ ⌞bᶜ⌟ ≫ ⌞c⌟ := by
        rw [whileDo_def, Category.assoc, ← Category.assoc ⌞bᶜ⌟ ⌞bᶜ⌟ ⌞c⌟, test_comp_self]

/-- The rule of consequence.  Note that the pre- and postconditions are strengthened and
weakened in *different* Boolean algebras. -/
theorem consequence {b b' : T X} {p : X ⟶ Y} {c c' : T Y}
    (hb : b' ≤ b) (h : HoareTriple b p c) (hc : c ≤ c') : HoareTriple b' p c' := by
  rw [hoareTriple_iff_le] at h ⊢
  calc ⌞b'⌟ ≫ p ≤ ⌞b⌟ ≫ p := test_comp_le_test_comp hb p
    _ ≤ p ≫ ⌞c⌟ := h
    _ ≤ p ≫ ⌞c'⌟ := comp_test_le_comp_test p hc

theorem strengthen_pre {b b' : T X} {p : X ⟶ Y} {c : T Y}
    (hb : b' ≤ b) (h : HoareTriple b p c) : HoareTriple b' p c :=
  consequence hb h le_rfl

theorem weaken_post {b : T X} {p : X ⟶ Y} {c c' : T Y}
    (h : HoareTriple b p c) (hc : c ≤ c') : HoareTriple b p c' :=
  consequence le_rfl h hc

/-- `{⊤} while b do p {bᶜ}`: the loop guard fails on exit. -/
theorem whileDo_exit (b : T X) (p : X ⟶ X) : HoareTriple ⊤ (TypedKAT.whileDo b p) bᶜ :=
  (whileDo (top_post _ _)).weaken_post inf_le_left

end HoareTriple

end Basic

end TypedKAT

/-! ### Every untyped Kleene algebra with tests is a one-object typed KAT -/

namespace CategoryTheory.SingleObj

open scoped KAT

/-- An untyped Kleene algebra with tests `KAT T K` is a typed KAT on the one-object category
`SingleObj K`, with the constant family of tests.  Recall that in `SingleObj K` the morphisms
are the elements of `K`, `𝟙 = 1` and `f ≫ g = g * f`. -/
instance instKleeneCategoryWithTests (T K : Type*) [BooleanAlgebra T] [KleeneAlgebra K]
    [KAT T K] : KleeneCategoryWithTests (SingleObj K) (fun _ ↦ T) where
  test a := (⌜a⌝ : K)
  test_bot := KAT.test_bot.trans bot_eq_zero.symm
  test_top := KAT.test_top
  test_sup a b := (KAT.test_sup a b).trans (add_eq_sup _ _)
  test_inf a b := by
    rw [inf_comm]
    exact KAT.test_inf b a

theorem test_as_test {T K : Type*} [BooleanAlgebra T] [KleeneAlgebra K] [KAT T K]
    {x : SingleObj K} (a : T) : (TypedKAT.test (T := fun _ ↦ T) a : x ⟶ x) = (⌜a⌝ : K) :=
  rfl

end CategoryTheory.SingleObj

/-! ### The endomorphisms at an object of a typed KAT form an untyped KAT -/

namespace CategoryTheory.End

/-- At every object `X` of a typed Kleene algebra with tests, the endomorphism Kleene algebra
`End X` together with the Boolean algebra `T X` is an untyped Kleene algebra with tests.
Beware the reversal `f * g = g ≫ f` built into `CategoryTheory.End`; it is harmless here
because tests at the same object commute (`TypedKAT.test_comp_comm`). -/
instance instKleeneAlgebraWithTests {C : Type u} [Category.{v} C] [KleeneCategory C]
    {T : C → Type w} [∀ X : C, BooleanAlgebra (T X)] [TypedKAT C T] (X : C) :
    KleeneAlgebraWithTests (T X) (End X) where
  test a := TypedKAT.test a
  test_bot := TypedKAT.test_bot
  test_top := TypedKAT.test_top
  test_sup a b := TypedKAT.test_sup a b
  test_inf a b := by
    rw [inf_comm]
    exact TypedKAT.test_inf b a

end CategoryTheory.End

/-! ### A typed model: heterogeneous relations -/

namespace CategoryTheory.RelCat

open scoped TypedKAT

variable {X Y : RelCat.{u}}

/-- The sub-identity relation on a subset, as an endomorphism of `RelCat`. -/
def test (s : Set X) : X ⟶ X := Hom.ofRel (SetRel.ofSet s)

@[simp] theorem rel_test (s : Set X) : (test s).rel = SetRel.ofSet s := rfl

/-- `RelCat` is a typed Kleene algebra with tests: the tests at an object `X` are the subsets
of `X`, embedded as the sub-identity relations.  Here a morphism `X ⟶ Y` is a relation between
two genuinely different types. -/
instance instKleeneCategoryWithTests : KleeneCategoryWithTests RelCat.{u} Set where
  test := test
  test_bot := by
    refine Hom.ext _ _ ?_
    ext ⟨a, b⟩
    simp
  test_top := by
    refine Hom.ext _ _ ?_
    ext ⟨a, b⟩
    simp
  test_sup := by
    intro Z s t
    refine Hom.ext _ _ ?_
    ext ⟨a, b⟩
    simp only [rel_test, SetRel.mem_ofSet, Set.sup_eq_union, Set.mem_union, Hom.rel_sup]
    tauto
  test_inf := by
    intro Z s t
    refine Hom.ext _ _ ?_
    ext ⟨a, b⟩
    simp only [rel_test, SetRel.mem_ofSet, Set.inf_eq_inter, Set.mem_inter_iff, Hom.rel_comp,
      SetRel.mem_comp]
    constructor
    · rintro ⟨rfl, hs, ht⟩
      exact ⟨a, ⟨rfl, hs⟩, rfl, ht⟩
    · rintro ⟨c, ⟨rfl, hs⟩, rfl, ht⟩
      exact ⟨rfl, hs, ht⟩

theorem test_eq (s : Set X) : (⌞s⌟ : X ⟶ X) = test s := rfl

/-- The typed Hoare triple in `RelCat` says exactly what it should: every `f`-successor of a
state satisfying the precondition satisfies the postcondition — and the two states live in
different types. -/
theorem hoareTriple_iff (s : Set X) (f : X ⟶ Y) (t : Set Y) :
    TypedKAT.HoareTriple s f t ↔ ∀ a ∈ s, ∀ b, (a, b) ∈ f.rel → b ∈ t := by
  have key : ∀ a b, ((a, b) : X × Y) ∈ (⌞s⌟ ≫ f ≫ ⌞tᶜ⌟).rel ↔
      a ∈ s ∧ (a, b) ∈ f.rel ∧ b ∉ t := by
    intro a b
    simp only [Hom.rel_comp, SetRel.mem_comp, test_eq, rel_test, SetRel.mem_ofSet,
      Set.mem_compl_iff]
    constructor
    · rintro ⟨c, ⟨rfl, hc⟩, d, hcd, rfl, hd⟩
      exact ⟨hc, hcd, hd⟩
    · rintro ⟨hc, hcd, hd⟩
      exact ⟨a, ⟨rfl, hc⟩, b, hcd, rfl, hd⟩
  rw [TypedKAT.hoareTriple_def]
  constructor
  · intro h a ha b hab
    by_contra hb
    have hmem := (key a b).2 ⟨ha, hab, hb⟩
    rw [h] at hmem
    simp at hmem
  · intro h
    refine Hom.ext _ _ ?_
    ext ⟨a, b⟩
    simp only [Hom.rel_bot, Set.mem_empty_iff_false, iff_false]
    intro hmem
    obtain ⟨ha, hab, hb⟩ := (key a b).1 hmem
    exact hb (h a ha b hab)

/-! #### Typed Hoare triples between two different objects -/

example : TypedKAT.HoareTriple (C := RelCat.{0}) (T := Set)
    ({0} : Set (ℕ : RelCat.{0})) (Hom.ofRel {p : ℕ × Bool | p.2 = (p.1 == 0)})
    ({true} : Set (Bool : RelCat.{0})) := by
  rw [hoareTriple_iff]
  intro a ha b hb
  rw [Set.mem_singleton_iff] at ha
  subst ha
  simpa using hb

example {W : RelCat.{u}} (s : Set X) (f : X ⟶ Y) (t : Set Y) (g : Y ⟶ W) (u : Set W)
    (hf : TypedKAT.HoareTriple s f t) (hg : TypedKAT.HoareTriple t g u) :
    TypedKAT.HoareTriple s (f ≫ g) u :=
  hf.seq hg

end CategoryTheory.RelCat

/-! ### A second typed model: rectangular matrices -/

namespace Matrix.Mat

open scoped KAT

variable {K : Type*} [KleeneAlgebra K] {T : Type*} [BooleanAlgebra T] [KAT T K]

/-- The category `Matrix.Mat K` of rectangular matrices over an untyped Kleene algebra with
tests is a typed Kleene algebra with tests: the tests at the object of dimension `n` are the
families `Fin n → T`, embedded as the diagonal matrices of tests (Pous' `matrix.v`). -/
noncomputable instance instKleeneCategoryWithTests :
    KleeneCategoryWithTests (Mat K) (fun X ↦ Fin X.dim → T) where
  test f := Matrix.diagTest f
  test_bot := by
    intro X
    have h := KAT.test_bot (T := Fin X.dim → T) (K := Matrix (Fin X.dim) (Fin X.dim) K)
    change (Matrix.diagTest (⊥ : Fin X.dim → T) : Matrix (Fin X.dim) (Fin X.dim) K) = ⊥
    rw [Matrix.bot_eq_zero]
    exact h
  test_top := by
    intro X
    have h := KAT.test_top (T := Fin X.dim → T) (K := Matrix (Fin X.dim) (Fin X.dim) K)
    change (Matrix.diagTest (⊤ : Fin X.dim → T) : Matrix (Fin X.dim) (Fin X.dim) K) = 1
    exact h
  test_sup := by
    intro X a b
    have h := KAT.test_sup (T := Fin X.dim → T) (K := Matrix (Fin X.dim) (Fin X.dim) K) a b
    change (Matrix.diagTest (a ⊔ b) : Matrix (Fin X.dim) (Fin X.dim) K)
      = Matrix.diagTest a ⊔ Matrix.diagTest b
    rw [← Matrix.add_eq_sup]
    exact h
  test_inf := by
    intro X a b
    have h := KAT.test_inf (T := Fin X.dim → T) (K := Matrix (Fin X.dim) (Fin X.dim) K) a b
    change (Matrix.diagTest (a ⊓ b) : Matrix (Fin X.dim) (Fin X.dim) K)
      = Matrix.diagTest a * Matrix.diagTest b
    exact h

theorem test_eq_diagTest {X : Mat K} (f : Fin X.dim → T) :
    (TypedKAT.test (T := fun Z : Mat K ↦ Fin Z.dim → T) f : X ⟶ X) = Matrix.diagTest f :=
  rfl

end Matrix.Mat
