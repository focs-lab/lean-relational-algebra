import RelationAlgebra.TypedConverse
import RelationAlgebra.Decide.Normalise

/-!
# Typed expressions with converse

`TypedRA.Term src tgt X Y` represents the Kleene algebra with converse fragment of
Damien Pous' `theories/expr.v`: zero, identity, actions, union, composition, iteration,
and converse. Converse reverses endpoints; iteration is restricted to endomorphisms.
There are no Boolean tests, meets, complements, top, or residuals in this syntax.
Erasure produces the existing `RaTerm` used by structural normalization.
-/

open CategoryTheory KleeneCategoryWithConverse
open scoped Computability

universe u v w

namespace TypedRA

/-- Expressions indexed by source and target, with globally named actions. -/
inductive Term {I : Type u} (src tgt : ℕ → I) : I → I → Type u
  | zero {X Y : I} : Term src tgt X Y
  | one {X : I} : Term src tgt X X
  | act (a : ℕ) : Term src tgt (src a) (tgt a)
  | add {X Y : I} : Term src tgt X Y → Term src tgt X Y → Term src tgt X Y
  | comp {X Y Z : I} : Term src tgt X Y → Term src tgt Y Z → Term src tgt X Z
  | star {X : I} : Term src tgt X X → Term src tgt X X
  | conv {X Y : I} : Term src tgt X Y → Term src tgt Y X

namespace Term

variable {I : Type u} {src tgt : ℕ → I} {X Y : I}

/-- Forget endpoints, retaining the operations and global action names. -/
def erase : {A B : I} → Term src tgt A B → RaTerm
  | _, _, .zero => .zero
  | _, _, .one => .one
  | _, _, .act a => .var a
  | _, _, .add e f => .add e.erase f.erase
  | _, _, .comp e f => .mul e.erase f.erase
  | _, _, .star e => .star e.erase
  | _, _, .conv e => .conv e.erase

/-- Interpret an expression in an arbitrary Kleene category with converse. -/
def eval {C : Type v} [Category.{w} C] [KleeneCategory C] [KleeneCategoryWithConverse C]
    (obj : I → C) (ρ : ∀ a, obj (src a) ⟶ obj (tgt a)) :
    {A B : I} → Term src tgt A B → (obj A ⟶ obj B)
  | _, _, .zero => ⊥
  | _, _, .one => 𝟙 _
  | _, _, .act a => ρ a
  | _, _, .add e f => eval obj ρ e ⊔ eval obj ρ f
  | _, _, .comp e f => eval obj ρ e ≫ eval obj ρ f
  | _, _, .star e => (eval obj ρ e)∗
  | _, _, .conv e => converse (eval obj ρ e)

/-- Rename or identify objects while retaining the well-typed expression. -/
def mapObjects {J : Type v} (f : I → J) :
    {A B : I} → Term src tgt A B → Term (f ∘ src) (f ∘ tgt) (f A) (f B)
  | _, _, .zero => .zero
  | _, _, .one => .one
  | _, _, .act a => .act a
  | _, _, .add e g => .add (e.mapObjects f) (g.mapObjects f)
  | _, _, .comp e g => .comp (e.mapObjects f) (g.mapObjects f)
  | _, _, .star e => .star (e.mapObjects f)
  | _, _, .conv e => .conv (e.mapObjects f)

@[simp] theorem erase_mapObjects {J : Type v} (f : I → J) (e : Term src tgt X Y) :
    (e.mapObjects f).erase = e.erase := by
  induction e <;> simp_all [mapObjects, erase]

/-- Evaluation commutes with object renaming, including noninjective renaming. -/
theorem eval_mapObjects {J : Type v} {C : Type*} [Category.{w} C] [KleeneCategory C]
    [KleeneCategoryWithConverse C] (f : I → J) (obj : J → C)
    (ρ : ∀ a, obj (f (src a)) ⟶ obj (f (tgt a))) (e : Term src tgt X Y) :
    eval obj ρ (e.mapObjects f) = eval (obj ∘ f) ρ e := by
  induction e <;> simp_all [mapObjects, eval] <;> rfl

end Term
end TypedRA
