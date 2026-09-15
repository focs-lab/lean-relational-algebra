import RelationAlgebra.Decide.KATSound
import RelationAlgebra.TypedKAT

/-!
# Typed syntax for Kleene algebra with tests

`TypedKAT.Term src tgt X Y` is a KAT expression from `X` to `Y`. Each action has the
source and target specified by `src` and `tgt`; composition requires matching endpoints,
and only endomorphisms can be iterated. Object names can have any type.

Boolean expressions use the existing `KAT.BTerm`. A test variable is interpreted separately
at each object: the same variable number at two objects need not denote the same test.
This follows Damien Pous's `theories/gregex.v` in
[`relation-algebra`](https://github.com/damien-pous/relation-algebra), revision
`2d2af3631929399bbac56f57b3e15302d8697e1c`. We use Kleene star
and an explicit identity constructor, rather than upstream's strict iteration.

`Term.eval` interprets expressions in any `KleeneCategoryWithTests`, with an arbitrary map
from syntactic objects to semantic objects. `Term.erase` forgets the object indices and
produces the existing untyped `KAT.KTerm`. Defining erasure does not assert the algebraic
untyping theorem. Typed completeness and reflection are proved separately in
`RelationAlgebra.TypedKATCompleteness.Main`.
-/

open CategoryTheory
open scoped Computability

universe u v w z

namespace TypedKAT

/-- KAT expressions indexed by their source and target objects. Action names are global;
test variable names are local to the object at which the test is embedded. -/
inductive Term {I : Type u} (src tgt : ℕ → I) : I → I → Type u
  | zero {X Y : I} : Term src tgt X Y
  | one {X : I} : Term src tgt X X
  | test {X : I} : KAT.BTerm → Term src tgt X X
  | act (a : ℕ) : Term src tgt (src a) (tgt a)
  | add {X Y : I} : Term src tgt X Y → Term src tgt X Y → Term src tgt X Y
  | comp {X Y Z : I} : Term src tgt X Y → Term src tgt Y Z → Term src tgt X Z
  | star {X : I} : Term src tgt X X → Term src tgt X X

namespace Term

variable {I : Type u} {src tgt : ℕ → I} {X Y Z : I}

/-- Forget object indices, preserving action and test variable names. -/
def erase : {A B : I} → Term src tgt A B → KAT.KTerm
  | _, _, .zero => .zero
  | _, _, .one => .one
  | _, _, .test b => .test b
  | _, _, .act a => .act a
  | _, _, .add e f => .add e.erase f.erase
  | _, _, .comp e f => .mul e.erase f.erase
  | _, _, .star e => .star e.erase

/-- Test variable numbers occurring in an expression, including repetitions. The object
of an occurrence is deliberately omitted, as in `erase`. -/
def tvars (e : Term src tgt X Y) : List ℕ := e.erase.tvars

/-- Action names occurring in an expression, including repetitions. -/
def acts (e : Term src tgt X Y) : List ℕ := e.erase.acts

/-- Check that all test variable numbers lie below a finite bound. -/
def tvarsBelow (k : ℕ) (e : Term src tgt X Y) : Bool := e.erase.tvarsBelow k

section Evaluation

variable {C : Type v} [Category.{w} C] [KleeneCategory C]
  {T : C → Type z} [∀ A, BooleanAlgebra (T A)] [TypedKAT C T]

/-- Interpret a typed expression. Tests at distinct syntactic objects have independent
valuations, even if `obj` maps those objects to the same semantic object. -/
def eval (obj : I → C) (τ : ∀ A, ℕ → T (obj A))
    (ρ : ∀ a, obj (src a) ⟶ obj (tgt a)) :
    {A B : I} → Term src tgt A B → (obj A ⟶ obj B)
  | _, _, .zero => ⊥
  | _, _, .one => 𝟙 _
  | A, _, .test b => TypedKAT.test (b.eval (τ A))
  | _, _, .act a => ρ a
  | _, _, .add e f => eval obj τ ρ e ⊔ eval obj τ ρ f
  | _, _, .comp e f => eval obj τ ρ e ≫ eval obj τ ρ f
  | _, _, .star e => (eval obj τ ρ e)∗

variable (obj : I → C) (τ : ∀ A, ℕ → T (obj A))
  (ρ : ∀ a, obj (src a) ⟶ obj (tgt a))

@[simp] theorem eval_zero : eval obj τ ρ (.zero : Term src tgt X Y) = ⊥ := rfl

@[simp] theorem eval_one : eval obj τ ρ (.one : Term src tgt X X) = 𝟙 (obj X) := rfl

@[simp] theorem eval_test (b : KAT.BTerm) :
    eval obj τ ρ (.test b : Term src tgt X X) = TypedKAT.test (b.eval (τ X)) := rfl

@[simp] theorem eval_act (a : ℕ) : eval obj τ ρ (.act a) = ρ a := rfl

@[simp] theorem eval_add (e f : Term src tgt X Y) :
    eval obj τ ρ (.add e f) = eval obj τ ρ e ⊔ eval obj τ ρ f := rfl

@[simp] theorem eval_comp (e : Term src tgt X Y) (f : Term src tgt Y Z) :
    eval obj τ ρ (.comp e f) = eval obj τ ρ e ≫ eval obj τ ρ f := rfl

@[simp] theorem eval_star (e : Term src tgt X X) :
    eval obj τ ρ (.star e) = (eval obj τ ρ e)∗ := rfl

/-- Pointwise equal environments give equal interpretations. -/
theorem eval_congr {τ' : ∀ A, ℕ → T (obj A)}
    {ρ' : ∀ a, obj (src a) ⟶ obj (tgt a)}
    (hτ : ∀ A a, τ A a = τ' A a) (hρ : ∀ a, ρ a = ρ' a)
    (e : Term src tgt X Y) : eval obj τ ρ e = eval obj τ' ρ' e := by
  obtain rfl : τ = τ' := funext fun A ↦ funext (hτ A)
  obtain rfl : ρ = ρ' := funext hρ
  rfl

end Evaluation

/-- A conditional can have different source and target objects. -/
def ifThenElse (b : KAT.BTerm) (e f : Term src tgt X Y) : Term src tgt X Y :=
  .add (.comp (.test b) e) (.comp (.test (.not b)) f)

/-- A loop body must be an endomorphism. -/
def whileDo (b : KAT.BTerm) (e : Term src tgt X X) : Term src tgt X X :=
  .comp (.star (.comp (.test b) e)) (.test (.not b))

section Commands

variable {C : Type v} [Category.{w} C] [KleeneCategory C]
  {T : C → Type z} [∀ A, BooleanAlgebra (T A)] [TypedKAT C T]
  (obj : I → C) (τ : ∀ A, ℕ → T (obj A))
  (ρ : ∀ a, obj (src a) ⟶ obj (tgt a))

@[simp] theorem eval_ifThenElse (b : KAT.BTerm) (e f : Term src tgt X Y) :
    eval obj τ ρ (ifThenElse b e f) =
      TypedKAT.ifThenElse (b.eval (τ X)) (eval obj τ ρ e) (eval obj τ ρ f) := rfl

@[simp] theorem eval_whileDo (b : KAT.BTerm) (e : Term src tgt X X) :
    eval obj τ ρ (whileDo b e) = TypedKAT.whileDo (b.eval (τ X)) (eval obj τ ρ e) := rfl

end Commands

/-- Rename objects, including identifying distinct objects. The result remains well typed. -/
def mapObjects {J : Type v} (f : I → J) :
    {A B : I} → Term src tgt A B → Term (f ∘ src) (f ∘ tgt) (f A) (f B)
  | _, _, .zero => .zero
  | _, _, .one => .one
  | _, _, .test b => .test b
  | _, _, .act a => .act a
  | _, _, .add e g => .add (e.mapObjects f) (g.mapObjects f)
  | _, _, .comp e g => .comp (e.mapObjects f) (g.mapObjects f)
  | _, _, .star e => .star (e.mapObjects f)

@[simp] theorem erase_mapObjects {J : Type v} (f : I → J) (e : Term src tgt X Y) :
    (e.mapObjects f).erase = e.erase := by
  induction e <;> simp_all [mapObjects, erase]

/-- Renaming objects commutes with interpretation when the environments are pulled back
along the same map. No injectivity assumption is needed. -/
theorem eval_mapObjects {J : Type v} {C : Type w} [Category.{z} C] [KleeneCategory C]
    {T : C → Type*} [∀ A, BooleanAlgebra (T A)] [TypedKAT C T]
    (f : I → J) (obj : J → C) (τ : ∀ A, ℕ → T (obj A))
    (ρ : ∀ a, obj (f (src a)) ⟶ obj (f (tgt a))) (e : Term src tgt X Y) :
    eval obj τ ρ (e.mapObjects f) = eval (obj ∘ f) (fun A ↦ τ (f A)) ρ e := by
  induction e <;> simp_all [mapObjects, eval] <;> rfl

end Term
end TypedKAT
