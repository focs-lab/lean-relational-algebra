import RelationAlgebra.TypedKAT.Syntax

/-!
# Restricting a typed expression to its finite object support

Even when the object alphabet is infinite, a pair of expressions uses only finitely many
objects. Restriction preserves erasure and evaluation, so a completeness theorem for finite
object alphabets suffices. Unused actions are assigned bottom when either endpoint lies
outside the support; every action that occurs in a restricted expression keeps its value.
-/

open CategoryTheory

universe u v w z

namespace TypedKAT.Term

variable {I : Type u} [DecidableEq I] {src tgt : ℕ → I} {X Y : I}

/-- Every object named by an expression, including the endpoints of zero and identity. -/
def objects : {A B : I} → Term src tgt A B → Finset I
  | A, B, .zero => {A, B}
  | A, _, .one => {A}
  | A, _, .test _ => {A}
  | _, _, .act a => {src a, tgt a}
  | _, _, .add e f => e.objects ∪ f.objects
  | _, _, .comp e f => e.objects ∪ f.objects
  | _, _, .star e => e.objects

theorem source_mem_objects (e : Term src tgt X Y) : X ∈ e.objects := by
  induction e <;> simp_all [objects]

theorem target_mem_objects (e : Term src tgt X Y) : Y ∈ e.objects := by
  induction e <;> simp_all [objects]

variable {s : Finset I}

/-- Transport only the endpoints of an expression, retaining its constructors. -/
def castEndpoints {A B A' B' : I} (hA : A = A') (hB : B = B')
    (e : Term src tgt A B) : Term src tgt A' B' := hA ▸ hB ▸ e

omit [DecidableEq I] in
@[simp] theorem erase_castEndpoints {A B A' B' : I} (hA : A = A') (hB : B = B')
    (e : Term src tgt A B) : (castEndpoints hA hB e).erase = e.erase := by
  subst A'; subst B'; rfl

/-- Map all objects into a nonempty finite support, retaining every object in the support. -/
def clip (d : s) (i : I) : s := if h : i ∈ s then ⟨i, h⟩ else d

@[simp] theorem clip_mem (d : s) {i : I} (hi : i ∈ s) : clip d i = ⟨i, hi⟩ := by
  simp [clip, hi]

/-- Retype an expression over a finite support containing all its objects. -/
def restrict (d : s) : {A B : I} → (e : Term src tgt A B) → (h : e.objects ⊆ s) →
    Term (clip d ∘ src) (clip d ∘ tgt)
      ⟨A, h (source_mem_objects e)⟩ ⟨B, h (target_mem_objects e)⟩
  | _, _, .zero, _ => .zero
  | _, _, .one, _ => .one
  | _, _, .test b, _ => .test b
  | _, _, .act a, h => by
    have hs : src a ∈ s := h (source_mem_objects (.act a))
    have ht : tgt a ∈ s := h (target_mem_objects (.act a))
    exact castEndpoints (clip_mem d hs) (clip_mem d ht)
      (Term.act a : Term (clip d ∘ src) (clip d ∘ tgt) _ _)
  | _, _, .add e f, h =>
    .add (restrict d e (Finset.Subset.trans Finset.subset_union_left h))
      (restrict d f (Finset.Subset.trans Finset.subset_union_right h))
  | _, _, .comp e f, h =>
    .comp (restrict d e (Finset.Subset.trans Finset.subset_union_left h))
      (restrict d f (Finset.Subset.trans Finset.subset_union_right h))
  | _, _, .star e, h => .star (restrict d e h)

@[simp] theorem erase_restrict (d : s) (e : Term src tgt X Y) (h : e.objects ⊆ s) :
    (e.restrict d h).erase = e.erase := by
  induction e with
  | zero => rfl
  | one => rfl
  | test _ => rfl
  | act a =>
    simp only [restrict, erase_castEndpoints, erase]
  | add e f he hf => simp only [restrict, erase, he, hf]
  | comp e f he hf => simp only [restrict, erase, he, hf]
  | star e he => simp only [restrict, erase, he]

section Evaluation

variable {C : Type v} [Category.{w} C] [KleeneCategory C]
  {T : C → Type z} [∀ A, BooleanAlgebra (T A)] [TypedKAT C T]
  (d : s) (o : I → C) (τ : ∀ A, ℕ → T (o A)) (ρ : ∀ a, o (src a) ⟶ o (tgt a))

omit [DecidableEq I] in
@[simp] theorem eval_castEndpoints {A B A' B' : I} (hA : A = A') (hB : B = B')
    (e : Term src tgt A B) :
    (castEndpoints hA hB e).eval o τ ρ =
      eqToHom (congrArg o hA.symm) ≫ e.eval o τ ρ ≫ eqToHom (congrArg o hB) := by
  subst A'; subst B'
  simp [castEndpoints]

/-- Restrict the action environment. Values outside the finite support are never used. -/
def restrictActions (a : ℕ) : o (clip d (src a)).val ⟶ o (clip d (tgt a)).val :=
  if hs : src a ∈ s then
    if ht : tgt a ∈ s then
      eqToHom (congrArg (fun i : s ↦ o i.val) (clip_mem d hs)) ≫ ρ a ≫
        eqToHom (congrArg (fun i : s ↦ o i.val) (clip_mem d ht).symm)
    else ⊥
  else ⊥

/-- Restriction preserves evaluation in every typed KAT. -/
@[simp] theorem eval_restrict (e : Term src tgt X Y) (h : e.objects ⊆ s) :
    (e.restrict d h).eval (fun i : s ↦ o i.val) (fun i ↦ τ i.val) (restrictActions d o ρ) =
      e.eval o τ ρ := by
  induction e with
  | zero => rfl
  | one => rfl
  | test _ => rfl
  | act a =>
    have hs := h (source_mem_objects (Term.act (src := src) (tgt := tgt) a))
    have ht := h (target_mem_objects (Term.act (src := src) (tgt := tgt) a))
    rw [restrict]
    have hh := eval_castEndpoints (src := clip d ∘ src) (tgt := clip d ∘ tgt)
      (T := T) (fun i : s ↦ o i.val) (fun i ↦ τ i.val) (restrictActions d o ρ)
      (clip_mem d hs) (clip_mem d ht) (Term.act a)
    refine hh.trans ?_
    simp only [eval, restrictActions, dif_pos hs, dif_pos ht, ← Category.assoc,
      eqToHom_trans, eqToHom_refl, Category.id_comp]
    simp [Category.assoc]
  | add e f he hf => simp only [restrict, eval, he, hf]
  | comp e f he hf => simp only [restrict, eval, he, hf]
  | star e he => simp only [restrict, eval, he]

end Evaluation
end TypedKAT.Term
