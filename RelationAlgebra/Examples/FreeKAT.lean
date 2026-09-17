import RelationAlgebra.TypedKAT.Free
import RelationAlgebra.Decide.HKATTactic

/-!
# Using the free typed KAT

These examples exercise quotient equality and order, generic KAT automation, interpretation
in other models, uniqueness, independent object-local tests, and unrestricted test indices.
-/

open CategoryTheory
open scoped Computability TypedKAT

universe u v w z

namespace TypedKAT.FreeExamples

section Model

variable {I : Type u} {src tgt : ℕ → I} {X Y : FreeCat src tgt}

/-- The quotient model supports the ordinary heterogeneous KAT laws. -/
theorem sliding (p : X ⟶ Y) (q : Y ⟶ X) : p ≫ (q ≫ p)∗ = (p ≫ q)∗ ≫ p := by kat

/-- Boolean normalization uses the free Boolean algebra of tests. -/
example (p : X ⟶ Y) (b c : FreeCat.Tests X) :
    ⌞b \ c⌟ ≫ p ⊔ ⌞b ⊓ c⌟ ≫ p = ⌞b⌟ ≫ p := by kat

/-- Hypotheses can be used in the quotient model through the existing tactic. -/
example (p : X ⟶ Y) (b c : FreeCat.Tests Y) (h : b ≤ c) :
    p ≫ ⌞b⌟ ≤ p ≫ ⌞c⌟ := by hkat

/-- Star induction remains rectangular. -/
example (p : X ⟶ X) (q : X ⟶ Y) (h : p ≫ q ≤ q) : p∗ ≫ q ≤ q :=
  KleeneCategory.kstar_comp_le_self p q h

example (p : X ⟶ X) (q : Y ⟶ X) (h : q ≫ p ≤ q) : q ≫ p∗ ≤ q :=
  KleeneCategory.comp_kstar_le_self p q h

/-- Quotient equality is equivalent to the checker-facing semantics at an adequate bound. -/
theorem equality_at_bound {A B : I} (e f : Term src tgt A B) (k : ℕ)
    (he : ∀ i ∈ e.tvars, i < k) (hf : ∀ i ∈ f.tvars, i < k) :
    FreeHom.ofTerm e = FreeHom.ofTerm f ↔ e.lang k = f.lang k := by
  rw [FreeHom.ofTerm_eq_iff, Term.semEq_iff_lang_eq k he hf]

/-- The induced order agrees with semantic inclusion, including after erasure. -/
example {A B : I} (e f : Term src tgt A B) :
    FreeHom.ofTerm e ≤ FreeHom.ofTerm f ↔ e.erase.SemLE f.erase := by
  rw [FreeHom.ofTerm_le_iff, Term.semLE_iff_erase]

example {A B : I} (e f : Term src tgt A B) :
    FreeHom.ofTerm e = FreeHom.ofTerm f ↔ e.erase.SemEq f.erase := by
  rw [FreeHom.ofTerm_eq_iff, Term.semEq_iff_erase]

/-- The class of an expression can be manipulated using ordinary categorical notation. -/
example {A B : I} (e : Term src tgt A B) :
    FreeHom.ofTerm (e.add (.comp .one e)) = FreeHom.ofTerm e := by
  simp

end Model

section Interpretation

variable {I : Type u} {src tgt : ℕ → I}
  {C : Type v} [Category.{w} C] [KleeneCategory C]
  {T : C → Type z} [∀ A, BooleanAlgebra (T A)] [TypedKAT C T]
  (o : I → C) (τ : ∀ A, ℕ → T (o A)) (ρ : ∀ a, o (src a) ⟶ o (tgt a))

/-- The universal property works with independent object, morphism, and test universes. -/
theorem unique_extension :
    ∃! F : Hom (FreeCat.Tests (src := src) (tgt := tgt)) T (fun X ↦ o X.object),
      (∀ X i, F.testMap (FreeCat.ofObject X) (FreeCat.testVar (FreeCat.ofObject X) i) = τ X i) ∧
      (∀ a, F.map (FreeCat.action a) = ρ a) := FreeCat.existsUnique_lift o τ ρ

/-- Interpreting a composite class computes composition in the target category. -/
example {A B D : I} (e : Term src tgt A B) (f : Term src tgt B D) :
    (FreeCat.lift o τ ρ).map (X := FreeCat.ofObject A) (Y := FreeCat.ofObject D)
      (FreeHom.ofTerm (e.comp f)) = e.eval o τ ρ ≫ f.eval o τ ρ := rfl

/-- Interpretation is also available as an ordinary category-theoretic functor. -/
example (a : ℕ) : (FreeCat.lift o τ ρ).toFunctor.map (FreeCat.action a) = ρ a := rfl

/-- A proposed extension is unique once its values on generators have been checked. -/
example (F : Hom (FreeCat.Tests (src := src) (tgt := tgt)) T (fun X ↦ o X.object))
    (ht : ∀ X i, F.testMap (FreeCat.ofObject X) (FreeCat.testVar (FreeCat.ofObject X) i) = τ X i)
    (ha : ∀ a, F.map (FreeCat.action a) = ρ a) : F = FreeCat.lift o τ ρ :=
  FreeCat.lift_unique o τ ρ F ht ha

end Interpretation

/-! No fixed atom bound is baked into the expression quotient. -/

/-- Every test generator can be true, however large its index. -/
theorem testVar_ne_bot (n : ℕ) : KAT.FreeTest.var n ≠ ⊥ := by
  intro h
  have hh := congrArg (KAT.FreeTest.lift (fun _ ↦ (⊤ : Set Unit))) h
  simp at hh

private abbrev loopSource (_ : ℕ) : Unit := ()

/-- Bound zero cannot distinguish this variable from false; the quotient still can. -/
theorem insufficient_bound :
    (Term.test (.tvar 100) : Term loopSource loopSource () ()).lang 0 =
      (Term.test .bot : Term loopSource loopSource () ()).lang 0 ∧
    FreeHom.ofTerm (Term.test (.tvar 100) : Term loopSource loopSource () ()) ≠
      FreeHom.ofTerm (Term.test .bot : Term loopSource loopSource () ()) := by
  constructor
  · apply Language.ext
    ext ⟨α, l⟩
    change (l = [] ∧ α ∈ KAT.allAtoms 0 ∧ α.sat (.tvar 100) = true) ↔
      (l = [] ∧ α ∈ KAT.allAtoms 0 ∧ false = true)
    constructor
    · rintro ⟨_, hα, h⟩
      have hnil := List.length_eq_zero_iff.mp (KAT.mem_allAtoms.mp hα)
      subst α
      cases h
    · rintro ⟨_, _, h⟩
      cases h
  · intro h
    exact testVar_ne_bot 100 (FreeHom.test_injective h)

/-! An infinite object alphabet with independent tests, even after objects are identified. -/

private abbrev source (n : ℕ) : ℕ := n
private abbrev target (n : ℕ) : ℕ := n + 1
private abbrev Chain := FreeCat source target
private def node (n : ℕ) : Chain := ⟨n⟩

private def state : RelCat := Unit
private def collapsedObjects (_ : ℕ) : RelCat := state
private def localTests (n _i : ℕ) : Set (collapsedObjects n) := if n = 0 then ⊤ else ⊥
private def collapsedActions (_a : ℕ) :
    collapsedObjects (source _a) ⟶ collapsedObjects (target _a) := 𝟙 state

private def collapse :=
  FreeCat.lift (src := source) (tgt := target) collapsedObjects localTests collapsedActions

/-- Identifying all objects leaves their primitive test valuations independent. -/
theorem distinct_local_tests :
    collapse.testMap (node 0) (FreeCat.testVar (node 0) 7) ≠
      collapse.testMap (node 1) (FreeCat.testVar (node 1) 7) := by
  change (⊤ : Set Unit) ≠ ⊥
  simp

/-- A concrete guarded path evaluates with its independent source and target tests. -/
example : collapse.map (X := node 0) (Y := node 1)
    (FreeHom.ofTerm (.comp (.test (.tvar 0)) (.comp (.act 0) (.test (.tvar 0))))) = ⊥ := by
  change (Term.comp (.test (.tvar 0)) (.comp (.act 0) (.test (.tvar 0))) :
    Term source target 0 1).eval collapsedObjects localTests collapsedActions = ⊥
  have hz : TypedKAT.test (C := RelCat) (T := Set) (X := collapsedObjects (target 0))
      (localTests (target 0) 0) = ⊥ := TypedKAT.test_bot
  simp only [Term.eval, KAT.BTerm.eval, hz, KleeneCategory.comp_bot]

/-- Distinct actions remain distinct classes; an interpretation can separate them. -/
example : FreeHom.ofTerm (Term.act 0 : Term loopSource loopSource () ()) ≠
    FreeHom.ofTerm (Term.act 1 : Term loopSource loopSource () ()) := by
  intro h
  have hh := congrArg (FreeHom.eval (C := RelCat) (src := loopSource) (tgt := loopSource)
    (T := Set) (fun _ : Unit ↦ state)
    (fun _ _ ↦ (⊤ : Set Unit)) (fun a ↦ if a = 0 then 𝟙 state else ⊥)) h
  have hm := congrArg (fun r : state ⟶ state ↦ ((), ()) ∈ r.rel) hh
  change (((), ()) ∈ SetRel.id) = (((), ()) ∈ (∅ : SetRel Unit Unit)) at hm
  exact (iff_of_eq hm).mp rfl

end TypedKAT.FreeExamples
