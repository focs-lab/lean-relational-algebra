import RelationAlgebra.TypedKAT.LanguageModel
import RelationAlgebra.Decide.HKATTactic

/-!
# Using the typed guarded-string language model

The model has arbitrary object alphabets, heterogeneous language morphisms, and sets of
bounded atoms as tests. These examples exercise generic algebraic rules, tactic support,
the canonical interpretation, and membership in the actual language representation.
-/

open CategoryTheory
open scoped Computability TypedKAT

universe u

namespace TypedKAT.LanguageModelExamples

section General

variable {I : Type u} {src tgt : ℕ → I} {k : ℕ}
  {X Y Z : LanguageCat src tgt k}

/-- The model can use generic typed KAT automation with heterogeneous actions. -/
theorem sliding (p : X ⟶ Y) (q : Y ⟶ X) : p ≫ (q ≫ p)∗ = (p ≫ q)∗ ≫ p := by kat

example (p : X ⟶ Y) (P : LanguageCat.Tests X) : ⌞P⌟ ≫ p ⊔ ⌞Pᶜ⌟ ≫ p = p := by kat

/-- The same Boolean algebra can supply independent source and target guards. -/
example (p : X ⟶ Y) (P : LanguageCat.Tests X) (Q : LanguageCat.Tests Y) :
    ⌞P⌟ ≫ p ≫ ⌞Q⌟ ≤ p := by kat

/-- A Boolean hypothesis is available at the target as well as the source. -/
example (p : X ⟶ Y) (P Q : LanguageCat.Tests Y) (h : P ≤ Q) :
    p ≫ ⌞P⌟ ≤ p ≫ ⌞Q⌟ := by hkat

/-- Hoare specifications compose in the new model just as in relations and matrices. -/
theorem sequence (p : X ⟶ Y) (q : Y ⟶ Z) (P : LanguageCat.Tests X)
    (Q : LanguageCat.Tests Y) (R : LanguageCat.Tests Z)
    (hp : TypedKAT.HoareTriple P p Q) (hq : TypedKAT.HoareTriple Q q R) :
    TypedKAT.HoareTriple P (p ≫ q) R := by hkat

/-- The rectangular induction axiom works through the bundled category interface. -/
theorem left_induction (p : X ⟶ X) (q : X ⟶ Y) (h : p ≫ q ≤ q) : p∗ ≫ q ≤ q :=
  KleeneCategory.kstar_comp_le_self p q h

theorem right_induction (p : X ⟶ X) (q : Y ⟶ X) (h : q ≫ p ≤ q) : q ≫ p∗ ≤ q :=
  KleeneCategory.comp_kstar_le_self p q h

/-- Existing endomorphism KAT instances are available without a new single-sorted model. -/
example (p q : End X) : (p + q)∗ = p∗ * (q * p∗)∗ := by kat

/-- Canonical interpretation and the checker-facing semantics coincide at every bound. -/
theorem canonical (e : Term src tgt X.object Y.object) :
    e.eval (T := fun _ : LanguageCat src tgt k ↦ Set (BoundedAtom k))
      (LanguageCat.ofObject (src := src) (tgt := tgt) (k := k))
      (fun _ ↦ LanguageCat.testVar) LanguageCat.action = e.lang k :=
  e.eval_languageCat k

end General

/-! An infinite object alphabet: action `n` goes from object `n` to object `n + 1`. -/

private abbrev Chain := LanguageCat (fun n : ℕ ↦ n) (fun n ↦ n + 1) 1

private def node (n : ℕ) : Chain := ⟨n⟩

private def step (n : ℕ) : node n ⟶ node (n + 1) := LanguageCat.action n

/-- The identity includes each correctly sized atom at its object. -/
example : ([true], []) ∈ Language.strings (𝟙 (node 0)) := by
  change ([true], []) ∈ KAT.unitGS 1
  simp [KAT.unitGS, KAT.mem_allAtoms]

/-- A malformed atom is absent even from the identity language. -/
example : ([], []) ∉ Language.strings (𝟙 (node 0)) := by
  change ([], []) ∉ KAT.unitGS 1
  simp [KAT.unitGS, KAT.mem_allAtoms]

/-- An empty action path cannot connect distinct objects. -/
example (L : node 0 ⟶ node 1) : ([false], []) ∉ L.strings := by
  intro h
  have hp := L.pathTyped _ h
  change (0 : ℕ) = 1 at hp
  omega

/-- Fusion accepts the shared atom exactly once. -/
theorem two_steps : ([true], [(0, [false]), (1, [true])]) ∈ (step 0 ≫ step 1).strings := by
  change _ ∈ KAT.fuse (Language.act (src := fun n : ℕ ↦ n) (tgt := fun n ↦ n + 1)
    (k := 1) 0).strings (Language.act 1).strings
  apply KAT.mem_fuse.2
  refine ⟨[(0, [false])], [(1, [true])], rfl, ?_, ?_⟩ <;>
    simp [Language.act, KAT.KTerm.gs, KAT.mem_allAtoms]

/-- The Boolean test reads the atom at the intermediate object. -/
example : ([true], [(0, [false]), (1, [true])]) ∉
    (step 0 ≫ ⌞LanguageCat.testVarAt (node 1) 0⌟ ≫ step 1).strings := by
  change _ ∉ KAT.fuse (step 0).strings
    (KAT.fuse (Language.ofAtoms (LanguageCat.testVar (k := 1) 0)).strings (step 1).strings)
  simp [KAT.mem_fuse, step, LanguageCat.action, Language.act, KAT.KTerm.gs,
    LanguageCat.testVar, List.cons_eq_append_iff, KAT.mem_allAtoms]

private abbrev LoopModel := LanguageCat (fun _ : ℕ ↦ ()) (fun _ ↦ ()) 1

private def loopObject : LoopModel := ⟨()⟩

private def loop : loopObject ⟶ loopObject := LanguageCat.action 0

/-- Star contains actual repeated guarded strings, with the shared atoms fused. -/
theorem twice_in_star :
    ([true], [(0, [false]), (0, [true])]) ∈ Language.strings (loop∗) := by
  change _ ∈ ⋃ n, (Language.pow loop n).strings
  apply Set.mem_iUnion.2
  refine ⟨2, ?_⟩
  simp [Language.pow, Language.comp, Language.one, loop, LanguageCat.action,
    Language.act, KAT.KTerm.gs, KAT.mem_fuse, KAT.unitGS, KAT.mem_allAtoms,
    List.cons_eq_append_iff]

/-- At bound zero there is still one atom, the empty valuation. -/
example : ([], []) ∈
    Language.strings
      (𝟙 (LanguageCat.ofObject (src := fun n : ℕ ↦ n) (tgt := fun n ↦ n) (k := 0) 0)) := by
  change ([], []) ∈ KAT.unitGS 0
  simp [KAT.unitGS, KAT.mem_allAtoms]

/-- A fixed bound keeps the existing false default for out-of-range variables. -/
example : LanguageCat.testVar (k := 0) 3 = (⊥ : Set (BoundedAtom 0)) := by
  ext α
  simp [LanguageCat.testVar]

/-- Distinct primitive tests must not be identified by the bundled model. -/
example : (Language.ofAtoms (LanguageCat.testVar (k := 1) 0) : node 0 ⟶ node 0) ≠
    Language.ofAtoms (LanguageCat.testVar (k := 1) 0)ᶜ := by
  intro h
  have he := Language.ofAtoms_injective h
  have hm := congrArg (fun P : Set (BoundedAtom 1) ↦ (⟨[true], rfl⟩ : BoundedAtom 1) ∈ P) he
  simp [LanguageCat.testVar] at hm

end TypedKAT.LanguageModelExamples
