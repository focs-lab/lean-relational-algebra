import RelationAlgebra.TypedKAT.GuardedString

/-!
# Using typed KAT expressions

These examples check heterogeneous composition, endomorphism-only iteration, independent
test valuations at different objects, and the connection with the guarded-string checker.
The `fail_if_success` examples ensure Lean rejects expressions with incompatible endpoints.
No tactic for equations in arbitrary typed KATs is claimed here.
-/

open CategoryTheory TypedKAT
open scoped Computability

namespace TypedKAT.Examples

/-! Action `n` goes from object `n` to object `n + 1`. -/

private abbrev src (n : ℕ) := n
private abbrev tgt (n : ℕ) := n + 1

/-- A path through three objects. -/
def twoSteps : Term src tgt 0 2 := .comp (.act 0) (.act 1)

example : Term src tgt 0 2 := by
  fail_if_success exact Term.comp (Term.act (src := src) (tgt := tgt) 1) (Term.act 0)
  exact twoSteps

example : Term src tgt 0 1 := by
  fail_if_success exact Term.one
  fail_if_success exact Term.star (Term.act (src := src) (tgt := tgt) 0)
  fail_if_success exact Term.comp (.test .top : Term src tgt 1 1) (.act 0)
  exact .act 0

/-- Guarding a heterogeneous command is allowed; its two tests live at different objects. -/
def guardedSteps : Term src tgt 0 2 :=
  .comp (.test (.tvar 0)) (.comp twoSteps (.test (.tvar 0)))

example : guardedSteps.tvarsBelow 1 = true := by decide
example : guardedSteps.tvarsBelow 0 = false := by decide

example : twoSteps.erase = .mul (.act 0) (.act 1) := rfl

example : (twoSteps.mapObjects (fun _ ↦ ())).erase = twoSteps.erase :=
  Term.erase_mapObjects _ _

/-! Interpret object `n` as `Fin (n + 1)`, and action `n` as incrementing the state. -/

private def obj (n : ℕ) : RelCat := Fin (n + 1)

private def action (n : ℕ) : obj (src n) ⟶ obj (tgt n) :=
  RelCat.Hom.ofRel {p | p.2.val = p.1.val + 1}

private def tests (n : ℕ) (_ : ℕ) : Set (obj n) := {x | x.val = n}

/-- Both steps are taken in source-to-target order, across three different state spaces. -/
example : ((0 : Fin 1), (2 : Fin 3)) ∈ (twoSteps.eval obj tests action).rel := by
  change ∃ b : Fin 2, b.val = (0 : Fin 1).val + 1 ∧ (2 : Fin 3).val = b.val + 1
  exact ⟨1, rfl, rfl⟩

example : ((0 : Fin 1), (0 : Fin 3)) ∉ (twoSteps.eval obj tests action).rel := by
  change ¬ ∃ b : Fin 2, b.val = (0 : Fin 1).val + 1 ∧ (0 : Fin 3).val = b.val + 1
  omega

/-- The same predicate number denotes `{0}` at object 0 and `{2}` at object 2. -/
example : ((0 : Fin 1), (2 : Fin 3)) ∈ (guardedSteps.eval obj tests action).rel := by
  change ∃ b : Fin 1, ((0 : Fin 1) = b ∧ (0 : Fin 1).val = 0) ∧
    ∃ c : Fin 3, (∃ d : Fin 2, d.val = b.val + 1 ∧ c.val = d.val + 1) ∧
      (c = (2 : Fin 3) ∧ c.val = 2)
  exact ⟨0, ⟨rfl, rfl⟩, 2, ⟨1, rfl, rfl⟩, rfl, rfl⟩

/-! Guarded strings retain every intermediate atom and all action endpoints. -/

example : ([true], [(0, [false]), (1, [true])]) ∈ (guardedSteps.lang 1).strings := by
  rw [Term.strings_lang]
  apply KAT.mem_fuse.2
  refine ⟨[], [(0, [false]), (1, [true])], rfl, ?_, ?_⟩
  · simp [Term.erase, KAT.KTerm.gs, KAT.allAtoms, KAT.Atom.sat]
  · apply KAT.mem_fuse.2
    refine ⟨[(0, [false]), (1, [true])], [], rfl, ?_, ?_⟩
    · apply KAT.mem_fuse.2
      exact ⟨[(0, [false])], [(1, [true])], rfl,
        by simp [Term.erase, KAT.KTerm.mem_gs_act, KAT.allAtoms],
        by simp [Term.erase, KAT.KTerm.mem_gs_act, KAT.allAtoms]⟩
    · simp [Term.erase, KAT.KTerm.gs, KAT.allAtoms, KAT.Atom.sat]

example : ¬ PathTyped src tgt 0 [1, 0] 2 := by simp [src]
example : ¬ PathTyped src tgt 0 [] 2 := by simp

/-- An action cannot bypass a false source test. -/
example : ([false], [(0, [true])]) ∉
    ((Term.comp (.test (.tvar 0)) (.act 0) : Term src tgt 0 1).lang 1).strings := by
  rw [Term.strings_lang]
  intro h
  obtain ⟨_, _, _, hb, _⟩ := KAT.mem_fuse.1 h
  have bad : false = true := hb.2.2
  cases bad

/-- Zero iterations accepts a single atom, including when there are no test variables. -/
example : ([], []) ∈ ((Term.star .zero : Term src tgt 0 0).lang 0).strings := by
  rw [Term.strings_lang]
  exact Set.mem_iUnion.2 ⟨0, rfl, by simp [KAT.allAtoms]⟩

example (g : KAT.GStr) (h : g ∈ (twoSteps.lang 1).strings) :
    PathTyped src tgt 0 (g.2.map Prod.fst) 2 ∧ KAT.GStr.wf 1 g :=
  ⟨(twoSteps.lang 1).pathTyped g h, (twoSteps.lang 1).wellFormed g h⟩

/-! Iteration is allowed once a pair of heterogeneous actions returns to its source. -/

private abbrev cycleSrc (a : ℕ) : ℕ := if a = 0 then 0 else 1
private abbrev cycleTgt (a : ℕ) : ℕ := if a = 0 then 1 else 0

private def slideLeft : Term cycleSrc cycleTgt 0 1 :=
  .comp (.act 0) (.star (.comp (.act 1) (.act 0)))

private def slideRight : Term cycleSrc cycleTgt 0 1 :=
  .comp (.star (.comp (.act 0) (.act 1))) (.act 0)

/-- The existing certificate checker can already establish equality of typed languages. -/
example : slideLeft.lang 0 = slideRight.lang 0 :=
  Term.lang_eq_of_decideEq (fuel := 100) (by decide)

example {C : Type*} [Category C] [KleeneCategory C]
    {T : C → Type*} [∀ X, BooleanAlgebra (T X)] [TypedKAT C T]
    (o : ℕ → C) (τ : ∀ X, ℕ → T (o X))
    (ρ : ∀ a, o (cycleSrc a) ⟶ o (cycleTgt a)) :
    slideLeft.eval o τ ρ = slideRight.eval o τ ρ :=
  KleeneCategory.comp_kstar_eq_kstar_comp (ρ 0) (ρ 1)

/-- `SingleObj` uses Mathlib's reversed multiplication convention. This interpretation
check guards against accidentally identifying ordinary erasure with that convention. -/
example {T K : Type*} [BooleanAlgebra T] [KleeneAlgebra K] [KAT T K]
    (τ : ℕ → T) (ρ : ℕ → K) :
    twoSteps.eval (T := fun _ ↦ T) (fun _ ↦ SingleObj.star K) (fun _ ↦ τ) ρ =
      ρ 1 * ρ 0 := rfl

end TypedKAT.Examples
