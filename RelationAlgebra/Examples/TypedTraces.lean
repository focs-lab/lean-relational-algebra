import RelationAlgebra.Models.TypedTrace
import RelationAlgebra.Decide.HKATTactic
import RelationAlgebra.Decide.RaTactic

/-!
# General typed trace examples

Action `n` goes from object `n` to `n+1`. Fusion additionally requires equal boundary
states. These are independent checks: correct object types alone do not permit fusion.
-/

open CategoryTheory TypedTrace
open scoped Computability TypedKAT TraceLang ResiduatedKleeneCategory

namespace Examples.TypedTraces

abbrev src (a : ℕ) := a
abbrev tgt (a : ℕ) := a + 1
abbrev Obj (n : ℕ) : TraceCat Bool src tgt := ⟨n⟩

def first : Obj 0 ⟶ Obj 1 := TypedTrace.Language.step false 0 true
def second : Obj 1 ⟶ Obj 2 := TypedTrace.Language.step true 1 false
def mismatched : Obj 1 ⟶ Obj 2 := TypedTrace.Language.step false 1 false

theorem two_actions : (false, [(0, true), (1, false)]) ∈ (first ≫ second).traces :=
  ⟨[(0, true)], [(1, false)], rfl, rfl, rfl⟩

theorem no_fusion : first ≫ mismatched = ⊥ := by
  apply TypedTrace.Language.ext
  ext ⟨s, l⟩
  constructor
  · rintro ⟨l₁, l₂, _, h₁, h₂⟩
    change (s, l₁) = (false, [(0, true)]) at h₁
    have hsteps : l₁ = [(0, true)] := congrArg Prod.snd h₁
    change (Trace.lastOf s l₁, l₂) = (false, [(1, false)]) at h₂
    have hstate : Trace.lastOf s l₁ = false := congrArg Prod.fst h₂
    simp only [hsteps, Trace.lastOf_cons, Trace.lastOf_nil] at hstate
    cases hstate
  · exact False.elim

theorem empty_is_not_rectangular :
    (false, []) ∉ (⊤ : Obj 0 ⟶ Obj 1).traces := by
  change ¬ (0 = 1)
  decide

theorem wrong_action_is_not_top :
    (false, [(1, true)]) ∉ (⊤ : Obj 0 ⟶ Obj 1).traces := by
  change ¬ (0 = 1 ∧ 2 = 1)
  decide

theorem right_action_is_top :
    (false, [(0, true)]) ∈ (⊤ : Obj 0 ⟶ Obj 1).traces := ⟨rfl, rfl⟩

theorem complement_stays_typed :
    (false, [(1, true)]) ∉ (firstᶜ).traces := fun h ↦ by
  have ht := h.1
  exact (Nat.zero_ne_one ht.1)

theorem residual_stays_typed :
    (false, []) ∉ ((⊥ : Obj 0 ⟶ Obj 1) ⇘ (⊥ : Obj 0 ⟶ Obj 2)).traces := fun h ↦ by
  have ht := h.1
  exact (by decide : (1 : ℕ) ≠ 2) ht

example : (false, []) ∈ (⊥ : Obj 0 ⟶ Obj 0)∗.traces := by
  rw [KleeneCategory.kstar_bot]
  rfl

example : (false, []) ∉ (⊥ : Obj 0 ⟶ Obj 0)⁺.traces := by
  rw [KleeneCategory.kplus_bot]
  exact id

example (R : Obj 0 ⟶ Obj 1) (S : Obj 1 ⟶ Obj 0) :
    R ≫ (S ≫ R)∗ = (R ≫ S)∗ ≫ R := by kat

example (R : Obj 0 ⟶ Obj 1) (S : Obj 1 ⟶ Obj 0) :
    R ≫ (S ≫ R)⁺ = (R ≫ S)⁺ ≫ R := by kat

example (R : Obj 0 ⟶ Obj 1) : R ⊔ Rᶜ = ⊤ := by ra

example (R : Obj 0 ⟶ Obj 1) (T : Obj 0 ⟶ Obj 2) : R ≫ (R ⇘ T) ≤ T := by ra

example (R : Obj 0 ⟶ Obj 1) (S : Obj 1 ⟶ Obj 0) (h : R ≫ S = ⊥) :
    R ≫ (S ≫ R)∗ ≫ S = ⊥ := by hkat

example (P : Set Bool) :
    (TypedKAT.test (T := fun _ : TraceCat Bool src tgt ↦ Set Bool) P : Obj 0 ⟶ Obj 0) ≫
      TypedKAT.test (T := fun _ : TraceCat Bool src tgt ↦ Set Bool) Pᶜ = ⊥ := by kat

example : TraceCat.atom (Obj 0) false ≫ TraceCat.action 0 ≫ TraceCat.atom (Obj 1) true =
    first := TraceCat.atom_action_atom false true 0

example : (⊤ : Obj 0 ⟶ Obj 1).traces ≠ (⊤ : TraceLang Bool ℕ) := by
  intro h
  have ht : (false, []) ∈ (⊤ : Obj 0 ⟶ Obj 1).traces := h ▸ Set.mem_univ _
  exact empty_is_not_rectangular ht

example : True := by
  fail_if_success have _ := first ≫ first
  fail_if_success have _ := first∗
  trivial

abbrev Loop : TraceCat Bool (fun _ : Unit ↦ ()) (fun _ ↦ ()) := ⟨()⟩

def toggle : Loop ⟶ Loop :=
  TypedTrace.Language.step false () true ⊔ TypedTrace.Language.step true () false

theorem two_toggle_steps :
    (false, [((), true), ((), false)]) ∈ (toggle⁺).traces := by
  change (false, [((), true), ((), false)]) ∈ toggle.traces * toggle.traces∗
  refine ⟨[((), true)], [((), false)], rfl, Or.inl rfl, ?_⟩
  exact (show toggle.traces ⊆ toggle.traces∗ from le_kstar) (Or.inr rfl)

theorem toggle_no_empty_path : (false, []) ∉ (toggle⁺).traces := by
  rintro ⟨l₁, l₂, hnil, htoggle, _⟩
  have hlen := List.append_eq_nil_iff.mp hnil.symm
  change (false, l₁) = (false, [((), true)]) ∨ (false, l₁) = (true, [((), false)]) at htoggle
  simp [hlen.1] at htoggle

example : (false, []) ∈ (toggle∗).traces :=
  (show (1 : TraceLang Bool Unit) ⊆ toggle.traces∗ from one_le_kstar) rfl

example : True := by
  fail_if_success have _ : toggle⁺ = toggle∗ := by kat
  trivial

section Universes

universe u v w
variable {σ : Type u} {α : Type v} {I : Type w} {s t : α → I}
  {X Y : TraceCat σ s t}

example (R : X ⟶ Y) (S : Y ⟶ X) : R ≫ (S ≫ R)∗ = (R ≫ S)∗ ≫ R := by kat

example (R : X ⟶ Y) : R ⊔ Rᶜ = ⊤ := by ra

example (R : X ⟶ X) : (R∗).traces = R.traces∗ := rfl

example (R : TypedTrace.Language σ (fun _ : α ↦ ()) (fun _ ↦ ()) () ()) :
    TypedTrace.Language.oneObjectOrderIso R = R.traces := rfl

end Universes
end Examples.TypedTraces
