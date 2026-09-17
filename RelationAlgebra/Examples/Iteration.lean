import RelationAlgebra.Decide.Tactic
import RelationAlgebra.Decide.HKATTactic
import RelationAlgebra.Decide.RaTactic
import RelationAlgebra.Models.MatrixIteration

/-!
# Strict iteration: algebra, tactics, and nonempty paths

Tests cover arbitrary carriers, rectangular contexts, hypothesis preprocessing, concrete
relations and matrices, endpoint rejection, invalid identities, and multiple goals.
-/

open CategoryTheory
open scoped Computability KAT TypedKAT KleeneCategoryWithConverse

universe u v
namespace IterationExamples

section Scalar
variable {K : Type u} [KleeneAlgebra K] (a b c : K)

theorem scalar_unfold : a⁺ = a + a * a⁺ := by ka
theorem scalar_sliding : a * (b * a)⁺ = (a * b)⁺ * a := by ka
example : a⁺ = a + a⁺ * a := by kat
example : a⁺⁺ = a⁺ := by ka
example : a⁺ * a⁺ ≤ a⁺ := by ka
example : (a⁺)∗ = a∗ := by kat
example : (a∗)⁺ = a∗ := by ka
example : (a⁺ + b⁺)⁺ = (a+b)⁺ := by ka
example : (0 : K)⁺ = 0 := by ka
example : (1 : K)⁺ = 1 := by kat
example : ∀ (a : K), a⁺ = a * a∗ := by ka
example (h : a * b ≤ c) (hc : a * c ≤ c) : a⁺ * b ≤ c :=
  KleeneAlgebra.kplus_mul_le h hc
example (h : b * a ≤ c) (hc : c * a ≤ c) : b * a⁺ ≤ c :=
  KleeneAlgebra.mul_kplus_le h hc
example (h : a * a = a) : (a * b)⁺ * a = (a * b * a)⁺ := KleeneAlgebra.kplus_mul_of_idempotent a b h

example : True := by
  fail_if_success have : a⁺ = a∗ := by ka
  fail_if_success have : 1 ≤ a⁺ := by kat
  fail_if_success have : a⁺ * b⁺ = (a * b)⁺ := by ka
  fail_if_success have : a⁺ * a⁺ = a⁺ := by kat
  fail_if_success have : a⁺ = a + a * a⁺ := by ka 0
  trivial

set_option linter.style.multiGoal false in
example : (0 : K)⁺ = 0 ∧ True := by
  constructor
  ka
  trivial

set_option linter.style.multiGoal false in
example : a⁺ = a + a * a⁺ ∧ True := by
  constructor
  kat
  trivial
end Scalar

section Converse
variable {K : Type u} [KleeneAlgebra K] [StarRing K] (a b : K)

theorem scalar_converse : star (a⁺) = (star a)⁺ := by ra
example : (star (a⁺))⁺ = (star a)⁺ := by ra
example : (a∗)⁺ = a∗ := by ra_simpl
example : a⁺⁺ = a⁺ := by ra_normalise

theorem remaining (h : a * a∗ = b) : a⁺ * 1 = b := by
  ra_normalise
  guard_target =ₛ a * a∗ = b
  exact h

example (h : a * a∗ = b) : 1 * a⁺ = b := by
  ra_simpl
  guard_target =ₛ a * a∗ = b
  exact h

example (h : a = b) : True := by
  fail_if_success have : a⁺ = b⁺ := by ra
  have _ := h
  trivial

set_option linter.style.multiGoal false in
example : (0 : K)⁺ = 0 ∧ True := by
  constructor
  ra
  trivial

set_option linter.style.multiGoal false in
example : (1 : K)⁺ = 1 ∧ True := by
  constructor
  ra_simpl
  trivial

set_option linter.style.multiGoal false in
example : a⁺⁺ = a⁺ ∧ True := by
  constructor
  ra_normalise
  trivial
end Converse

section Tests
variable {T K : Type u} [BooleanAlgebra T] [KleeneAlgebra K] [KAT T K] (b : T) (p : K)

theorem hoare_plus (h : KAT.HoareTriple b p b) : KAT.HoareTriple b p⁺ b := by hkat

theorem plus_hypothesis (h : KAT.HoareTriple b p⁺ b) : KAT.HoareTriple b p b := by hkat

example (h : p⁺ = 0) : p = 0 := by hkat
example : (⌜b⌝ * p)⁺ = ⌜b⌝ * p * (⌜b⌝ * p)∗ := by kat

set_option linter.style.multiGoal false in
example (h : KAT.HoareTriple b p⁺ b) : KAT.HoareTriple b p b ∧ True := by
  constructor
  hkat
  trivial
end Tests

section Typed
variable {C : Type u} [Category.{v} C] [KleeneCategory C] {X Y : C}
  (f : X ⟶ X) (g : X ⟶ Y) (h : Y ⟶ X)

theorem typed_sliding : g ≫ (h ≫ g)⁺ = (g ≫ h)⁺ ≫ g := by kat
theorem typed_unfold : f⁺ = f ⊔ f ≫ f⁺ := by kat
example : (f⁺)∗ = f∗ := by kat
example : f⁺ ≫ f⁺ ≤ f⁺ := by kat
example (k : X ⟶ Y) (hfg : f ≫ g ≤ k) (hfk : f ≫ k ≤ k) : f⁺ ≫ g ≤ k :=
  KleeneCategory.kplus_comp_le hfg hfk
example (k : Y ⟶ X) (hhf : h ≫ f ≤ k) (hkf : k ≫ f ≤ k) : h ≫ f⁺ ≤ k :=
  KleeneCategory.comp_kplus_le hhf hkf
example (e : Y ⟶ Y) (he : f ≫ g = g ≫ e) : f⁺ ≫ g = g ≫ e⁺ :=
  KleeneCategory.kplus_comp_eq_comp_kplus_of_eq he
example (a : End X) : a⁺ = (show X ⟶ X from a)⁺ := KleeneCategory.End.kplus_def a

example : True := by
  fail_if_success have := g⁺
  fail_if_success have : f⁺ = f∗ := by kat
  fail_if_success have : 𝟙 X ≤ f⁺ := by kat
  trivial

example {T : C → Type u} [∀ X, BooleanAlgebra (T X)] [TypedKAT C T]
    (b : T X) (hp : TypedKAT.HoareTriple b f b) : TypedKAT.HoareTriple b f⁺ b := by hkat

theorem typed_plus_hypothesis {T : C → Type u} [∀ X, BooleanAlgebra (T X)] [TypedKAT C T]
    (b : T X) (hp : TypedKAT.HoareTriple b f⁺ b) : TypedKAT.HoareTriple b f b := by hkat

example (hp : f⁺ = ⊥) : f ≫ g = ⊥ := by hkat

variable [KleeneCategoryWithConverse C]

theorem typed_converse : (f⁺)ᵒ = (fᵒ)⁺ := by ra
example : (f⁺)∗ = f∗ := by ra_normalise
example : ∀ (p : X ⟶ X), (p⁺)ᵒ = (pᵒ)⁺ := by ra
example (k : X ⟶ X) (hk : f ≫ f∗ = k) : 𝟙 X ≫ f⁺ = k := by
  ra_simpl
  guard_target =ₛ f ≫ f∗ = k
  exact hk

set_option linter.style.multiGoal false in
example : (f⁺)ᵒ = (fᵒ)⁺ ∧ True := by
  constructor
  ra
  trivial
end Typed

section Models
open scoped SetRel

def step : SetRel ℕ ℕ := {p | p.2 = p.1 + 1}

theorem two_steps : (0, 2) ∈ step⁺ := by
  apply (SetRel.mem_kplus _ _ _).mpr
  exact (Relation.TransGen.single (r := fun x y ↦ (x, y) ∈ step)
    (show (0, 1) ∈ step from rfl)).tail (show (1, 2) ∈ step from rfl)

/-- Strict closure excludes a zero-length path when the relation has no cycles. -/
theorem no_zero_steps : (0, 0) ∉ step⁺ := by
  rw [SetRel.mem_kplus]
  intro h
  have positive : ∀ {a b}, Relation.TransGen (fun x y ↦ (x, y) ∈ step) a b → a < b := by
    intro a b h
    induction h with
    | single h =>
      change _ = _ + 1 at h
      omega
    | tail _ h ih =>
      change _ = _ + 1 at h
      omega
  exact (Nat.lt_irrefl 0) (positive h)

example : (0, 0) ∈ step∗ := Relation.ReflTransGen.refl
example (R : SetRel ℕ ℕ) : star (R⁺) = (star R)⁺ := by ra

private def numbers : RelCat := ℕ
private def flags : RelCat := Bool

example (G : numbers ⟶ flags) (H : flags ⟶ numbers) :
    G ≫ (H ≫ G)⁺ = (G ≫ H)⁺ ≫ G := by kat
example (R : numbers ⟶ numbers) (x y : ℕ) :
    (x, y) ∈ (R⁺).rel ↔ Relation.TransGen (fun a b ↦ (a, b) ∈ R.rel) x y :=
  RelCat.mem_kplus R x y

example {K : Type u} [KleeneAlgebra K]
    (A : (⟨2⟩ : Matrix.Mat K) ⟶ ⟨3⟩) (B : (⟨3⟩ : Matrix.Mat K) ⟶ ⟨2⟩) :
    A ≫ (B ≫ A)⁺ = (A ≫ B)⁺ ≫ A := by kat

theorem matrix_paths {K : Type u} [KleeneAlgebra K] (r : Fin 3 → Fin 3 → Prop) :
    (Matrix.ofRel K r)⁺ = Matrix.ofRel K (Relation.TransGen r) := Matrix.ofRel_kplus r

example {K : Type u} [KleeneAlgebra K] : (0 : Matrix (Fin 0) (Fin 0) K)⁺ = 0 := by ka
example {K : Type u} [KleeneAlgebra K] (A : Matrix (Fin 2) (Fin 2) K) : A⁺⁺ = A⁺ := by ka
example {K : Type u} [KleeneAlgebra K] [StarRing K] (A : Matrix (Fin 2) (Fin 2) K) :
    star (A⁺) = (star A)⁺ := by ra
end Models
end IterationExamples
