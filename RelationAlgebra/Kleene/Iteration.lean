import RelationAlgebra.Converse

/-!
# Strict iteration

`a⁺` means one or more steps and is defined as `a * a∗`. It adds no axiom to
`KleeneAlgebra`. Open `Computability` for the notation, as for `a∗`.

The laws follow Damien Pous' strict-iteration development in
[`kleene.v`](https://github.com/damien-pous/relation-algebra/blob/2d2af3631929399bbac56f57b3e15302d8697e1c/theories/kleene.v).
Our assumptions are Kleene-algebra assumptions, rather than upstream's weaker levels.
`KPlus` only supplies notation; the canonical instance is derived from the existing star.
-/

/-- The operation of strict iteration, with notation `a⁺` in the `Computability` scope. -/
class KPlus (K : Type*) where
  kplus : K → K

scoped[Computability] postfix:max "⁺" => KPlus.kplus

open scoped Computability

namespace KleeneAlgebra

variable {K : Type*} [KleeneAlgebra K] {a b c x : K}

/-- The canonical strict iteration on a Kleene algebra. -/
instance (priority := 100) instKPlus : KPlus K := ⟨fun a ↦ a * a∗⟩

theorem kplus_eq_mul_kstar (a : K) : a⁺ = a * a∗ := rfl

theorem kplus_eq_kstar_mul (a : K) : a⁺ = a∗ * a := (kstar_mul_comm a).symm

theorem le_kplus (a : K) : a ≤ a⁺ := le_mul_kstar

theorem kplus_le_kstar (a : K) : a⁺ ≤ a∗ := mul_kstar_le_kstar

@[gcongr] theorem kplus_mono (h : a ≤ b) : a⁺ ≤ b⁺ := mul_le_mul' h (kstar_mono h)

@[simp] theorem kplus_zero : (0 : K)⁺ = 0 := by simp only [kplus_eq_mul_kstar, zero_mul]

@[simp] theorem kplus_one : (1 : K)⁺ = 1 := by simp only [kplus_eq_mul_kstar, kstar_one, one_mul]

@[simp] theorem kplus_top [OrderTop K] : (⊤ : K)⁺ = ⊤ := le_antisymm le_top (le_kplus _)

theorem one_add_kplus (a : K) : 1 + a⁺ = a∗ := one_add_mul_kstar

/-- Strict left unfolding includes a first step, not an identity step. -/
theorem kplus_unfold_left (a : K) : a + a * a⁺ = a⁺ := by
  simpa only [kplus_eq_kstar_mul, add_comm] using kstar_mul_fixpoint a a

theorem kplus_unfold_right (a : K) : a + a⁺ * a = a⁺ := by
  simpa only [kplus_eq_mul_kstar, add_comm] using mul_kstar_fixpoint a a

theorem mul_kplus_le_kplus (a : K) : a * a⁺ ≤ a⁺ :=
  le_add_self.trans (kplus_unfold_left a).le

theorem kplus_mul_le_kplus (a : K) : a⁺ * a ≤ a⁺ :=
  le_add_self.trans (kplus_unfold_right a).le

/-- Left induction starts with `a * b ≤ c`, allowing a mandatory first step. -/
theorem kplus_mul_le (hab : a * b ≤ c) (hac : a * c ≤ c) : a⁺ * b ≤ c := by
  rw [kplus_eq_kstar_mul, mul_assoc]
  exact kstar_mul_le hab hac

theorem mul_kplus_le (hba : b * a ≤ c) (hca : c * a ≤ c) : b * a⁺ ≤ c := by
  rw [kplus_eq_mul_kstar, ← mul_assoc]
  exact mul_kstar_le hba hca

theorem kplus_le_of_mul_le_right (hab : a ≤ b) (h : a * b ≤ b) : a⁺ ≤ b := by
  rw [kplus_eq_kstar_mul]
  exact kstar_mul_le hab h

theorem kplus_le_of_mul_le_left (hab : a ≤ b) (h : b * a ≤ b) : a⁺ ≤ b :=
  mul_kstar_le hab h

/-- Transitivity of strict iteration need not be equality. -/
theorem kplus_mul_kplus_le (a : K) : a⁺ * a⁺ ≤ a⁺ :=
  kplus_mul_le (mul_kplus_le_kplus a) (mul_kplus_le_kplus a)

/-- `a⁺` is the least multiplicatively transitive element above `a`. -/
theorem isLeast_kplus (a : K) : IsLeast {b | a ≤ b ∧ b * b ≤ b} a⁺ :=
  ⟨⟨le_kplus a, kplus_mul_kplus_le a⟩, fun _ h ↦
    kplus_le_of_mul_le_right h.1 ((mul_le_mul_left h.1 _).trans h.2)⟩

@[simp] theorem kplus_idem (a : K) : a⁺⁺ = a⁺ :=
  (kplus_le_of_mul_le_right le_rfl (kplus_mul_kplus_le a)).antisymm (le_kplus _)

@[simp] theorem kstar_kplus (a : K) : (a⁺)∗ = a∗ :=
  ((kstar_mono (kplus_le_kstar a)).trans (kstar_idem a).le).antisymm
    (kstar_mono (le_kplus a))

@[simp] theorem kplus_kstar (a : K) : (a∗)⁺ = a∗ := by
  rw [kplus_eq_mul_kstar, kstar_idem, kstar_mul_kstar]

theorem kplus_mul_kstar (a : K) : a⁺ * a∗ = a⁺ := by
  rw [kplus_eq_mul_kstar, mul_assoc, kstar_mul_kstar]

theorem kstar_mul_kplus (a : K) : a∗ * a⁺ = a⁺ := by
  rw [kplus_eq_kstar_mul, ← mul_assoc, kstar_mul_kstar]

theorem kplus_mul_le_mul_kplus_of_le (h : a * x ≤ x * b) : a⁺ * x ≤ x * b⁺ := by
  calc a⁺ * x = a * (a∗ * x) := mul_assoc _ _ _
    _ ≤ a * (x * b∗) := mul_le_mul_right (kstar_mul_le_mul_kstar_of_le h) _
    _ = (a * x) * b∗ := (mul_assoc _ _ _).symm
    _ ≤ (x * b) * b∗ := mul_le_mul_left h _
    _ = x * b⁺ := mul_assoc _ _ _

theorem mul_kplus_le_kplus_mul_of_le (h : x * a ≤ b * x) : x * a⁺ ≤ b⁺ * x := by
  calc x * a⁺ = (x * a) * a∗ := (mul_assoc _ _ _).symm
    _ ≤ (b * x) * a∗ := mul_le_mul_left h _
    _ = b * (x * a∗) := mul_assoc _ _ _
    _ ≤ b * (b∗ * x) := mul_le_mul_right (mul_kstar_le_kstar_mul_of_le h) _
    _ = b⁺ * x := (mul_assoc _ _ _).symm

theorem kplus_mul_eq_mul_kplus_of_eq (h : a * x = x * b) : a⁺ * x = x * b⁺ :=
  (kplus_mul_le_mul_kplus_of_le h.le).antisymm (mul_kplus_le_kplus_mul_of_le h.ge)

/-- Strict sliding. -/
theorem mul_kplus_eq_kplus_mul (a b : K) : a * (b * a)⁺ = (a * b)⁺ * a :=
  (kplus_mul_eq_mul_kplus_of_eq (mul_assoc a b a)).symm

theorem kplus_add_kplus (a b : K) : (a⁺ + b⁺)⁺ = (a + b)⁺ := by
  apply le_antisymm
  · apply (isLeast_kplus _).2
    exact ⟨add_le (kplus_mono le_self_add) (kplus_mono le_add_self), kplus_mul_kplus_le _⟩
  · exact kplus_mono (add_le_add (le_kplus a) (le_kplus b))

/-- Strict iteration through an idempotent boundary (`itr_aea` upstream). -/
theorem kplus_mul_of_idempotent (a e : K) (ha : a * a = a) :
    (a * e)⁺ * a = (a * e * a)⁺ := by
  symm
  calc (a * e * a)⁺ = (a * e) * (a * ((a * e) * a)∗) := mul_assoc _ _ _
    _ = (a * e) * ((a * (a * e))∗ * a) := by rw [mul_kstar_eq_kstar_mul]
    _ = (a * e) * ((a * e)∗ * a) := by rw [← mul_assoc a a e, ha]
    _ = (a * e)⁺ * a := (mul_assoc _ _ _).symm

@[simp] theorem star_kplus [StarRing K] (a : K) : star (a⁺) = (star a)⁺ := by
  rw [kplus_eq_mul_kstar, star_mul, star_kstar, ← kplus_eq_kstar_mul]

end KleeneAlgebra

namespace SetRel

open scoped SetRel

/-- Unlike star, strict relational iteration requires a nonempty path. -/
@[simp] theorem mem_kplus {α : Type*} (R : SetRel α α) (a b : α) :
    (a, b) ∈ R⁺ ↔ Relation.TransGen (fun x y ↦ (x, y) ∈ R) a b :=
  (Relation.TransGen.head'_iff (r := fun x y ↦ (x, y) ∈ R)).symm

theorem kplus_def {α : Type*} (R : SetRel α α) :
    R⁺ = {p | Relation.TransGen (fun x y ↦ (x, y) ∈ R) p.1 p.2} := by
  ext ⟨a, b⟩
  exact mem_kplus R a b

end SetRel
