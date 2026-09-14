import RelationAlgebra.Kleene.Basic
import RelationAlgebra.KAT.Defs

/-!
# Basic theory of Kleene algebra with tests

We derive the basic laws about tests (tests are below `1`, idempotent, commute with each other,
`⌜b⌝ * ⌜bᶜ⌝ = 0`, `⌜b⌝ + ⌜bᶜ⌝ = 1`, ...) and define the usual **guarded commands**

* `KAT.ifThenElse b p q = ⌜b⌝ * p + ⌜bᶜ⌝ * q`,
* `KAT.whileDo b p = (⌜b⌝ * p)∗ * ⌜bᶜ⌝`,

together with their basic equational laws.
-/

open scoped Computability KAT

namespace KAT

variable {T K : Type*} [BooleanAlgebra T] [KleeneAlgebra K] [KAT T K] {a b c : T} {p q : K}

/-! ### Tests -/

theorem test_mono : Monotone (@test T K _ _ _) := by
  intro a b h
  have this : (test (a ⊔ b) : K) = test b := by rw [sup_eq_right.2 h]
  rw [test_sup] at this
  exact add_eq_right_iff_le.1 this

theorem test_le_test (h : a ≤ b) : (⌜a⌝ : K) ≤ ⌜b⌝ := test_mono h

@[simp] theorem test_le_one : (⌜a⌝ : K) ≤ 1 := by
  have h : (⌜a⌝ : K) ≤ ⌜(⊤ : T)⌝ := test_mono le_top
  rwa [test_top] at h

@[simp] theorem test_mul_self (a : T) : (⌜a⌝ : K) * ⌜a⌝ = ⌜a⌝ := by rw [← test_inf, inf_idem]

theorem test_mul_comm (a b : T) : (⌜a⌝ : K) * ⌜b⌝ = ⌜b⌝ * ⌜a⌝ := by
  rw [← test_inf, ← test_inf, inf_comm]

theorem test_mul_left_comm (a b : T) (p : K) : ⌜a⌝ * (⌜b⌝ * p) = ⌜b⌝ * (⌜a⌝ * p) := by
  rw [← mul_assoc, test_mul_comm, mul_assoc]

theorem test_mul_right_comm (p : K) (a b : T) : p * ⌜a⌝ * ⌜b⌝ = p * ⌜b⌝ * ⌜a⌝ := by
  rw [mul_assoc, test_mul_comm, mul_assoc]

theorem test_add_comm (a b : T) : (⌜a⌝ : K) + ⌜b⌝ = ⌜b⌝ + ⌜a⌝ := add_comm _ _

@[simp] theorem test_mul_compl (a : T) : (⌜a⌝ : K) * ⌜aᶜ⌝ = 0 := by
  rw [← test_inf, inf_compl_eq_bot, test_bot]

@[simp] theorem test_compl_mul (a : T) : (⌜aᶜ⌝ : K) * ⌜a⌝ = 0 := by
  rw [← test_inf, compl_inf_eq_bot, test_bot]

@[simp] theorem test_add_compl (a : T) : (⌜a⌝ : K) + ⌜aᶜ⌝ = 1 := by
  rw [← test_sup, sup_compl_eq_top, test_top]

@[simp] theorem test_compl_add (a : T) : (⌜aᶜ⌝ : K) + ⌜a⌝ = 1 := by
  rw [← test_sup, compl_sup_eq_top, test_top]

theorem test_himp (a b : T) : (⌜a ⇨ b⌝ : K) = ⌜aᶜ⌝ + ⌜b⌝ := by
  rw [himp_eq, test_sup, add_comm]

theorem test_sdiff (a b : T) : (⌜a \ b⌝ : K) = ⌜a⌝ * ⌜bᶜ⌝ := by
  rw [sdiff_eq, test_inf]

@[simp] theorem test_kstar (a : T) : (⌜a⌝ : K)∗ = 1 := kstar_eq_one.2 test_le_one

theorem test_mul_le (a : T) (p : K) : ⌜a⌝ * p ≤ p := mul_le_of_le_one_left' test_le_one

theorem mul_test_le (p : K) (a : T) : p * ⌜a⌝ ≤ p := mul_le_of_le_one_right' test_le_one

theorem test_mul_add_test_compl_mul (a : T) (p : K) : ⌜a⌝ * p + ⌜aᶜ⌝ * p = p := by
  rw [← add_mul, test_add_compl, one_mul]

theorem mul_test_add_mul_test_compl (p : K) (a : T) : p * ⌜a⌝ + p * ⌜aᶜ⌝ = p := by
  rw [← mul_add, test_add_compl, mul_one]

theorem test_mul_test_mul (a b : T) (p : K) : ⌜a⌝ * (⌜b⌝ * p) = ⌜a ⊓ b⌝ * p := by
  rw [test_inf, mul_assoc]

theorem test_mul_le_test_mul (h : a ≤ b) (p : K) : ⌜a⌝ * p ≤ ⌜b⌝ * p :=
  mul_le_mul_left (test_le_test h) _

theorem mul_test_le_mul_test (p : K) (h : a ≤ b) : p * ⌜a⌝ ≤ p * ⌜b⌝ :=
  mul_le_mul_right (test_le_test h) _

/-! ### Guarded commands -/

/-- `if b then p else q`, encoded as `⌜b⌝ * p + ⌜bᶜ⌝ * q`. -/
def ifThenElse (b : T) (p q : K) : K := ⌜b⌝ * p + ⌜bᶜ⌝ * q

/-- `while b do p`, encoded as `(⌜b⌝ * p)∗ * ⌜bᶜ⌝`. -/
def whileDo (b : T) (p : K) : K := (⌜b⌝ * p)∗ * ⌜bᶜ⌝

theorem ifThenElse_def (b : T) (p q : K) : ifThenElse b p q = ⌜b⌝ * p + ⌜bᶜ⌝ * q := rfl

theorem whileDo_def (b : T) (p : K) : whileDo b p = (⌜b⌝ * p)∗ * ⌜bᶜ⌝ := rfl

@[simp] theorem ifThenElse_self (b : T) (p : K) : ifThenElse b p p = p :=
  test_mul_add_test_compl_mul b p

theorem ifThenElse_compl (b : T) (p q : K) : ifThenElse bᶜ p q = ifThenElse b q p := by
  simp only [ifThenElse, compl_compl, add_comm]

@[simp] theorem ifThenElse_top (p q : K) : ifThenElse (⊤ : T) p q = p := by
  simp [ifThenElse]

@[simp] theorem ifThenElse_bot (p q : K) : ifThenElse (⊥ : T) p q = q := by
  simp [ifThenElse]

theorem test_mul_ifThenElse (b : T) (p q : K) : ⌜b⌝ * ifThenElse b p q = ⌜b⌝ * p := by
  simp only [ifThenElse, mul_add, ← mul_assoc, test_mul_self, test_mul_compl, zero_mul, add_zero]

theorem test_compl_mul_ifThenElse (b : T) (p q : K) : ⌜bᶜ⌝ * ifThenElse b p q = ⌜bᶜ⌝ * q := by
  simp only [ifThenElse, mul_add, ← mul_assoc, test_mul_self, test_compl_mul, zero_mul, zero_add]

theorem ifThenElse_mul (b : T) (p q r : K) :
    ifThenElse b p q * r = ifThenElse b (p * r) (q * r) := by
  simp only [ifThenElse, add_mul, mul_assoc]

/-- Unfolding a `while` loop once. -/
theorem whileDo_unfold (b : T) (p : K) : whileDo b p = ifThenElse b (p * whileDo b p) 1 := by
  unfold whileDo ifThenElse
  conv_lhs => rw [← one_add_mul_kstar]
  rw [add_mul, one_mul, mul_one, add_comm]
  simp only [mul_assoc]

@[simp] theorem whileDo_mul_test_compl (b : T) (p : K) : whileDo b p * ⌜bᶜ⌝ = whileDo b p := by
  rw [whileDo, mul_assoc, test_mul_self]

@[simp] theorem test_compl_mul_whileDo (b : T) (p : K) : ⌜bᶜ⌝ * whileDo b p = ⌜bᶜ⌝ := by
  rw [whileDo_unfold, test_compl_mul_ifThenElse, mul_one]

@[simp] theorem whileDo_bot (p : K) : whileDo (⊥ : T) p = 1 := by
  simp [whileDo]

end KAT
