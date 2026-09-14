import Mathlib.Algebra.Order.Kleene
import Mathlib.Order.Bounds.Basic

/-!
# Derived laws of Kleene algebra

Mathlib's `KleeneAlgebra` (in `Mathlib.Algebra.Order.Kleene`) provides Kozen's axioms together
with a handful of consequences (`kstar_mono`, `kstar_idem`, `kstar_mul_kstar`,
`one_add_mul_kstar`, `pow_le_kstar`, ...).  This file collects the standard derived laws that
one needs when actually *using* Kleene algebra:

* least-(pre)fixpoint characterisations of `a∗ * b` and `b * a∗`
  (`isLeast_kstar_mul`, `isLeast_mul_kstar`, `kstar_mul_fixpoint`, `mul_kstar_fixpoint`);
* `a∗ * a = a * a∗` (`kstar_mul_comm`);
* the *sliding* rule `a * (b * a)∗ = (a * b)∗ * a` (`mul_kstar_eq_kstar_mul`);
* the *denesting* rules `(a + b)∗ = a∗ * (b * a∗)∗ = (a∗ * b)∗ * a∗` (`kstar_add`, `kstar_add'`);
* the *bisimulation* rules `a * x ≤ x * b → a∗ * x ≤ x * b∗` and friends
  (`kstar_mul_le_mul_kstar_of_le`, `mul_kstar_le_kstar_mul_of_le`, `kstar_mul_eq_mul_kstar_of_eq`);
* `(a + b)∗ = a∗ * b∗` when `b * a ≤ a * b` (`kstar_add_of_mul_le_mul`).

Everything is stated for an arbitrary `[KleeneAlgebra K]` and lives in the `KleeneAlgebra`
namespace, so that it cannot clash with future additions to Mathlib's root namespace.

## References

* [D. Kozen, *A completeness theorem for Kleene algebras and the algebra of regular events*]
* [D. Pous, *Kleene Algebra with Tests and Coq tools for while programs*]
-/

open scoped Computability

namespace KleeneAlgebra

variable {K : Type*} [KleeneAlgebra K] {a b c x : K}

/-! ### Basic order facts -/

theorem le_kstar_mul : b ≤ a∗ * b := le_mul_of_one_le_left' one_le_kstar

theorem le_mul_kstar : b ≤ b * a∗ := le_mul_of_one_le_right' one_le_kstar

theorem mul_kstar_mul_le_kstar_mul : a * (a∗ * b) ≤ a∗ * b := by
  rw [← mul_assoc]
  exact mul_le_mul_left mul_kstar_le_kstar _

theorem mul_kstar_mul_le_mul_kstar : b * a∗ * a ≤ b * a∗ := by
  rw [mul_assoc]
  exact mul_le_mul_right kstar_mul_le_kstar _

theorem kstar_add_le : a∗ + b∗ ≤ (a + b)∗ :=
  add_le (kstar_mono le_self_add) (kstar_mono le_add_self)

theorem kstar_pow_le (n : ℕ) : (a ^ n)∗ ≤ a∗ :=
  (kstar_mono pow_le_kstar).trans (kstar_idem a).le

/-! ### Star as a least (pre)fixpoint -/

/-- `a∗ * b` is the least solution `x` of `a * x + b ≤ x`. -/
theorem isLeast_kstar_mul (a b : K) : IsLeast {x | a * x + b ≤ x} (a∗ * b) :=
  ⟨add_le mul_kstar_mul_le_kstar_mul le_kstar_mul,
    fun _ (hx : a * _ + b ≤ _) ↦ kstar_mul_le (add_le_iff.1 hx).2 (add_le_iff.1 hx).1⟩

/-- `b * a∗` is the least solution `x` of `x * a + b ≤ x`. -/
theorem isLeast_mul_kstar (a b : K) : IsLeast {x | x * a + b ≤ x} (b * a∗) :=
  ⟨add_le mul_kstar_mul_le_mul_kstar le_mul_kstar,
    fun _ (hx : _ * a + b ≤ _) ↦ mul_kstar_le (add_le_iff.1 hx).2 (add_le_iff.1 hx).1⟩

/-- `a∗ * b` is a fixpoint of `x ↦ a * x + b`. -/
theorem kstar_mul_fixpoint (a b : K) : a * (a∗ * b) + b = a∗ * b :=
  calc a * (a∗ * b) + b = (a * a∗ + 1) * b := by rw [add_mul, one_mul, mul_assoc]
    _ = a∗ * b := by rw [add_comm, one_add_mul_kstar]

/-- `b * a∗` is a fixpoint of `x ↦ x * a + b`. -/
theorem mul_kstar_fixpoint (a b : K) : b * a∗ * a + b = b * a∗ :=
  calc b * a∗ * a + b = b * (a∗ * a + 1) := by rw [mul_add, mul_one, mul_assoc]
    _ = b * a∗ := by rw [add_comm, one_add_kstar_mul]

/-! ### Commutation of `a` and `a∗` -/

theorem kstar_mul_le_mul_kstar : a∗ * a ≤ a * a∗ :=
  calc a∗ * a ≤ a∗ * (a * a∗) := mul_le_mul_right le_mul_kstar _
    _ ≤ a * a∗ := kstar_mul_le_self (mul_le_mul_right mul_kstar_le_kstar _)

theorem mul_kstar_le_kstar_mul : a * a∗ ≤ a∗ * a :=
  calc a * a∗ ≤ a∗ * a * a∗ := mul_le_mul_left le_kstar_mul _
    _ ≤ a∗ * a := mul_kstar_le_self (mul_le_mul_left kstar_mul_le_kstar _)

theorem kstar_mul_comm (a : K) : a∗ * a = a * a∗ :=
  kstar_mul_le_mul_kstar.antisymm mul_kstar_le_kstar_mul

/-! ### Sliding and denesting -/

/-- The **sliding rule**: `a (b a)∗ = (a b)∗ a`. -/
theorem mul_kstar_eq_kstar_mul (a b : K) : a * (b * a)∗ = (a * b)∗ * a := by
  apply le_antisymm
  · refine mul_kstar_le le_kstar_mul ?_
    calc (a * b)∗ * a * (b * a) = (a * b)∗ * (a * b) * a := by simp only [mul_assoc]
      _ ≤ (a * b)∗ * a := mul_le_mul_left kstar_mul_le_kstar _
  · refine kstar_mul_le le_mul_kstar ?_
    calc a * b * (a * (b * a)∗) = a * (b * a * (b * a)∗) := by simp only [mul_assoc]
      _ ≤ a * (b * a)∗ := mul_le_mul_right mul_kstar_le_kstar _

/-- The **denesting rule**: `(a + b)∗ = a∗ (b a∗)∗`. -/
theorem kstar_add (a b : K) : (a + b)∗ = a∗ * (b * a∗)∗ := by
  apply le_antisymm
  · refine kstar_le_of_mul_le_right (Left.one_le_mul one_le_kstar one_le_kstar) ?_
    rw [add_mul]
    refine add_le ?_ ?_
    · rw [← mul_assoc]
      exact mul_le_mul_left mul_kstar_le_kstar _
    · rw [← mul_assoc]
      exact mul_kstar_le_kstar.trans le_kstar_mul
  · have ha : a∗ ≤ (a + b)∗ := kstar_mono le_self_add
    have hb : (b * a∗)∗ ≤ (a + b)∗ :=
      calc (b * a∗)∗ ≤ ((a + b)∗ * (a + b)∗)∗ :=
            kstar_mono (mul_le_mul' (le_kstar.trans' le_add_self) ha)
        _ = (a + b)∗ := by rw [kstar_mul_kstar, kstar_idem]
    calc a∗ * (b * a∗)∗ ≤ (a + b)∗ * (a + b)∗ := mul_le_mul' ha hb
      _ = (a + b)∗ := kstar_mul_kstar _

/-- The other **denesting rule**: `(a + b)∗ = (a∗ b)∗ a∗`. -/
theorem kstar_add' (a b : K) : (a + b)∗ = (a∗ * b)∗ * a∗ := by
  rw [kstar_add, mul_kstar_eq_kstar_mul]

theorem kstar_one_add (a : K) : (1 + a)∗ = a∗ :=
  le_antisymm
    (kstar_le_of_mul_le_left one_le_kstar
      (by rw [mul_add, mul_one]; exact add_le le_rfl kstar_mul_le_kstar))
    (kstar_mono le_add_self)

theorem kstar_add_one (a : K) : (a + 1)∗ = a∗ := by rw [add_comm, kstar_one_add]

theorem kstar_kstar_mul_kstar (a b : K) : (a∗ * b∗)∗ = (a + b)∗ := by
  apply le_antisymm
  · calc (a∗ * b∗)∗ ≤ ((a + b)∗ * (a + b)∗)∗ :=
          kstar_mono (mul_le_mul' (kstar_mono le_self_add) (kstar_mono le_add_self))
      _ = (a + b)∗ := by rw [kstar_mul_kstar, kstar_idem]
  · refine kstar_mono (add_le ?_ ?_)
    · exact le_kstar.trans le_mul_kstar
    · exact le_kstar.trans le_kstar_mul

/-! ### Bisimulation rules -/

theorem kstar_mul_le_mul_kstar_of_le (h : a * x ≤ x * b) : a∗ * x ≤ x * b∗ :=
  kstar_mul_le le_mul_kstar <|
    calc a * (x * b∗) = a * x * b∗ := (mul_assoc _ _ _).symm
      _ ≤ x * b * b∗ := mul_le_mul_left h _
      _ = x * (b * b∗) := mul_assoc _ _ _
      _ ≤ x * b∗ := mul_le_mul_right mul_kstar_le_kstar _

theorem mul_kstar_le_kstar_mul_of_le (h : x * a ≤ b * x) : x * a∗ ≤ b∗ * x :=
  mul_kstar_le le_kstar_mul <|
    calc b∗ * x * a = b∗ * (x * a) := mul_assoc _ _ _
      _ ≤ b∗ * (b * x) := mul_le_mul_right h _
      _ = b∗ * b * x := (mul_assoc _ _ _).symm
      _ ≤ b∗ * x := mul_le_mul_left kstar_mul_le_kstar _

/-- **Bisimulation**: if `x` intertwines `a` and `b`, it intertwines `a∗` and `b∗`. -/
theorem kstar_mul_eq_mul_kstar_of_eq (h : a * x = x * b) : a∗ * x = x * b∗ :=
  (kstar_mul_le_mul_kstar_of_le h.le).antisymm (mul_kstar_le_kstar_mul_of_le h.ge)

/-- If `b` "commutes past" `a`, then `(a + b)∗ = a∗ b∗`. -/
theorem kstar_add_of_mul_le_mul (h : b * a ≤ a * b) : (a + b)∗ = a∗ * b∗ := by
  apply le_antisymm
  · refine kstar_le_of_mul_le_right (Left.one_le_mul one_le_kstar one_le_kstar) ?_
    rw [add_mul]
    refine add_le ?_ ?_
    · rw [← mul_assoc]
      exact mul_le_mul_left mul_kstar_le_kstar _
    · calc b * (a∗ * b∗) = b * a∗ * b∗ := (mul_assoc _ _ _).symm
        _ ≤ a∗ * b * b∗ := mul_le_mul_left (mul_kstar_le_kstar_mul_of_le h) _
        _ = a∗ * (b * b∗) := mul_assoc _ _ _
        _ ≤ a∗ * b∗ := mul_le_mul_right mul_kstar_le_kstar _
  · exact (mul_le_mul' (kstar_mono le_self_add) (kstar_mono le_add_self)).trans
      (kstar_mul_kstar _).le

/-- If `a` and `b` commute, then `(a + b)∗ = a∗ b∗`. -/
theorem kstar_add_of_comm (h : a * b = b * a) : (a + b)∗ = a∗ * b∗ :=
  kstar_add_of_mul_le_mul h.ge

end KleeneAlgebra
