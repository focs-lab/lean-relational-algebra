import Mathlib.Algebra.Order.Kleene
import Mathlib.Algebra.Order.Quantale

/-!
# Kleene algebras from quantales

A (unital) *quantale* is a monoid on a complete lattice whose multiplication distributes over
arbitrary joins.  Mathlib packages this as `[Monoid K] [CompleteLattice K] [IsQuantale K]`.

Every such structure is a Kleene algebra: addition is join, zero is bottom, and the star is the
"star-continuous" one, `a∗ = ⨆ n, a ^ n`.  This is the abstract reason why relations and
languages are Kleene algebras.  We provide the construction as reducible non-instances
(`IdemSemiring.ofQuantale`, `KleeneAlgebra.ofQuantale`), in the same spirit as Mathlib's
`IdemSemiring.ofSemiring`, so that concrete models may use them to build their instances.
-/

open scoped Computability

variable (K : Type*) [Monoid K] [CompleteLattice K] [IsQuantale K]

-- See note [reducible non-instances]
/-- A unital quantale is an idempotent semiring with `+ = ⊔` and `0 = ⊥`. -/
abbrev IdemSemiring.ofQuantale : IdemSemiring K where
  __ : Monoid K := inferInstance
  __ : SemilatticeSup K := inferInstance
  __ : OrderBot K := inferInstance
  add := (· ⊔ ·)
  add_assoc := sup_assoc
  zero := ⊥
  zero_add := bot_sup_eq
  add_zero := sup_bot_eq
  add_comm := sup_comm
  nsmul := @nsmulRec K ⟨⊥⟩ ⟨(· ⊔ ·)⟩
  left_distrib _ _ _ := Quantale.mul_sup_distrib
  right_distrib _ _ _ := Quantale.sup_mul_distrib
  zero_mul _ := Quantale.bot_mul
  mul_zero _ := Quantale.mul_bot
  add_eq_sup _ _ := rfl

-- See note [reducible non-instances]
/-- A unital quantale is a Kleene algebra with `a∗ = ⨆ n, a ^ n`. -/
abbrev KleeneAlgebra.ofQuantale : KleeneAlgebra K where
  __ := IdemSemiring.ofQuantale K
  kstar a := ⨆ n : ℕ, a ^ n
  one_le_kstar a := le_iSup_of_le 0 (pow_zero a).ge
  mul_kstar_le_kstar a := by
    rw [Quantale.mul_iSup_distrib]
    exact iSup_le fun n ↦ le_iSup_of_le (n + 1) (pow_succ' a n).ge
  kstar_mul_le_kstar a := by
    rw [Quantale.iSup_mul_distrib]
    exact iSup_le fun n ↦ le_iSup_of_le (n + 1) (pow_succ a n).ge
  mul_kstar_le_self a b h := by
    rw [Quantale.mul_iSup_distrib]
    refine iSup_le fun n ↦ ?_
    induction n with
    | zero => simp
    | succ n ih =>
      calc b * a ^ (n + 1) = b * a ^ n * a := by rw [pow_succ, mul_assoc]
        _ ≤ b * a := mul_le_mul_left ih _
        _ ≤ b := h
  kstar_mul_le_self a b h := by
    rw [Quantale.iSup_mul_distrib]
    refine iSup_le fun n ↦ ?_
    induction n with
    | zero => simp
    | succ n ih =>
      calc a ^ (n + 1) * b = a * (a ^ n * b) := by rw [pow_succ', mul_assoc]
        _ ≤ a * b := mul_le_mul_right ih _
        _ ≤ b := h

theorem KleeneAlgebra.ofQuantale_kstar (a : K) :
    (KleeneAlgebra.ofQuantale K).kstar a = ⨆ n : ℕ, a ^ n := rfl
