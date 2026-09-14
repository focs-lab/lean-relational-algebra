import RelationAlgebra.KAT.Basic

/-!
# Hoare logic in Kleene algebra with tests

Following Kozen (*On Hoare logic and Kleene algebra with tests*, 2000), a partial-correctness
Hoare triple `{b} p {c}` is encoded in KAT as the equation

  `⌜b⌝ * p * ⌜cᶜ⌝ = 0`,

i.e. "running `p` from a state satisfying `b` can never end in a state violating `c`".
We prove the equivalent formulations `⌜b⌝ * p ≤ p * ⌜c⌝` and `⌜b⌝ * p = ⌜b⌝ * p * ⌜c⌝`, and
derive the rules of Hoare logic (skip, sequencing, conditional, while, consequence) as
theorems.  Everything holds in an arbitrary KAT, hence in particular in the relational model.
-/

open scoped Computability KAT

namespace KAT

variable {T K : Type*} [BooleanAlgebra T] [KleeneAlgebra K] [KAT T K] {b b' c c' d : T} {p q : K}

/-- The partial-correctness Hoare triple `{b} p {c}`, encoded as `⌜b⌝ * p * ⌜cᶜ⌝ = 0`. -/
def HoareTriple (b : T) (p : K) (c : T) : Prop := ⌜b⌝ * p * ⌜cᶜ⌝ = 0

theorem hoareTriple_def : HoareTriple b p c ↔ ⌜b⌝ * p * ⌜cᶜ⌝ = 0 := Iff.rfl

/-- `{b} p {c}` iff `⌜b⌝ * p ≤ p * ⌜c⌝`. -/
theorem hoareTriple_iff_le : HoareTriple b p c ↔ ⌜b⌝ * p ≤ p * ⌜c⌝ := by
  constructor
  · intro (h : ⌜b⌝ * p * ⌜cᶜ⌝ = 0)
    calc ⌜b⌝ * p = ⌜b⌝ * p * (⌜c⌝ + ⌜cᶜ⌝) := by rw [test_add_compl, mul_one]
      _ = ⌜b⌝ * p * ⌜c⌝ + ⌜b⌝ * p * ⌜cᶜ⌝ := mul_add _ _ _
      _ = ⌜b⌝ * p * ⌜c⌝ := by rw [h, add_zero]
      _ ≤ p * ⌜c⌝ := mul_le_mul_left (test_mul_le _ _) _
  · intro h
    refine le_antisymm ?_ zero_le
    calc ⌜b⌝ * p * ⌜cᶜ⌝ ≤ p * ⌜c⌝ * ⌜cᶜ⌝ := mul_le_mul_left h _
      _ = 0 := by rw [mul_assoc, test_mul_compl, mul_zero]

/-- `{b} p {c}` iff `⌜b⌝ * p = ⌜b⌝ * p * ⌜c⌝`. -/
theorem hoareTriple_iff_eq : HoareTriple b p c ↔ ⌜b⌝ * p = ⌜b⌝ * p * ⌜c⌝ := by
  constructor
  · intro (h : ⌜b⌝ * p * ⌜cᶜ⌝ = 0)
    calc ⌜b⌝ * p = ⌜b⌝ * p * (⌜c⌝ + ⌜cᶜ⌝) := by rw [test_add_compl, mul_one]
      _ = ⌜b⌝ * p * ⌜c⌝ + ⌜b⌝ * p * ⌜cᶜ⌝ := mul_add _ _ _
      _ = ⌜b⌝ * p * ⌜c⌝ := by rw [h, add_zero]
  · intro h
    rw [hoareTriple_iff_le, h, mul_assoc]
    exact test_mul_le _ _

namespace HoareTriple

/-! ### Rules of Hoare logic -/

theorem skip (b : T) : HoareTriple b (1 : K) b := by
  change ⌜b⌝ * 1 * ⌜bᶜ⌝ = 0
  rw [mul_one, test_mul_compl]

theorem zero (b c : T) : HoareTriple b (0 : K) c := by
  change ⌜b⌝ * 0 * ⌜cᶜ⌝ = 0
  rw [mul_zero, zero_mul]

theorem bot (p : K) (c : T) : HoareTriple ⊥ p c := by
  change ⌜⊥⌝ * p * ⌜cᶜ⌝ = 0
  rw [test_bot, zero_mul, zero_mul]

theorem top (b : T) (p : K) : HoareTriple b p ⊤ := by
  change ⌜b⌝ * p * ⌜⊤ᶜ⌝ = 0
  rw [compl_top, test_bot, mul_zero]

/-- `{b} ⌜c⌝ {b ⊓ c}`: running a test as a program asserts it. -/
theorem test (b c : T) : HoareTriple b (⌜c⌝ : K) (b ⊓ c) := by
  change ⌜b⌝ * ⌜c⌝ * ⌜(b ⊓ c)ᶜ⌝ = 0
  rw [← test_inf, ← test_inf, inf_compl_eq_bot, test_bot]

/-- Sequential composition. -/
theorem seq (hp : HoareTriple b p c) (hq : HoareTriple c q d) : HoareTriple b (p * q) d := by
  rw [hoareTriple_iff_le] at hp hq ⊢
  calc ⌜b⌝ * (p * q) = ⌜b⌝ * p * q := (mul_assoc _ _ _).symm
    _ ≤ p * ⌜c⌝ * q := mul_le_mul_left hp _
    _ = p * (⌜c⌝ * q) := mul_assoc _ _ _
    _ ≤ p * (q * ⌜d⌝) := mul_le_mul_right hq _
    _ = p * q * ⌜d⌝ := (mul_assoc _ _ _).symm

/-- Nondeterministic choice. -/
theorem add (hp : HoareTriple b p c) (hq : HoareTriple b q c) : HoareTriple b (p + q) c := by
  have hp' : ⌜b⌝ * p * ⌜cᶜ⌝ = 0 := hp
  have hq' : ⌜b⌝ * q * ⌜cᶜ⌝ = 0 := hq
  change ⌜b⌝ * (p + q) * ⌜cᶜ⌝ = 0
  rw [mul_add, add_mul, hp', hq', add_zero]

/-- Conditional. -/
theorem ifThenElse (hp : HoareTriple (b ⊓ c) p d) (hq : HoareTriple (bᶜ ⊓ c) q d) :
    HoareTriple c (KAT.ifThenElse b p q) d := by
  have hp' : ⌜b ⊓ c⌝ * p * ⌜dᶜ⌝ = 0 := hp
  have hq' : ⌜bᶜ ⊓ c⌝ * q * ⌜dᶜ⌝ = 0 := hq
  rw [test_inf] at hp' hq'
  change ⌜c⌝ * (⌜b⌝ * p + ⌜bᶜ⌝ * q) * ⌜dᶜ⌝ = 0
  simp only [mul_add, add_mul, ← mul_assoc]
  rw [test_mul_comm c b, test_mul_comm c bᶜ, hp', hq', add_zero]

/-- Iteration: an invariant of `p` is an invariant of `p∗`. -/
theorem kstar (h : HoareTriple b p b) : HoareTriple b p∗ b := by
  rw [hoareTriple_iff_le] at h ⊢
  exact KleeneAlgebra.mul_kstar_le_kstar_mul_of_le h

/-- While loop. -/
theorem whileDo (h : HoareTriple (b ⊓ c) p c) : HoareTriple c (KAT.whileDo b p) (bᶜ ⊓ c) := by
  rw [hoareTriple_iff_le] at h ⊢
  rw [test_inf] at h ⊢
  have key : ⌜c⌝ * (⌜b⌝ * p) ≤ ⌜b⌝ * p * ⌜c⌝ := by
    have e : ⌜c⌝ * (⌜b⌝ * p) = ⌜b⌝ * (⌜b⌝ * ⌜c⌝ * p) := by
      rw [← mul_assoc, test_mul_comm c b, ← mul_assoc, ← mul_assoc, test_mul_self]
    rw [e, mul_assoc ⌜b⌝ p]
    exact mul_le_mul_right h _
  calc ⌜c⌝ * KAT.whileDo b p = ⌜c⌝ * (⌜b⌝ * p)∗ * ⌜bᶜ⌝ := (mul_assoc _ _ _).symm
    _ ≤ (⌜b⌝ * p)∗ * ⌜c⌝ * ⌜bᶜ⌝ :=
        mul_le_mul_left (KleeneAlgebra.mul_kstar_le_kstar_mul_of_le key) _
    _ = KAT.whileDo b p * (⌜bᶜ⌝ * ⌜c⌝) := by
        rw [KAT.whileDo, mul_assoc, mul_assoc, test_mul_comm c bᶜ,
          ← mul_assoc ⌜bᶜ⌝ ⌜bᶜ⌝, test_mul_self]

/-- Rule of consequence. -/
theorem consequence (hb : b' ≤ b) (h : HoareTriple b p c) (hc : c ≤ c') :
    HoareTriple b' p c' := by
  rw [hoareTriple_iff_le] at h ⊢
  calc ⌜b'⌝ * p ≤ ⌜b⌝ * p := test_mul_le_test_mul hb _
    _ ≤ p * ⌜c⌝ := h
    _ ≤ p * ⌜c'⌝ := mul_test_le_mul_test _ hc

theorem weaken_pre (hb : b' ≤ b) (h : HoareTriple b p c) : HoareTriple b' p c :=
  consequence hb h le_rfl

theorem strengthen_post (h : HoareTriple b p c) (hc : c ≤ c') : HoareTriple b p c' :=
  consequence le_rfl h hc

/-- `{c} while b do p {bᶜ}`: the loop guard fails on exit. -/
theorem whileDo_exit (b : T) (p : K) : HoareTriple ⊤ (KAT.whileDo b p) bᶜ :=
  (whileDo (top _ _)).strengthen_post inf_le_left

end HoareTriple

end KAT
