import RelationAlgebra.Decide.HKATTactic
import RelationAlgebra.Decide.Tactic

/-! # Algebraic steps in Paterson's flowchart equivalence

The equation numbers refer to Angus and Kozen (2001), §5. These lemmas isolate the
hypotheses needed by each step of Damien Pous's `examples/paterson.v` proof.
-/
open scoped Computability KAT
namespace Paterson.Algebra
variable {T K : Type*} [BooleanAlgebra T] [KleeneAlgebra K] [KAT T K]

/-- Rewrite a pair of adjacent factors in a right-associated product. -/
theorem reassoc {a b c : K} (h : a * b = c) (d : K) : a * (b * d) = c * d := by
  rw [← mul_assoc, h]

/-- Sliding and denesting, with the program fragments treated as opaque actions. -/
theorem denest (u b c d e : K) :
    u * b∗ * c * (d * b∗ * c)∗ * e = u * (b + c * d)∗ * c * e := by kat

/-- Split the four possible outcomes of the two branch tests. -/
theorem split_branches (a b : T) (p q r s : K) (h : ⌜b⌝ * r = r * ⌜b⌝) :
    ⌜aᶜ⌝ * p * q + ⌜a⌝ * r * (⌜bᶜ⌝ + ⌜b⌝ * s) * q =
      ⌜aᶜ ⊓ bᶜ⌝ * p * q + ⌜aᶜ ⊓ b⌝ * p * q +
      ⌜a ⊓ bᶜ⌝ * r * ⌜bᶜ⌝ * q + ⌜a ⊓ b⌝ * r * s * q := by hkat 10000

/-- Move an invariant test through a while loop. -/
theorem test_loop_comm (a b : T) (p : K) (h : ⌜a⌝ * p = p * ⌜a⌝) :
    ⌜a⌝ * (⌜b⌝ * p)∗ = (⌜b⌝ * p)∗ * ⌜a⌝ := by
  symm
  apply KleeneAlgebra.kstar_mul_eq_mul_kstar_of_eq
  hkat

/-- Denest the original flowchart and split its branches (equation 19). -/
theorem step19 (a1 a2 a3 a4 : T) (x1 p41 p11 q214 q311 p13 p22 z2 : K)
    (h1 : ⌜a4⌝ * p13 = p13 * ⌜a4⌝) (h2 : ⌜a4⌝ * p22 = p22 * ⌜a4⌝) :
    x1 * p41 * p11 * q214 * q311 * (⌜a1ᶜ⌝ * p11 * q214 * q311)∗ * ⌜a1⌝ * p13 *
      ((⌜a4ᶜ⌝ + ⌜a4⌝ * (⌜a2ᶜ⌝ * p22)∗ * ⌜a2 ⊓ a3ᶜ⌝ * p41 * p11) * q214 * q311 *
        (⌜a1ᶜ⌝ * p11 * q214 * q311)∗ * ⌜a1⌝ * p13)∗ *
      ⌜a4⌝ * (⌜a2ᶜ⌝ * p22)∗ * ⌜a2 ⊓ a3⌝ * z2 =
    x1 * p41 * p11 * q214 * q311 *
      (⌜a1ᶜ ⊓ a4ᶜ⌝ * p11 * q214 * q311 + ⌜a1ᶜ ⊓ a4⌝ * p11 * q214 * q311 +
       ⌜a1 ⊓ a4ᶜ⌝ * p13 * ⌜a4ᶜ⌝ * q214 * q311 +
       ⌜a1 ⊓ a4⌝ * p13 * (⌜a2ᶜ⌝ * p22)∗ * ⌜a2 ⊓ a3ᶜ⌝ * p41 * p11 * q214 * q311)∗ *
      ⌜a1⌝ * p13 * (⌜a2ᶜ⌝ * p22)∗ * ⌜a2 ⊓ a3 ⊓ a4⌝ * z2 := by
  have hL := test_loop_comm a4 a2ᶜ p22 h2
  have hb := split_branches a1 a4 p11 (q214 * q311) p13
    ((⌜a2ᶜ⌝ * p22)∗ * ⌜a2 ⊓ a3ᶜ⌝ * p41 * p11) h1
  have hd := denest (x1 * p41 * p11 * q214 * q311) (⌜a1ᶜ⌝ * p11 * q214 * q311)
    (⌜a1⌝ * p13) ((⌜a4ᶜ⌝ + ⌜a4⌝ * (⌜a2ᶜ⌝ * p22)∗ * ⌜a2 ⊓ a3ᶜ⌝ * p41 * p11) * q214 * q311)
    (⌜a4⌝ * (⌜a2ᶜ⌝ * p22)∗ * ⌜a2 ⊓ a3⌝ * z2)
  simp only [mul_assoc] at hb hd ⊢
  rw [hd, hb]
  rw [reassoc hL]
  simp only [mul_assoc]
  rw [reassoc (KAT.test_inf a4 (a2 ⊓ a3)).symm, inf_comm a4]

/-- Branches trapped in `¬b`, and an unreachable `¬a ∧ b` branch, cannot
contribute to an execution that finishes in `a ∧ b`. -/
theorem prune_branches (a b : T) (p u v w : K)
    (hp : p * ⌜a ⊓ bᶜ ⊔ aᶜ ⊓ b⌝ ≤ 0)
    (hu : ⌜b⌝ * u = u * ⌜b⌝) (hv : ⌜b⌝ * v = v * ⌜b⌝) :
    p * (⌜bᶜ⌝ * u + ⌜aᶜ ⊓ b⌝ * v + ⌜a ⊓ b⌝ * w * p)∗ * ⌜a ⊓ b⌝ =
      p * (⌜a ⊓ b⌝ * w * p)∗ * ⌜a ⊓ b⌝ := by hkat 30000

/-- Composition preserves commutation. -/
theorem comm_mul {c x y : K} (hx : c * x = x * c) (hy : c * y = y * c) :
    c * (x * y) = (x * y) * c := by rw [← mul_assoc, hx, mul_assoc, hy, ← mul_assoc]

/-- A sequence that establishes agreement still does so after an action preserving both tests. -/
theorem agreement_after (a b : T) (r q : K)
    (hr : r * ⌜a ⊓ bᶜ ⊔ aᶜ ⊓ b⌝ ≤ 0)
    (ha : ⌜a⌝ * q = q * ⌜a⌝) (hb : ⌜b⌝ * q = q * ⌜b⌝) :
    r * q * ⌜a ⊓ bᶜ ⊔ aᶜ ⊓ b⌝ ≤ 0 := by hkat 10000

/-- The three superfluous branches disappear (equation 24), treating the
inner while loop and its following test as an opaque program fragment. -/
theorem step24 (a b : T) (r q w v s : K)
    (hr : r * ⌜a ⊓ bᶜ ⊔ aᶜ ⊓ b⌝ ≤ 0)
    (haq : ⌜a⌝ * q = q * ⌜a⌝) (hbq : ⌜b⌝ * q = q * ⌜b⌝)
    (hbw : ⌜b⌝ * w = w * ⌜b⌝) (hbv : ⌜b⌝ * v = v * ⌜b⌝) :
    r * q * (⌜aᶜ ⊓ bᶜ⌝ * w * q + ⌜aᶜ ⊓ b⌝ * w * q +
      ⌜a ⊓ bᶜ⌝ * v * ⌜bᶜ⌝ * q + ⌜a ⊓ b⌝ * s * r * q)∗ * ⌜a ⊓ b⌝ =
      r * q * (⌜a ⊓ b⌝ * s * r * q)∗ * ⌜a ⊓ b⌝ := by
  have hp := agreement_after a b r q hr haq hbq
  have hv := comm_mul hbw hbq
  have hu : ⌜b⌝ * (⌜aᶜ⌝ * w * q + ⌜a⌝ * v * ⌜bᶜ⌝ * q) =
      (⌜aᶜ⌝ * w * q + ⌜a⌝ * v * ⌜bᶜ⌝ * q) * ⌜b⌝ := by
    clear hr haq hp hv
    hkat 10000
  have hh := prune_branches a b (r * q)
    (⌜aᶜ⌝ * w * q + ⌜a⌝ * v * ⌜bᶜ⌝ * q) (w * q) s hp hu hv
  have he : ⌜bᶜ⌝ * (⌜aᶜ⌝ * w * q + ⌜a⌝ * v * ⌜bᶜ⌝ * q) +
      ⌜aᶜ ⊓ b⌝ * (w * q) + ⌜a ⊓ b⌝ * s * (r * q) =
      ⌜aᶜ ⊓ bᶜ⌝ * w * q + ⌜aᶜ ⊓ b⌝ * w * q +
        ⌜a ⊓ bᶜ⌝ * v * ⌜bᶜ⌝ * q + ⌜a ⊓ b⌝ * s * r * q := by kat
  rw [he] at hh
  simpa only [mul_assoc] using hh

/-- Agreement established by `p` makes the extra test `b` redundant (equation 29). -/
theorem step29 (a b : T) (p v h : K)
    (hp : p * ⌜a ⊓ bᶜ ⊔ aᶜ ⊓ b⌝ ≤ 0)
    (ha : ⌜a⌝ * h = h * ⌜a⌝) (hb : ⌜b⌝ * h = h * ⌜b⌝) :
    p * (⌜a ⊓ b⌝ * v * p)∗ * h * ⌜a ⊓ b⌝ = (p * ⌜a⌝ * v)∗ * p * h * ⌜a⌝ := by
  have ht : p * ⌜a ⊓ b⌝ = p * ⌜a⌝ := by clear ha hb; hkat
  have he : p * h * ⌜a ⊓ b⌝ = p * h * ⌜a⌝ := by clear ht; hkat 10000
  calc
    _ = (p * ⌜a ⊓ b⌝ * v)∗ * (p * h * ⌜a ⊓ b⌝) := by kat
    _ = _ := by rw [ht, he]; simp only [mul_assoc]

/-- A test commutes with every other test. -/
theorem comm_tests (a b : T) : (⌜a⌝ : K) * ⌜b⌝ = ⌜b⌝ * ⌜a⌝ := by kat

/-- Move an action through a while loop if it commutes with its test and body. -/
theorem action_loop_comm (a : T) (v p : K)
    (ha : ⌜a⌝ * v = v * ⌜a⌝) (hp : v * p = p * v) :
    v * (⌜a⌝ * p)∗ = (⌜a⌝ * p)∗ * v := by
  symm
  apply KleeneAlgebra.kstar_mul_eq_mul_kstar_of_eq
  rw [mul_assoc, ← hp, ← mul_assoc, ha, mul_assoc]

/-- Pull an assignment past the inner loop and its exit tests. -/
theorem move_inner (a b : T) (v l : K) (hv : v * l = l * v)
    (ha : ⌜a⌝ * l = l * ⌜a⌝) (hb : ⌜b⌝ * v = v * ⌜b⌝) :
    ⌜a⌝ * v * l * ⌜b⌝ = l * ⌜a ⊓ b⌝ * v := by
  calc
    _ = ⌜a⌝ * l * v * ⌜b⌝ := by rw [mul_assoc _ v l, hv, ← mul_assoc]
    _ = l * ⌜a⌝ * ⌜b⌝ * v := by rw [ha, mul_assoc _ v, ← hb, ← mul_assoc]
    _ = _ := by rw [mul_assoc l, ← KAT.test_inf]

/-- With `a = b` initially and `b` unchanged by the loop, an exit satisfying
both tests must have skipped the loop. -/
theorem loop_exit_agreement (a b : T) (q p : K)
    (hq : q * ⌜a ⊓ bᶜ ⊔ aᶜ ⊓ b⌝ ≤ 0) (hp : ⌜b⌝ * p = p * ⌜b⌝) :
    q * (⌜aᶜ⌝ * p)∗ * ⌜a ⊓ b⌝ = q * ⌜a⌝ := by hkat 10000

/-- If the final tests disagree, the initial loop test must have been false. -/
theorem loop_enter_agreement (a b : T) (q r p : K)
    (hq : q * ⌜a ⊓ bᶜ ⊔ aᶜ ⊓ b⌝ ≤ 0)
    (hp : ⌜b⌝ * p = p * ⌜b⌝) (hr : ⌜b⌝ * r = r * ⌜b⌝) :
    q * r * (⌜aᶜ⌝ * p)∗ * ⌜a ⊓ bᶜ⌝ = q * ⌜aᶜ⌝ * r * (⌜aᶜ⌝ * p)∗ * ⌜a⌝ := by hkat 30000

/-- Unroll the inner loop twice: agreement after two iterations rules out
all longer terminating paths (equation 38). -/
theorem step38 (a b : T) (s q r p z : K)
    (hap : ⌜a⌝ * p = p * ⌜a⌝) (haq : ⌜a⌝ * q = q * ⌜a⌝)
    (hbr : ⌜b⌝ * r = r * ⌜b⌝)
    (hr : r * p * p * ⌜a ⊓ bᶜ ⊔ aᶜ ⊓ b⌝ ≤ 0) :
    s * (⌜a⌝ * q * ⌜bᶜ⌝ * r * (⌜bᶜ⌝ * p)∗ * ⌜b⌝)∗ * q * ⌜b⌝ * (⌜bᶜ⌝ * p)∗ * ⌜a ⊓ b⌝ * z =
      s * ⌜a⌝ * q * (⌜bᶜ⌝ * r * ⌜a⌝ * p * ⌜b⌝ * q +
        ⌜bᶜ⌝ * r * ⌜a⌝ * p * ⌜bᶜ⌝ * (p * q))∗ * ⌜b⌝ * z := by hkat 100000

/-- Commutation with a test also gives commutation with its complement. -/
theorem compl_comm (a : T) (p : K) (h : ⌜a⌝ * p = p * ⌜a⌝) :
    ⌜aᶜ⌝ * p = p * ⌜aᶜ⌝ := by hkat

/-- Combine two test commutation facts. -/
theorem inf_commute (a b : T) (p : K)
    (ha : ⌜a⌝ * p = p * ⌜a⌝) (hb : ⌜b⌝ * p = p * ⌜b⌝) :
    ⌜a ⊓ b⌝ * p = p * ⌜a ⊓ b⌝ := by
  rw [KAT.test_inf, mul_assoc, hb, ← mul_assoc, ha, mul_assoc]

end Paterson.Algebra
