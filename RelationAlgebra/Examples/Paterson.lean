import RelationAlgebra.Examples.Paterson.Algebra
import RelationAlgebra.Examples.Paterson.Facts
import RelationAlgebra.Examples.Paterson.Stages

/-! # Paterson's flowchart equivalence

A relational mechanization of the S6A = S6E proof of Angus and Kozen (2001), following
Damien Pous's `examples/paterson.v`. Assignment facts are proved from a five-cell store;
the algebraic steps use the library's kernel-checked KAT automation.

## Using the result

`Paterson.paterson M` states equality of the two relations. `Paterson.terminates_iff M s t`
is its pointwise form. `M : Interpretation` supplies arbitrary functions `f : ℕ → ℕ`,
`g : ℕ → ℕ → ℕ`, and `p : ℕ → Bool`; there are no other hypotheses.

The relations describe terminating executions. Both programs use `io` for their input and
output and clear `y1`–`y4` before returning. The theorem equates their entire final stores;
it does not assert that either program terminates on every input.

## Proof organization and sources

* `Paterson/Model`: the store, substitution laws, and dead-store elimination through iteration.
* `Paterson/Programs` and `Paterson/Stages`: the two schemes and intermediate expressions.
* `Paterson/Facts`: all concrete assignment hypotheses, proved from store updates.
* `Paterson/Algebra`: the reusable steps, for any Kleene algebra with tests.

The proof follows [Damien Pous's `examples/paterson.v`](https://github.com/damien-pous/relation-algebra/blob/2d2af3631929399bbac56f57b3e15302d8697e1c/examples/paterson.v)
and [Angus and Kozen, *Kleene Algebra with Tests and Program Schematology* (2001), §5](https://www.cs.cornell.edu/~kozen/Papers/allegra.pdf).
The equation numbers identify the corresponding steps of their proof. The present checker
benefits from separating the larger `hkat` steps into smaller lemmas.
-/
open scoped Computability SetRel KAT
namespace Paterson
namespace Proof
open Algebra Stages
variable (M : Interpretation)
local notation "a1" => Programs.a1.denote M
local notation "a2" => Programs.a2.denote M
local notation "a3" => Programs.a3.denote M
local notation "a4" => Programs.a4.denote M
local notation "x1" => Programs.x1.denote M
local notation "s1" => Programs.s1.denote M
local notation "s2" => Programs.s2.denote M
local notation "z1" => Programs.z1.denote M
local notation "z2" => Programs.z2.denote M
local notation "p11" => Programs.p11.denote M
local notation "p13" => Programs.p13.denote M
local notation "p22" => Programs.p22.denote M
local notation "p41" => Programs.p41.denote M
local notation "q222" => Programs.q222.denote M
local notation "q214" => Programs.q214.denote M
local notation "q211" => Programs.q211.denote M
local notation "q311" => Programs.q311.denote M
local notation "r11" => Programs.r11.denote M
local notation "r12" => Programs.r12.denote M
local notation "r13" => Programs.r13.denote M
local notation "r22" => Programs.r22.denote M
local notation "bInit" => Programs.bInit.denote M
local notation "bNext" => Programs.bNext.denote M
local notation "qInit" => Programs.qInit.denote M
local notation "qNext" => Programs.qNext.denote M
local notation "L" => (⌜a2ᶜ⌝ * p22)∗

private theorem test_tail (a b : Set State) (r : SetRel State State) :
    ⌜a⌝ * (⌜b⌝ * r) = ⌜a ⊓ b⌝ * r := reassoc (KAT.test_inf a b).symm r

private theorem test_univ : (⌜(Set.univ : Set State)⌝ : SetRel State State) = 1 := KAT.test_top

private theorem p13_L : p13 * L = L * p13 :=
  action_loop_comm a2ᶜ p13 p22 (compl_comm a2 p13 (Facts.a2_p13 M)) (Facts.p13_p22 M)

private theorem a1_L : (⌜a1⌝ : SetRel State State) * L = L * ⌜a1⌝ :=
  test_loop_comm a1 a2ᶜ p22 (Facts.a1_p22 M)

private theorem a4_L : (⌜a4⌝ : SetRel State State) * L = L * ⌜a4⌝ :=
  test_loop_comm a4 a2ᶜ p22 (Facts.a4_p22 M)

private theorem eq19 : Programs.s6a.denote M = s19.denote M := by
  simpa only [Programs.s6a, s19, Prog.denote, BExpr.denote_and, BExpr.denote_not] using
    step19 a1 a2 a3 a4 x1 p41 p11 q214 q311 p13 p22 z2 (Facts.a4_p13 M) (Facts.a4_p22 M)

private theorem eq23 : s19.denote M = s23.denote M := by
  have hc := inf_commute (a2 ⊓ a3) a4 p13
    (inf_commute a2 a3 p13 (Facts.a2_p13 M) (Facts.a3_p13 M)) (Facts.a4_p13 M)
  have ht := move_inner a1 (a2 ⊓ a3 ⊓ a4) p13 L (p13_L M) (a1_L M) hc
  simp only [← inf_assoc] at ht
  simp only [s19, s23, Prog.denote, BExpr.denote_and, BExpr.denote_not]
  change x1 * p41 * p11 * q214 * q311 *
     (⌜a1ᶜ ⊓ a4ᶜ⌝ * p11 * q214 * q311 + ⌜a1ᶜ ⊓ a4⌝ * p11 * q214 * q311 +
      ⌜a1 ⊓ a4ᶜ⌝ * p13 * ⌜a4ᶜ⌝ * q214 * q311 +
      ⌜a1 ⊓ a4⌝ * p13 * (⌜a2ᶜ⌝ * p22)∗ * ⌜a2 ⊓ a3ᶜ⌝ * p41 * p11 * q214 * q311)∗ *
     ⌜a1⌝ * p13 * (⌜a2ᶜ⌝ * p22)∗ * ⌜a2 ⊓ a3 ⊓ a4⌝ * z2 =
    x1 * p41 * p11 * q214 * q311 *
     (⌜a1ᶜ ⊓ a4ᶜ⌝ * p11 * q214 * q311 + ⌜a1ᶜ ⊓ a4⌝ * p11 * q214 * q311 +
      ⌜a1 ⊓ a4ᶜ⌝ * p13 * ⌜a4ᶜ⌝ * q214 * q311 +
      ⌜a1 ⊓ a4⌝ * p13 * (⌜a2ᶜ⌝ * p22)∗ * ⌜a2 ⊓ a3ᶜ⌝ * p41 * p11 * q214 * q311)∗ *
     (⌜a2ᶜ⌝ * p22)∗ * ⌜a1 ⊓ a2 ⊓ a3 ⊓ a4⌝ * z2
  have ht' := reassoc ht z2
  simp only [mul_assoc] at ht' ⊢
  rw [ht', Facts.p13_z2 M]

private theorem eq24 : s23.denote M = s24.denote M := by
  have hh := step24 a1 a4 (p41 * p11) (q214 * q311) p11 p13
    (p13 * L * ⌜a2 ⊓ a3ᶜ⌝) (Facts.p41_p11 M)
    (comm_mul (Facts.a1_q214 M) (Facts.a1_q311 M))
    (comm_mul (Facts.a4_q214 M) (Facts.a4_q311 M)) (Facts.a4_p11 M) (Facts.a4_p13 M)
  have hc : L * ⌜a1 ⊓ a2 ⊓ a3 ⊓ a4⌝ = ⌜a1 ⊓ a4⌝ * (L * ⌜a2 ⊓ a3⌝) := by
    have ht := inf_commute a1 a4 L (a1_L M) (a4_L M)
    calc
      _ = L * (⌜a1 ⊓ a4⌝ * ⌜a2 ⊓ a3⌝) := by congr 1; kat
      _ = _ := by rw [← mul_assoc, ← ht, mul_assoc]
  simp only [s23, s24, Prog.denote, BExpr.denote_and, BExpr.denote_not]
  change x1 * p41 * p11 * q214 * q311 *
     (⌜a1ᶜ ⊓ a4ᶜ⌝ * p11 * q214 * q311 + ⌜a1ᶜ ⊓ a4⌝ * p11 * q214 * q311 +
      ⌜a1 ⊓ a4ᶜ⌝ * p13 * ⌜a4ᶜ⌝ * q214 * q311 +
      ⌜a1 ⊓ a4⌝ * p13 * (⌜a2ᶜ⌝ * p22)∗ * ⌜a2 ⊓ a3ᶜ⌝ * p41 * p11 * q214 * q311)∗ *
     (⌜a2ᶜ⌝ * p22)∗ * ⌜a1 ⊓ a2 ⊓ a3 ⊓ a4⌝ * z2 =
    x1 * p41 * p11 * q214 * q311 *
     (⌜a1 ⊓ a4⌝ * p13 * (⌜a2ᶜ⌝ * p22)∗ * ⌜a2 ⊓ a3ᶜ⌝ * p41 * p11 * q214 * q311)∗ *
     (⌜a2ᶜ⌝ * p22)∗ * ⌜a1 ⊓ a2 ⊓ a3 ⊓ a4⌝ * z2
  simp only [mul_assoc]
  have hc' := reassoc hc z2
  simp only [mul_assoc] at hc'
  simp only [hc']
  have hh' := congrArg (fun r : SetRel State State => x1 * r * (L * ⌜a2 ⊓ a3⌝ * z2)) hh
  simpa only [mul_assoc] using hh'

private theorem eq27 : s24.denote M = s27.denote M := by
  have hh := Facts.p41_p11_q214 M
  have hh' := reassoc hh
  simp only [mul_assoc] at hh hh'
  simp only [s24, s27, Prog.denote, BExpr.denote_and, BExpr.denote_not]
  change x1 * p41 * p11 * q214 * q311 *
     (⌜a1 ⊓ a4⌝ * p13 * (⌜a2ᶜ⌝ * p22)∗ * ⌜a2 ⊓ a3ᶜ⌝ * p41 * p11 * q214 * q311)∗ *
     (⌜a2ᶜ⌝ * p22)∗ * ⌜a1 ⊓ a2 ⊓ a3 ⊓ a4⌝ * z2 =
    x1 * p41 * p11 * q211 * q311 *
     (⌜a1 ⊓ a4⌝ * p13 * (⌜a2ᶜ⌝ * p22)∗ * ⌜a2 ⊓ a3ᶜ⌝ * p41 * p11 * q211 * q311)∗ *
     (⌜a2ᶜ⌝ * p22)∗ * ⌜a1 ⊓ a2 ⊓ a3 ⊓ a4⌝ * z2
  simp only [mul_assoc]
  rw [hh', hh']

private theorem eq29 : s27.denote M = s29.denote M := by
  have hp := agreement_after a1 a4 (p41 * p11) (q211 * q311) (Facts.p41_p11 M)
    (comm_mul (Facts.a1_q211 M) (Facts.a1_q311 M))
    (comm_mul (Facts.a4_q211 M) (Facts.a4_q311 M))
  have hh := step29 a1 a4 (p41 * p11 * q211 * q311) (p13 * L * ⌜a2 ⊓ a3ᶜ⌝)
    (L * ⌜a2 ⊓ a3⌝) (by simpa only [mul_assoc] using hp)
    (comm_mul (a1_L M) (comm_tests a1 (a2 ⊓ a3)))
    (comm_mul (a4_L M) (comm_tests a4 (a2 ⊓ a3)))
  have hx := congrArg (fun r : SetRel State State => x1 * r * z2) hh
  simp only [s27, s29, Prog.denote, BExpr.denote_and, BExpr.denote_not]
  change x1 * p41 * p11 * q211 * q311 *
     (⌜a1 ⊓ a4⌝ * p13 * (⌜a2ᶜ⌝ * p22)∗ * ⌜a2 ⊓ a3ᶜ⌝ * p41 * p11 * q211 * q311)∗ *
     (⌜a2ᶜ⌝ * p22)∗ * ⌜a1 ⊓ a2 ⊓ a3 ⊓ a4⌝ * z2 =
    x1 * (p41 * (p11 * q211 * q311 * ⌜a1⌝ * p13 * (⌜a2ᶜ⌝ * p22)∗ * ⌜a2 ⊓ a3ᶜ⌝))∗ *
     p41 * p11 * q211 * q311 * (⌜a2ᶜ⌝ * p22)∗ * ⌜a1 ⊓ a2 ⊓ a3⌝ * z2
  simpa only [mul_assoc, ← KAT.test_inf, test_tail, inf_assoc, inf_left_comm, inf_comm] using hx

private theorem eq31 : s29.denote M = s31.denote M := by
  have hh := Facts.gc_clr M .y4 body29 (by decide) (by decide)
  simpa [body29, s29, s31, Prog.gc, Prog.denote, test_univ, mul_assoc] using hh.symm

private theorem eq32 : s31.denote M = s32.denote M := by
  have hc := inf_commute a2 a3ᶜ p13 (Facts.a2_p13 M)
    (compl_comm a3 p13 (Facts.a3_p13 M))
  have ht := move_inner a1 (a2 ⊓ a3ᶜ) p13 L (p13_L M) (a1_L M) hc
  simp only [← inf_assoc, mul_assoc] at ht
  simp only [s31, s32, Prog.denote, BExpr.denote_and, BExpr.denote_not]
  change x1 * (p11 * q211 * q311 * ⌜a1⌝ * p13 * (⌜a2ᶜ⌝ * p22)∗ * ⌜a2 ⊓ a3ᶜ⌝)∗ *
     p11 * q211 * q311 * (⌜a2ᶜ⌝ * p22)∗ * ⌜a1 ⊓ a2 ⊓ a3⌝ * z2 =
    (x1 * p11) * (q211 * q311 * (⌜a2ᶜ⌝ * p22)∗ * ⌜a1 ⊓ a2 ⊓ a3ᶜ⌝ * (p13 * p11))∗ *
     q211 * q311 * (⌜a2ᶜ⌝ * p22)∗ * ⌜a1 ⊓ a2 ⊓ a3⌝ * z2
  simp only [mul_assoc]
  rw [ht]
  kat 10000

private theorem eq33 : s32.denote M = s33.denote M := by
  simp only [s32, s33, Prog.denote, BExpr.denote_and, BExpr.denote_not]
  change (x1 * p11) * (q211 * q311 * (⌜a2ᶜ⌝ * p22)∗ * ⌜a1 ⊓ a2 ⊓ a3ᶜ⌝ * (p13 * p11))∗ *
     q211 * q311 * (⌜a2ᶜ⌝ * p22)∗ * ⌜a1 ⊓ a2 ⊓ a3⌝ * z2 =
    s1 * (q211 * q311 * (⌜a2ᶜ⌝ * p22)∗ * ⌜a1 ⊓ a2 ⊓ a3ᶜ⌝ * r13)∗ *
     q211 * q311 * (⌜a2ᶜ⌝ * p22)∗ * ⌜a1 ⊓ a2 ⊓ a3⌝ * z2
  rw [Facts.x1_p11 M, Facts.p13_p11 M]

private theorem eq34 : s33.denote M = s34.denote M := by
  have hrL := action_loop_comm a2ᶜ r13 p22
    (compl_comm a2 r13 (Facts.a2_r13 M)) (Facts.r13_p22 M)
  have hrt := inf_commute a2 a3ᶜ r13 (Facts.a2_r13 M)
    (compl_comm a3 r13 (Facts.a3_r13 M))
  have haQ := comm_mul (Facts.a1_q211 M) (Facts.a1_q311 M)
  have ht : (q211 * q311) * L * ⌜a1 ⊓ a2 ⊓ a3ᶜ⌝ * r13 =
      ⌜a1⌝ * ((q211 * q311) * r13) * L * ⌜a2 ⊓ a3ᶜ⌝ := by
    have hatt := KAT.test_inf (K := SetRel State State) a1 (a2 ⊓ a3ᶜ)
    have haQL := comm_mul haQ (a1_L M)
    rw [inf_assoc, hatt]
    simp only [← mul_assoc]
    rw [← haQL]
    simp only [mul_assoc]
    rw [hrt, reassoc hrL.symm]
    simp only [mul_assoc]
  simp only [s33, s34, Prog.denote, BExpr.denote_and, BExpr.denote_not]
  change s1 * (q211 * q311 * (⌜a2ᶜ⌝ * p22)∗ * ⌜a1 ⊓ a2 ⊓ a3ᶜ⌝ * r13)∗ *
     q211 * q311 * (⌜a2ᶜ⌝ * p22)∗ * ⌜a1 ⊓ a2 ⊓ a3⌝ * z2 =
    s1 * (⌜a1⌝ * (q211 * q311 * r13) * (⌜a2ᶜ⌝ * p22)∗ * ⌜a2 ⊓ a3ᶜ⌝)∗ *
     q211 * q311 * (⌜a2ᶜ⌝ * p22)∗ * ⌜a1 ⊓ a2 ⊓ a3⌝ * z2
  simp only [mul_assoc] at ht ⊢
  rw [ht]

private theorem eq35 : s34.denote M = s35.denote M := by
  simp only [s34, s35, Prog.denote, BExpr.denote_and, BExpr.denote_not]
  change s1 * (⌜a1⌝ * (q211 * q311 * r13) * (⌜a2ᶜ⌝ * p22)∗ * ⌜a2 ⊓ a3ᶜ⌝)∗ *
     q211 * q311 * (⌜a2ᶜ⌝ * p22)∗ * ⌜a1 ⊓ a2 ⊓ a3⌝ * z2 =
    s1 * (⌜a1⌝ * (q211 * q311 * r12) * (⌜a2ᶜ⌝ * p22)∗ * ⌜a2 ⊓ a3ᶜ⌝)∗ *
     q211 * q311 * (⌜a2ᶜ⌝ * p22)∗ * ⌜a1 ⊓ a2 ⊓ a3⌝ * z2
  rw [Facts.q211_q311_r13 M]

private theorem eq36 : s35.denote M = s36.denote M := by
  have hi := loop_enter_agreement a2 a3 (q211 * q311) r12 p22
    (Facts.q211_q311 M) (Facts.a3_p22 M) (Facts.a3_r12 M)
  have he := loop_exit_agreement a2 a3 (q211 * q311) p22
    (Facts.q211_q311 M) (Facts.a3_p22 M)
  have he' : (q211 * q311) * L * ⌜a1 ⊓ a2 ⊓ a3⌝ =
      (q211 * q311) * ⌜a2⌝ * L * ⌜a1 ⊓ a2⌝ := by
    have h1 : (q211 * q311) * L * ⌜a1 ⊓ a2 ⊓ a3⌝ =
        ((q211 * q311) * L * ⌜a2 ⊓ a3⌝) * ⌜a1⌝ := by kat
    rw [h1, he]
    kat
  simp only [s35, s36, Prog.denote, BExpr.denote_and, BExpr.denote_not]
  change s1 * (⌜a1⌝ * (q211 * q311 * r12) * (⌜a2ᶜ⌝ * p22)∗ * ⌜a2 ⊓ a3ᶜ⌝)∗ *
     q211 * q311 * (⌜a2ᶜ⌝ * p22)∗ * ⌜a1 ⊓ a2 ⊓ a3⌝ * z2 =
    s1 * (⌜a1⌝ * (q211 * q311) * ⌜a2ᶜ⌝ * r12 * (⌜a2ᶜ⌝ * p22)∗ * ⌜a2⌝)∗ *
     (q211 * q311) * ⌜a2⌝ * (⌜a2ᶜ⌝ * p22)∗ * ⌜a1 ⊓ a2⌝ * z2
  have hi' := hi
  have he'' := reassoc he' z2
  simp only [mul_assoc] at hi' he'' ⊢
  rw [hi', he'']

private theorem eq37 : s36.denote M = s37.denote M := by
  have hh := Facts.gc_clr M .y3 body36 (by decide) (by decide)
  simpa [body36, s36, s37, Prog.gc, Prog.denote, test_univ, mul_assoc] using hh.symm

private theorem eq38 : s37.denote M = s38.denote M := by
  simpa only [s37, s38, Prog.denote, BExpr.denote_and, BExpr.denote_not] using
    step38 a1 a2 s1 q211 r12 p22 z2
      (Facts.a1_p22 M) (Facts.a1_q211 M) (Facts.a2_r12 M) (Facts.r12_p22 M)

private theorem eq43 : s38.denote M = s43.denote M := by
  simp only [s38, s43, Prog.denote, BExpr.denote_not]
  change s1 * ⌜a1⌝ * q211 * (⌜a2ᶜ⌝ * r12 * ⌜a1⌝ * p22 * ⌜a2⌝ * q211 +
     ⌜a2ᶜ⌝ * r12 * ⌜a1⌝ * p22 * ⌜a2ᶜ⌝ * (p22 * q211))∗ * ⌜a2⌝ * z2 =
    s1 * ⌜a1⌝ * q211 * (⌜a2ᶜ⌝ * r12 * ⌜a1⌝ * q211)∗ * ⌜a2⌝ * z2
  rw [Facts.p22_q211 M]
  have hi : ⌜a2ᶜ⌝ * r12 * ⌜a1⌝ * p22 * ⌜a2⌝ * q211 +
      ⌜a2ᶜ⌝ * r12 * ⌜a1⌝ * p22 * ⌜a2ᶜ⌝ * q211 = ⌜a2ᶜ⌝ * r12 * ⌜a1⌝ * (p22 * q211) := by kat
  rw [hi, Facts.p22_q211 M]

private theorem eq44 : s43.denote M = s44.denote M := by
  simp only [s43, s44, Prog.denote, BExpr.denote_not]
  change s1 * ⌜a1⌝ * q211 * (⌜a2ᶜ⌝ * r12 * ⌜a1⌝ * q211)∗ * ⌜a2⌝ * z2 =
    (⌜bInit⌝ * s1 * qInit * (⌜a2ᶜ⌝ * ⌜bNext⌝ * r12 * qNext)∗ * ⌜a2⌝ *
      assign M .io (.var .y2)) * Programs.clr.denote M
  have hi := reassoc (Facts.left_init M)
  have hl := Facts.left_loop M
  simp only [mul_assoc] at hi hl ⊢
  rw [hi, hl]
  rfl

private theorem eq_common : s44.denote M = common.denote M := by
  have hh := Facts.gc_clr M .y1 body44 (by decide) (by decide)
  simpa [body44, s44, common, Prog.gc, Prog.denote, test_univ, mul_assoc] using hh.symm

private theorem rhs_common : Programs.s6e.denote M = common.denote M := by
  simp only [Programs.s6e, common, Prog.denote, BExpr.denote_not]
  change s2 * ⌜a2⌝ * q222 * (⌜a2ᶜ⌝ * r22 * ⌜a2⌝ * q222)∗ * ⌜a2⌝ * z2 =
    ⌜bInit⌝ * qInit * (⌜a2ᶜ⌝ * ⌜bNext⌝ * qNext)∗ * ⌜a2⌝ * z2
  have hi := reassoc (Facts.right_init M)
  have hl := Facts.right_loop M
  simp only [mul_assoc] at hi hl ⊢
  rw [hi, hl]

end Proof

/-- **Paterson's flowchart equivalence**: S6A and S6E have the same relation of
initial and final states for every interpretation of `f`, `g`, and `P`.

As in Pous's statement, both schemes write their result to `io` and clear the four
temporary cells. No termination or additional equation on the interpretation is assumed.
-/
theorem paterson (M : Interpretation) : Programs.s6a.denote M = Programs.s6e.denote M := by
  calc
    _ = Stages.s19.denote M := Proof.eq19 M
    _ = Stages.s23.denote M := Proof.eq23 M
    _ = Stages.s24.denote M := Proof.eq24 M
    _ = Stages.s27.denote M := Proof.eq27 M
    _ = Stages.s29.denote M := Proof.eq29 M
    _ = Stages.s31.denote M := Proof.eq31 M
    _ = Stages.s32.denote M := Proof.eq32 M
    _ = Stages.s33.denote M := Proof.eq33 M
    _ = Stages.s34.denote M := Proof.eq34 M
    _ = Stages.s35.denote M := Proof.eq35 M
    _ = Stages.s36.denote M := Proof.eq36 M
    _ = Stages.s37.denote M := Proof.eq37 M
    _ = Stages.s38.denote M := Proof.eq38 M
    _ = Stages.s43.denote M := Proof.eq43 M
    _ = Stages.s44.denote M := Proof.eq44 M
    _ = Stages.common.denote M := Proof.eq_common M
    _ = _ := (Proof.rhs_common M).symm

/-- Pointwise form: either scheme can terminate in a given final state exactly
when the other can terminate in that state. -/
theorem terminates_iff (M : Interpretation) (s t : State) :
    (s, t) ∈ Programs.s6a.denote M ↔ (s, t) ∈ Programs.s6e.denote M := by
  rw [paterson]

end Paterson
