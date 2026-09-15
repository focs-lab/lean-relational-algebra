import RelationAlgebra.Decide.HKATTactic
import RelationAlgebra.Decide.Tactic
import RelationAlgebra.Models.Rel

/-!
# Certifying compiler optimisations

A port of upstream `examples/compiler_opts.v` (revision
`2d2af3631929399bbac56f57b3e15302d8697e1c`), which formalises the compiler optimisations of

> Dexter Kozen and Maria-Cristina Patron, *Certification of compiler optimizations using Kleene
> algebra with tests*, Proc. CL 2000, LNAI 1861, pages 568-582, Springer.

Each optimisation is an equality between two programs that holds under hypotheses about the
primitive actions and tests, for instance "`p` always establishes `¬a`", or "`b` commutes with
`q`".  Those are the Hoare-style hypotheses that `hkat` eliminates.

## Correspondence with upstream

All twelve upstream optimisation statements are present.

| Upstream | Here | Proof |
|---|---|---|
| `opti_3_1_a` | `deadcode_branch` | `hkat` |
| `opti_3_1_b` | `deadcode_loop` | `hkat` |
| `opti_3_2` | `common_subexpression` | `calc` + `hkat` |
| `opti_3_3` | `copy_propagation` | `calc` + `hkat` |
| `opti_3_4i` | `loop_hoisting` | `calc` + `hkat` + a star-commutation step |
| `opti_3_4ii` | `loop_hoisting'` | `calc` + `hkat` + two star-commutation steps |
| `opti_3_5` | `induction_variable` | `calc` + `hkat` |
| `opti_3_8` | `loop_unrolling` | `kat` |
| `opti_3_9` | `redundant_load` | `hkat` |
| `opti_3_10'i` | `bounds_check` | `hkat` |
| `opti_3_10'` | `bounds_check'` | `subst` then `bounds_check` |
| `opti_3_11` | `sentinels` | `hkat` |

Of upstream's five preliminary lemmas, `lemma_1` (`kstar_slide_of_absorb`), `lemma_2`
(`test_kstar_of_comm`) and `lemma_3` (`kstar_eq_one_add_mul_sq`) are ported.  `lemma_1'` is the
categorical dual of `lemma_1` and `lemma_1''` is used only inside an alternative proof that
upstream leaves commented out; neither is needed here.

Upstream proves the four "commutation-heavy" optimisations (`opti_3_2`, `opti_3_3`, `opti_3_4i`,
`opti_3_4ii`) with its `mrewrite` tactic, which rewrites modulo associativity of composition.
This port has no `mrewrite`, so the associativity bookkeeping is done explicitly in `calc`
steps.  That is more verbose but no less complete: the Horn theory of Kleene algebra with
commutation hypotheses being undecidable says nothing about these particular instances, each of
which has a proof.  For `opti_3_4ii` the route taken here is shorter than upstream's and does
not need `lemma_1`.

## Scope

The twelve optimisation theorems are stated for `SetRel α α`, with tests `Set α`.  Untyped KAT
completeness now lets `kat` and `hkat` work with arbitrary
`[BooleanAlgebra T] [KleeneAlgebra K] [KAT T K]`; generalising these theorem statements remains
to be done.  The preliminary lemmas that need no tests are stated for an arbitrary Kleene algebra.

Three of the examples need far more than the default fuel and take tens of seconds each; the
amount is recorded at each one.  That is a fair measure of the gap between this port's naive
bisimulation search and upstream's OCaml-backed decision procedure.
-/

open scoped Computability SetRel KAT

namespace CompilerOpts

/-! ### Preliminary lemmas -/

section Preliminaries

variable {K : Type*} [KleeneAlgebra K] (x y u : K)

/-- Upstream `lemma_1`: if `x * y` is absorbed on the right by `x`, iteration can be slid.
Holds in every Kleene algebra. -/
theorem kstar_slide_of_absorb (h : x * y = x * y * x) : x * y∗ = x * (y * x)∗ := by
  rw [KleeneAlgebra.mul_kstar_eq_kstar_mul]
  refine le_antisymm ?_ ?_
  · refine mul_kstar_le KleeneAlgebra.le_kstar_mul ?_
    calc (x * y)∗ * x * y = (x * y)∗ * (x * y) := by rw [mul_assoc]
      _ = (x * y)∗ * (x * y * x) := by rw [← h]
      _ = (x * y)∗ * (x * y) * x := by simp only [mul_assoc]
      _ ≤ (x * y)∗ * x := mul_le_mul_left kstar_mul_le_kstar x
  · refine kstar_mul_le KleeneAlgebra.le_mul_kstar ?_
    calc x * y * (x * y∗) = x * y * x * y∗ := by simp only [mul_assoc]
      _ = x * y * y∗ := by rw [← h]
      _ = x * (y * y∗) := by rw [mul_assoc]
      _ ≤ x * y∗ := mul_le_mul_right mul_kstar_le_kstar x

/-- Upstream `lemma_3`: unrolling an iteration into even and odd steps. -/
theorem kstar_eq_one_add_mul_sq : u∗ = (1 + u) * (u * u)∗ := by ka

end Preliminaries

variable {α : Type*} (a b c d : Set α) (p q r s t u v w : SetRel α α)

/-- Upstream `lemma_2`: a test commuting with an action also commutes with its iteration. -/
theorem test_kstar_of_comm (h : ⌜b⌝ * q = q * ⌜b⌝) :
    (⌜b⌝ : SetRel α α) * q∗ = ⌜b⌝ * (q * ⌜b⌝)∗ := by hkat

/-! ### 3.1 Dead code elimination -/

/-- Upstream `opti_3_1_a`: if `p` always establishes `¬a`, the `a` branch after it is dead. -/
theorem deadcode_branch (h : p = p * ⌜aᶜ⌝) : p * (⌜a⌝ * q + ⌜aᶜ⌝) = p := by hkat

/-- Upstream `opti_3_1_b`: if `p` always establishes `¬a`, the loop guarded by `a` never
runs. -/
theorem deadcode_loop (h : p = p * ⌜aᶜ⌝) : p * (⌜a⌝ * q)∗ * ⌜aᶜ⌝ = p := by hkat

/-! ### 3.2 Common subexpression elimination -/

/-- Upstream `opti_3_2`. -/
theorem common_subexpression (hpa : p = p * ⌜a⌝) (haq : (⌜a⌝ : SetRel α α) * q = ⌜a⌝ * q * ⌜b⌝)
    (hbr : (⌜b⌝ : SetRel α α) * r = ⌜b⌝) (hr : r = w * r) (hw : q * w = w) :
    p * q = p * r := by
  have hqr : r = q * r := by
    calc r = w * r := hr
      _ = q * w * r := by rw [hw]
      _ = q * (w * r) := mul_assoc q w r
      _ = q * r := by rw [← hr]
  have key : p * q * r = p * q := by hkat 200000
  calc p * q = p * q * r := key.symm
    _ = p * (q * r) := by simp only [mul_assoc]
    _ = p * r := by rw [← hqr]

/-! ### 3.3 Copy propagation -/

/-- Upstream `opti_3_3`. -/
theorem copy_propagation (hqa : q = q * ⌜a⌝) (har : (⌜a⌝ : SetRel α α) * r = ⌜a⌝ * r * ⌜b⌝)
    (hbs : (⌜b⌝ : SetRel α α) * s = ⌜b⌝) (hs : s = w * s) (hw : r * w = w)
    (hsv : s * v = v * s) (hv : q * v = v) :
    p * q * r * v = p * s * v := by
  have hrs : s = r * s := by
    calc s = w * s := hs
      _ = r * w * s := by rw [hw]
      _ = r * (w * s) := mul_assoc r w s
      _ = r * s := by rw [← hs]
  have hrsv : r * (s * v) = s * v := by rw [← mul_assoc, ← hrs]
  have hqsv : q * (s * v) = s * v := by
    calc q * (s * v) = q * (v * s) := by rw [hsv]
      _ = q * v * s := by rw [mul_assoc]
      _ = v * s := by rw [hv]
      _ = s * v := by rw [← hsv]
  have key : p * q * r * s * v = p * q * r * v := by hkat 200000
  calc p * q * r * v = p * q * r * s * v := key.symm
    _ = p * (q * (r * (s * v))) := by simp only [mul_assoc]
    _ = p * (q * (s * v)) := by rw [hrsv]
    _ = p * (s * v) := by rw [hqsv]
    _ = p * s * v := by rw [mul_assoc]

/-! ### 3.4 Loop hoisting -/

/-- Upstream `opti_3_4i`.  Needs `hkat 200000`; takes about a minute. -/
theorem loop_hoisting (hub : u * ⌜b⌝ = u) (hbu : (⌜b⌝ : SetRel α α) * u = ⌜b⌝)
    (hbq : (⌜b⌝ : SetRel α α) * q = q * ⌜b⌝) (hbs : (⌜b⌝ : SetRel α α) * s = s * ⌜b⌝)
    (hbr : (⌜b⌝ : SetRel α α) * r = r * ⌜b⌝) (haw : (⌜a⌝ : SetRel α α) * w = w * ⌜a⌝)
    (hur : u * r = q) (huw : u * w = w) (hqsw : q * s * w = w * (q * s)) :
    p * u * (⌜a⌝ * r * s)∗ * ⌜aᶜ⌝ * w = p * (⌜a⌝ * q * s)∗ * ⌜aᶜ⌝ * w := by
  have hcomm : ((⌜a⌝ : SetRel α α) * q * s) * w = w * (⌜a⌝ * q * s) := by
    calc ((⌜a⌝ : SetRel α α) * q * s) * w = ⌜a⌝ * (q * s * w) := by simp only [mul_assoc]
      _ = ⌜a⌝ * (w * (q * s)) := by rw [hqsw]
      _ = (⌜a⌝ * w) * (q * s) := by simp only [mul_assoc]
      _ = (w * ⌜a⌝) * (q * s) := by rw [haw]
      _ = w * (⌜a⌝ * q * s) := by simp only [mul_assoc]
  have hstar : ((⌜a⌝ : SetRel α α) * q * s)∗ * w = w * (⌜a⌝ * q * s)∗ :=
    KleeneAlgebra.kstar_mul_eq_mul_kstar_of_eq hcomm
  calc p * u * (⌜a⌝ * r * s)∗ * ⌜aᶜ⌝ * w
      = p * u * ⌜b⌝ * (⌜a⌝ * ⌜b⌝ * (u * r) * s)∗ * ⌜aᶜ⌝ * w := by hkat 200000
    _ = p * u * ⌜b⌝ * (⌜a⌝ * ⌜b⌝ * q * s)∗ * ⌜aᶜ⌝ * w := by rw [hur]
    _ = p * u * (⌜a⌝ * q * s)∗ * w * ⌜aᶜ⌝ := by hkat 200000
    _ = p * u * ((⌜a⌝ * q * s)∗ * w) * ⌜aᶜ⌝ := by simp only [mul_assoc]
    _ = p * u * (w * (⌜a⌝ * q * s)∗) * ⌜aᶜ⌝ := by rw [hstar]
    _ = p * (u * w) * (⌜a⌝ * q * s)∗ * ⌜aᶜ⌝ := by simp only [mul_assoc]
    _ = p * w * (⌜a⌝ * q * s)∗ * ⌜aᶜ⌝ := by rw [huw]
    _ = p * ((⌜a⌝ * q * s)∗ * w) * ⌜aᶜ⌝ := by rw [hstar]; simp only [mul_assoc]
    _ = p * (⌜a⌝ * q * s)∗ * ⌜aᶜ⌝ * w := by hkat 200000

/-- Upstream `opti_3_4ii`.  The proof here is shorter than upstream's and avoids
`kstar_slide_of_absorb`: the whole content is that `w` commutes with both loop bodies. -/
theorem loop_hoisting' (hwu : u = w * u) (huw : u * w = w) (hpq : w * p * q = p * q * w)
    (hw : w * ⌜a⌝ = (⌜a⌝ : SetRel α α) * w) :
    (⌜a⌝ * u * p * q)∗ * ⌜aᶜ⌝ * u = (⌜a⌝ * p * q)∗ * ⌜aᶜ⌝ * u := by
  have hcw : (⌜aᶜ⌝ : SetRel α α) * w = w * ⌜aᶜ⌝ := by hkat
  have hCw : ⌜a⌝ * u * p * q * w = w * (⌜a⌝ * p * q) := by
    calc ⌜a⌝ * u * p * q * w = ⌜a⌝ * u * (p * q * w) := by simp only [mul_assoc]
      _ = ⌜a⌝ * u * (w * p * q) := by rw [← hpq]
      _ = ⌜a⌝ * (u * w) * (p * q) := by simp only [mul_assoc]
      _ = ⌜a⌝ * w * (p * q) := by rw [huw]
      _ = w * ⌜a⌝ * (p * q) := by rw [← hw]
      _ = w * (⌜a⌝ * p * q) := by simp only [mul_assoc]
  have hYcomm : (⌜a⌝ : SetRel α α) * p * q * w = w * (⌜a⌝ * p * q) := by
    calc (⌜a⌝ : SetRel α α) * p * q * w = ⌜a⌝ * (p * q * w) := by simp only [mul_assoc]
      _ = ⌜a⌝ * (w * p * q) := by rw [← hpq]
      _ = ⌜a⌝ * w * (p * q) := by simp only [mul_assoc]
      _ = w * ⌜a⌝ * (p * q) := by rw [← hw]
      _ = w * (⌜a⌝ * p * q) := by simp only [mul_assoc]
  have hCstar : ((⌜a⌝ : SetRel α α) * u * p * q)∗ * w = w * (⌜a⌝ * p * q)∗ :=
    KleeneAlgebra.kstar_mul_eq_mul_kstar_of_eq hCw
  have hYstar : ((⌜a⌝ : SetRel α α) * p * q)∗ * w = w * (⌜a⌝ * p * q)∗ :=
    KleeneAlgebra.kstar_mul_eq_mul_kstar_of_eq hYcomm
  have hz : (⌜aᶜ⌝ : SetRel α α) * u = w * (⌜aᶜ⌝ * u) := by
    calc (⌜aᶜ⌝ : SetRel α α) * u = ⌜aᶜ⌝ * (w * u) := by rw [← hwu]
      _ = ⌜aᶜ⌝ * w * u := by simp only [mul_assoc]
      _ = w * ⌜aᶜ⌝ * u := by rw [hcw]
      _ = w * (⌜aᶜ⌝ * u) := by simp only [mul_assoc]
  calc (⌜a⌝ * u * p * q)∗ * ⌜aᶜ⌝ * u
      = (⌜a⌝ * u * p * q)∗ * (⌜aᶜ⌝ * u) := mul_assoc _ _ _
    _ = (⌜a⌝ * u * p * q)∗ * (w * (⌜aᶜ⌝ * u)) := by rw [← hz]
    _ = (⌜a⌝ * u * p * q)∗ * w * (⌜aᶜ⌝ * u) := (mul_assoc _ _ _).symm
    _ = w * (⌜a⌝ * p * q)∗ * (⌜aᶜ⌝ * u) := by rw [hCstar]
    _ = (⌜a⌝ * p * q)∗ * w * (⌜aᶜ⌝ * u) := by rw [← hYstar]
    _ = (⌜a⌝ * p * q)∗ * (w * (⌜aᶜ⌝ * u)) := mul_assoc _ _ _
    _ = (⌜a⌝ * p * q)∗ * (⌜aᶜ⌝ * u) := by rw [← hz]
    _ = (⌜a⌝ * p * q)∗ * ⌜aᶜ⌝ * u := (mul_assoc _ _ _).symm

/-! ### 3.5 Induction variable elimination -/

/-- Upstream `opti_3_5`.  Needs `hkat 200000`; takes about twenty seconds. -/
theorem induction_variable (hq : q = q * ⌜b⌝) (hb : (⌜b⌝ : SetRel α α) = ⌜b⌝ * q)
    (hr : (⌜c⌝ : SetRel α α) * r = ⌜c⌝ * r * ⌜b⌝)
    (hbp : (⌜b⌝ : SetRel α α) * p = ⌜b⌝ * p * ⌜c⌝)
    (hcq : (⌜c⌝ : SetRel α α) * q = ⌜c⌝ * r) :
    q * (⌜a⌝ * p * q)∗ = q * (⌜a⌝ * p * r)∗ := by
  have e : (⌜b⌝ : SetRel α α) * p * q = ⌜b⌝ * p * r := by
    calc (⌜b⌝ : SetRel α α) * p * q = (⌜b⌝ * p * ⌜c⌝) * q := by rw [← hbp]
      _ = ⌜b⌝ * p * (⌜c⌝ * q) := by simp only [mul_assoc]
      _ = ⌜b⌝ * p * (⌜c⌝ * r) := by rw [hcq]
      _ = (⌜b⌝ * p * ⌜c⌝) * r := by simp only [mul_assoc]
      _ = ⌜b⌝ * p * r := by rw [← hbp]
  calc q * (⌜a⌝ * p * q)∗ = q * (⌜a⌝ * (⌜b⌝ * p * q))∗ * ⌜b⌝ := by hkat 200000
    _ = q * (⌜a⌝ * (⌜b⌝ * p * r))∗ * ⌜b⌝ := by rw [e]
    _ = q * (⌜a⌝ * p * r)∗ := by hkat 200000

/-! ### 3.8 Loop unrolling -/

/-- Upstream `opti_3_8`: unrolling the body of a `while` loop once.  Needs no hypothesis. -/
theorem loop_unrolling :
    ((⌜a⌝ : SetRel α α) * p)∗ * ⌜aᶜ⌝ = (⌜a⌝ * p * (⌜a⌝ * p + ⌜aᶜ⌝))∗ * ⌜aᶜ⌝ := by kat

/-! ### 3.9 Redundant loads and stores -/

/-- Upstream `opti_3_9`: if `p` establishes `a` and `q` does nothing when `a` holds, `q` can be
dropped. -/
theorem redundant_load (hp : p = p * ⌜a⌝) (hq : (⌜a⌝ : SetRel α α) * q = ⌜a⌝) : p * q = p := by
  hkat

/-! ### 3.10 Array bounds check elimination -/

/-- Upstream `opti_3_10'i`.  Two test variables give four atoms; needs `hkat 200000` and takes
about half a minute. -/
theorem bounds_check (h1 : u * ⌜a⌝ = u) (h2 : (⌜a ⊓ b⌝ : SetRel α α) * p = p * ⌜a ⊓ b⌝)
    (h3 : (⌜a⌝ : SetRel α α) * (⌜b⌝ * p * q * v) = (⌜b⌝ * p * q * v) * ⌜a⌝) :
    u * (⌜b⌝ * p * (⌜a ⊓ b⌝ * q + ⌜(a ⊓ b)ᶜ⌝ * s) * v)∗ * ⌜bᶜ⌝
      = u * (⌜b⌝ * p * q * v)∗ * ⌜bᶜ⌝ := by hkat 200000

/-- Upstream `opti_3_10'`: the same with the conjunction abbreviated by a third test. -/
theorem bounds_check' (hc : a ⊓ b = c) (h1 : u * ⌜a⌝ = u)
    (h2 : (⌜c⌝ : SetRel α α) * p = p * ⌜c⌝)
    (h3 : (⌜a⌝ : SetRel α α) * (⌜b⌝ * p * q * v) = (⌜b⌝ * p * q * v) * ⌜a⌝) :
    u * (⌜b⌝ * p * (⌜c⌝ * q + ⌜cᶜ⌝ * s) * v)∗ * ⌜bᶜ⌝ = u * (⌜b⌝ * p * q * v)∗ * ⌜bᶜ⌝ := by
  subst hc
  exact bounds_check a b p q s u v h1 h2 h3

/-! ### 3.11 Introduction of sentinels -/

/-- Upstream `opti_3_11`, its hardest example: four test variables, so sixteen atoms.  Needs
`hkat 500000` and takes about a minute; upstream reports about two seconds for its OCaml-backed
algorithm. -/
theorem sentinels (h1 : u * ⌜c⌝ = u) (h2 : (⌜c⌝ : SetRel α α) * p = p * ⌜c⌝)
    (h3 : (⌜c⌝ : SetRel α α) * q = q * ⌜c⌝) (h4 : p * ⌜d⌝ = p)
    (h5 : (⌜a⌝ : SetRel α α) * q * ⌜d⌝ = ⌜a⌝ * q) (h6 : c ⊓ d ⊓ b ≤ a) :
    u * p * (⌜a ⊓ b⌝ * q)∗ * ⌜(a ⊓ b)ᶜ⌝ * (⌜a⌝ * t + ⌜aᶜ⌝ * s)
      = u * p * (⌜b⌝ * q)∗ * ⌜bᶜ⌝ * (⌜a⌝ * t + ⌜aᶜ⌝ * s) := by hkat 500000

end CompilerOpts
