import RelationAlgebra.Converse

/-!
# A verified normalisation procedure for relation algebra

This file ports the *structural* core of `theories/normalisation.v` from Damien Pous'
Rocq/Coq library [`relation-algebra`](https://github.com/damien-pous/relation-algebra),
which is the basis of his `ra`, `ra_normalise` and `ra_simpl` tactics.  The Lean tactics
built on top of it are in `RelationAlgebra.Decide.RaTactic`.

## What is normalised

`RaTerm` is the syntax of the fragment consisting of `0`, `1`, variables, union `+`,
composition `*`, Kleene star `∗` and converse (Mathlib's `star`).  `RaTerm.norm` puts a term
into the following normal form, in two passes.

1. `RaTerm.convElim` pushes every converse down to the variables, using
   `star_zero`, `star_one`, `star_add`, `star_mul`, `KleeneAlgebra.star_kstar` and
   `star_star`.  After this pass the only converses left are of the shape `xᵒ` with `x` a
   variable.
2. `RaTerm.toPoly` turns the result into a *polynomial*: a list of *monomials*
   (`RaTerm.Poly = List RaTerm.Mono`, `RaTerm.Mono = List RaTerm`), read as a sum of
   products.  Sums are flattened, sorted by `RaTerm.monoCmp` and made duplicate-free;
   products are flattened; units and zeros disappear; composition is distributed over union;
   and `RaTerm.mkStar` applies `0∗ = 1`, `1∗ = 1` and `a∗∗ = a∗` to starred subterms.
   `RaTerm.polyToTerm` then reads the polynomial back as a right-associated term.

So `norm` quotients by the laws of an *idempotent semiring with an involutive,
anti-multiplicative, additive converse*, plus the three star simplifications above — exactly
the laws used in the proof of `RaTerm.eval_norm`, namely associativity, commutativity and
idempotence of `+`, neutrality of `0` for `+`, associativity of `*`, neutrality of `1` and
annihilation by `0` for `*`, distributivity of `*` over `+`, `star_zero`, `star_one`,
`star_add`, `star_mul`, `star_star`, `KleeneAlgebra.star_kstar`, `0∗ = 1`, `1∗ = 1` and
`a∗∗ = a∗`.

## What is *not* normalised

Everything that genuinely uses the Kleene-star axioms or the Boolean structure:
`(1 + a)∗ = a∗`, `a∗ * a = a * a∗`, sliding `a * (b * a)∗ = (a * b)∗ * a`, denesting
`(a + b)∗ = a∗ * (b * a∗)∗`, `(a∗ * b∗)∗ = (a + b)∗`, and anything involving `⊓`, `ᶜ`, `⊤`
or residuals — those operations are not even part of `RaTerm`, and a goal that mentions them
is reified as an opaque variable.  Starred subterms are compared syntactically *after* their
arguments have been normalised, so `(a + b)∗` and `(b + a)∗` are identified, and so are
`a∗∗ * a` and `a∗ * a`; but nothing beyond the laws listed above is applied, so for instance
`a∗ * a` and `a * a∗` are not identified.

Consequently the derived tactic `ra` is **sound but incomplete**, exactly as upstream's is:
it proves what the structural laws prove and nothing more.  In particular a failure of `ra`
says nothing about the validity of the goal.  (For the complete decision procedure of the
star fragment *without* converse, use `ka`, which rests on Kozen's completeness theorem.)

Canonicity of the normal form for the fragment listed above is *not* formally proved here —
only `RaTerm.eval_norm`, which is what makes the tactics sound.  Upstream makes the same
choice.

## References

* [D. Pous, *relation-algebra*, `theories/normalisation.v`](https://github.com/damien-pous/relation-algebra)
* [D. Pous, *Kleene Algebra with Tests and Coq Tools for While Programs*, ITP 2013]
-/

open scoped Computability

/-- Syntax of relation-algebra expressions: an idempotent semiring with converse and star. -/
inductive RaTerm : Type
  /-- The empty relation `0`. -/
  | zero
  /-- The identity relation `1`. -/
  | one
  /-- The variable with index `i`. -/
  | var (i : ℕ)
  /-- Union `a + b`. -/
  | add (a b : RaTerm)
  /-- Composition `a * b`. -/
  | mul (a b : RaTerm)
  /-- Kleene star `a∗`. -/
  | star (a : RaTerm)
  /-- Converse `aᵒ`, denoted by Mathlib's `star`. -/
  | conv (a : RaTerm)
  deriving DecidableEq, Repr, Inhabited

namespace RaTerm

/-- A *monomial*: a list of factors, read as their product (the empty list is `1`). -/
abbrev Mono : Type := List RaTerm

/-- A *polynomial*: a list of monomials, read as their sum (the empty list is `0`). -/
abbrev Poly : Type := List Mono

/-! ### Semantics -/

section Eval

variable {K : Type*} [KleeneAlgebra K] [StarRing K] (ρ : ℕ → K)

/-- Evaluate a term in a Kleene algebra with converse, under a valuation of the variables. -/
def eval : RaTerm → K
  | zero => 0
  | one => 1
  | var i => ρ i
  | add a b => eval a + eval b
  | mul a b => eval a * eval b
  | star a => (eval a)∗
  | conv a => Star.star (eval a)

@[simp] theorem eval_zero : eval ρ zero = 0 := rfl
@[simp] theorem eval_one : eval ρ one = 1 := rfl
@[simp] theorem eval_var (i : ℕ) : eval ρ (var i) = ρ i := rfl
@[simp] theorem eval_add (a b : RaTerm) : eval ρ (add a b) = eval ρ a + eval ρ b := rfl
@[simp] theorem eval_mul (a b : RaTerm) : eval ρ (mul a b) = eval ρ a * eval ρ b := rfl
@[simp] theorem eval_star (a : RaTerm) : eval ρ (star a) = (eval ρ a)∗ := rfl
@[simp] theorem eval_conv (a : RaTerm) : eval ρ (conv a) = Star.star (eval ρ a) := rfl

/-- The value of a monomial: the product of the values of its factors. -/
def evalMono : Mono → K
  | [] => 1
  | a :: m => eval ρ a * evalMono m

/-- The value of a polynomial: the sum of the values of its monomials. -/
def evalPoly : Poly → K
  | [] => 0
  | m :: p => evalMono ρ m + evalPoly p

@[simp] theorem evalMono_nil : evalMono ρ [] = 1 := rfl

@[simp] theorem evalMono_cons (a : RaTerm) (m : Mono) :
    evalMono ρ (a :: m) = eval ρ a * evalMono ρ m := rfl

@[simp] theorem evalPoly_nil : evalPoly ρ [] = 0 := rfl

@[simp] theorem evalPoly_cons (m : Mono) (p : Poly) :
    evalPoly ρ (m :: p) = evalMono ρ m + evalPoly ρ p := rfl

theorem evalMono_append (m n : Mono) :
    evalMono ρ (m ++ n) = evalMono ρ m * evalMono ρ n := by
  induction m with
  | nil => simp
  | cons a m ih => simp [ih, mul_assoc]

end Eval

/-! ### Smart constructors

Each of these applies the structural simplifications available at its head symbol. -/

/-- Smart union: `0 + b = b`, `a + 0 = a`, `a + a = a`. -/
def mkAdd (a b : RaTerm) : RaTerm :=
  match a, b with
  | zero, b => b
  | a, zero => a
  | a, b => if a = b then a else add a b

/-- Smart composition: `0 * b = a * 0 = 0`, `1 * b = b`, `a * 1 = a`. -/
def mkMul (a b : RaTerm) : RaTerm :=
  match a, b with
  | zero, _ => zero
  | _, zero => zero
  | one, b => b
  | a, one => a
  | a, b => mul a b

/-- Smart Kleene star: `0∗ = 1`, `1∗ = 1`, `a∗∗ = a∗`. -/
def mkStar : RaTerm → RaTerm
  | zero => one
  | one => one
  | star a => star a
  | a => star a

section SmartEval

variable {K : Type*} [KleeneAlgebra K] [StarRing K] (ρ : ℕ → K)

@[simp] theorem eval_mkAdd (a b : RaTerm) : eval ρ (mkAdd a b) = eval ρ a + eval ρ b := by
  unfold mkAdd
  split
  · simp
  · simp
  · split_ifs with h
    · rw [h, add_idem]
    · rfl

@[simp] theorem eval_mkMul (a b : RaTerm) : eval ρ (mkMul a b) = eval ρ a * eval ρ b := by
  unfold mkMul
  split
  · simp
  · simp
  · simp
  · simp
  · rfl

@[simp] theorem eval_mkStar (a : RaTerm) : eval ρ (mkStar a) = (eval ρ a)∗ := by
  cases a <;> simp [mkStar, kstar_one, kstar_idem]

end SmartEval

/-! ### Pushing converses to the leaves -/

/-- `convPush a` denotes the converse of `a`, with the converse pushed down to the leaves. -/
def convPush : RaTerm → RaTerm
  | zero => zero
  | one => one
  | var i => conv (var i)
  | add a b => mkAdd (convPush a) (convPush b)
  | mul a b => mkMul (convPush b) (convPush a)
  | star a => mkStar (convPush a)
  | conv a => a

/-- `convElim a` denotes `a`, with every converse pushed down to the leaves. -/
def convElim : RaTerm → RaTerm
  | zero => zero
  | one => one
  | var i => var i
  | add a b => add (convElim a) (convElim b)
  | mul a b => mul (convElim a) (convElim b)
  | star a => star (convElim a)
  | conv a => convPush (convElim a)

section ConvEval

variable {K : Type*} [KleeneAlgebra K] [StarRing K] (ρ : ℕ → K)

@[simp] theorem eval_convPush (a : RaTerm) : eval ρ (convPush a) = Star.star (eval ρ a) := by
  induction a with
  | zero => simp [convPush]
  | one => simp [convPush]
  | var i => simp [convPush]
  | add a b iha ihb => rw [convPush, eval_mkAdd, iha, ihb, eval_add, star_add]
  | mul a b iha ihb => rw [convPush, eval_mkMul, iha, ihb, eval_mul, star_mul]
  | star a ih => rw [convPush, eval_mkStar, ih, eval_star, KleeneAlgebra.star_kstar]
  | conv a => simp [convPush]

@[simp] theorem eval_convElim (a : RaTerm) : eval ρ (convElim a) = eval ρ a := by
  induction a with
  | zero => simp [convElim]
  | one => simp [convElim]
  | var i => simp [convElim]
  | add a b iha ihb => simp [convElim, iha, ihb]
  | mul a b iha ihb => simp [convElim, iha, ihb]
  | star a ih => simp [convElim, ih]
  | conv a ih => simp [convElim, ih]

end ConvEval

/-! ### Polynomials -/

/-- The index of the head constructor of a term, used to order terms. -/
def rank : RaTerm → ℕ
  | zero => 0
  | one => 1
  | var _ => 2
  | add _ _ => 3
  | mul _ _ => 4
  | star _ => 5
  | conv _ => 6

/-- A total order on terms, used to sort the monomials of a polynomial. -/
def cmp : RaTerm → RaTerm → Ordering
  | var i, var j => compare i j
  | add a b, add c d => (cmp a c).then (cmp b d)
  | mul a b, mul c d => (cmp a c).then (cmp b d)
  | star a, star b => cmp a b
  | conv a, conv b => cmp a b
  | a, b => compare a.rank b.rank

/-- The induced order on monomials: shorter monomials first, then lexicographically. -/
def monoCmp : Mono → Mono → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: m, b :: n => (cmp a b).then (monoCmp m n)

/-- Insert a monomial into a polynomial, keeping it sorted and duplicate-free. -/
def insertMono (m : Mono) : Poly → Poly
  | [] => [m]
  | n :: p =>
    if m = n then n :: p
    else
      match monoCmp m n with
      | .lt => m :: n :: p
      | _ => n :: insertMono m p

/-- Union of two polynomials. -/
def addPoly (p q : Poly) : Poly := p.foldr insertMono q

/-- Multiply a monomial into every monomial of a polynomial, on the left. -/
def mulMonoPoly (m : Mono) : Poly → Poly
  | [] => []
  | n :: q => insertMono (m ++ n) (mulMonoPoly m q)

/-- Product of two polynomials: composition is distributed over union. -/
def mulPoly (p q : Poly) : Poly :=
  p.foldr (fun m acc => addPoly (mulMonoPoly m q) acc) []

/-- Read a monomial back as a right-associated product. -/
def monoToTerm : Mono → RaTerm
  | [] => one
  | a :: m => mkMul a (monoToTerm m)

/-- Read a polynomial back as a right-associated sum. -/
def polyToTerm : Poly → RaTerm
  | [] => zero
  | m :: p => mkAdd (monoToTerm m) (polyToTerm p)

/-- Star of a polynomial: the polynomial is read back as a term and starred. -/
def starPoly (p : Poly) : Poly := [[mkStar (polyToTerm p)]]

/-- Normalise a term into a polynomial.  Converses are expected to have been pushed to the
leaves by `convElim` already; a converse of a compound term is treated as an opaque factor
(with its argument normalised), which is sound but not canonical. -/
def toPoly : RaTerm → Poly
  | zero => []
  | one => [[]]
  | var i => [[var i]]
  | add a b => addPoly (toPoly a) (toPoly b)
  | mul a b => mulPoly (toPoly a) (toPoly b)
  | star a => starPoly (toPoly a)
  | conv a => [[conv (polyToTerm (toPoly a))]]

section PolyEval

variable {K : Type*} [KleeneAlgebra K] [StarRing K] (ρ : ℕ → K)

theorem eval_monoToTerm (m : Mono) : eval ρ (monoToTerm m) = evalMono ρ m := by
  induction m with
  | nil => rw [monoToTerm, eval_one, evalMono_nil]
  | cons a m ih => rw [monoToTerm, eval_mkMul, ih, evalMono_cons]

theorem eval_polyToTerm (p : Poly) : eval ρ (polyToTerm p) = evalPoly ρ p := by
  induction p with
  | nil => rw [polyToTerm, eval_zero, evalPoly_nil]
  | cons m p ih => rw [polyToTerm, eval_mkAdd, eval_monoToTerm, ih, evalPoly_cons]

theorem evalPoly_insertMono (m : Mono) :
    ∀ p : Poly, evalPoly ρ (insertMono m p) = evalMono ρ m + evalPoly ρ p
  | [] => by rw [insertMono, evalPoly_cons, evalPoly_nil]
  | n :: p => by
    have ih := evalPoly_insertMono m p
    rw [insertMono]
    split_ifs with h
    · rw [h, evalPoly_cons, ← add_assoc, add_idem]
    · split
      · rfl
      all_goals rw [evalPoly_cons, ih, evalPoly_cons, add_left_comm]

theorem evalPoly_addPoly (p q : Poly) :
    evalPoly ρ (addPoly p q) = evalPoly ρ p + evalPoly ρ q := by
  induction p with
  | nil => simp [addPoly]
  | cons m p ih => rw [addPoly, List.foldr_cons, evalPoly_insertMono, ← addPoly, ih,
      evalPoly_cons, add_assoc]

theorem evalPoly_mulMonoPoly (m : Mono) :
    ∀ q : Poly, evalPoly ρ (mulMonoPoly m q) = evalMono ρ m * evalPoly ρ q
  | [] => by simp [mulMonoPoly]
  | n :: q => by
    rw [mulMonoPoly, evalPoly_insertMono, evalMono_append, evalPoly_mulMonoPoly m q,
      evalPoly_cons, mul_add]

theorem evalPoly_mulPoly (p q : Poly) :
    evalPoly ρ (mulPoly p q) = evalPoly ρ p * evalPoly ρ q := by
  induction p with
  | nil => simp [mulPoly]
  | cons m p ih => rw [mulPoly, List.foldr_cons, evalPoly_addPoly, evalPoly_mulMonoPoly,
      ← mulPoly, ih, evalPoly_cons, add_mul]

theorem evalPoly_starPoly (p : Poly) : evalPoly ρ (starPoly p) = (evalPoly ρ p)∗ := by
  rw [starPoly, evalPoly_cons, evalPoly_nil, evalMono_cons, evalMono_nil, eval_mkStar,
    eval_polyToTerm, mul_one, add_zero]

theorem evalPoly_toPoly (a : RaTerm) : evalPoly ρ (toPoly a) = eval ρ a := by
  induction a with
  | zero => simp [toPoly]
  | one => simp [toPoly]
  | var i => simp [toPoly]
  | add a b iha ihb => rw [toPoly, evalPoly_addPoly, iha, ihb, eval_add]
  | mul a b iha ihb => rw [toPoly, evalPoly_mulPoly, iha, ihb, eval_mul]
  | star a ih => rw [toPoly, evalPoly_starPoly, ih, eval_star]
  | conv a ih => rw [toPoly, evalPoly_cons, evalPoly_nil, evalMono_cons, evalMono_nil,
      eval_conv, eval_polyToTerm, ih, mul_one, add_zero, eval_conv]

end PolyEval

/-! ### The normalisation functions and their correctness -/

/-- The normal form of a term: converses are pushed to the leaves, then the term is put in
sum-of-products form (see the module docstring for the exact list of laws applied). -/
def norm (e : RaTerm) : RaTerm := polyToTerm (toPoly (convElim e))

/-- A lighter cleanup than `norm`: units and zeros are removed, `0∗` and `1∗` become `1`,
`a∗∗` becomes `a∗`, and converses are pushed to the leaves.  Sums are *not* sorted and
composition is *not* distributed over union. -/
def simplify : RaTerm → RaTerm
  | zero => zero
  | one => one
  | var i => var i
  | add a b => mkAdd (simplify a) (simplify b)
  | mul a b => mkMul (simplify a) (simplify b)
  | star a => mkStar (simplify a)
  | conv a => convPush (simplify a)

/-- Syntactic equality of normal forms, as a `Bool`. -/
def normEq (e f : RaTerm) : Bool := norm e == norm f

/-- The test used for inequalities: `e ≤ f` is checked as `e + f = f`. -/
def normLe (e f : RaTerm) : Bool := normEq (add e f) f

section Correct

variable {K : Type*} [KleeneAlgebra K] [StarRing K]

/-- **Correctness of the normalisation procedure**: a term and its normal form have the same
value in every Kleene algebra with converse.  This is what makes `ra`, `ra_normalise` and
`ra_simpl` sound. -/
theorem eval_norm (ρ : ℕ → K) (e : RaTerm) : (e.norm).eval ρ = e.eval ρ := by
  rw [norm, eval_polyToTerm, evalPoly_toPoly, eval_convElim]

/-- Correctness of the light cleanup `simplify`. -/
theorem eval_simplify (ρ : ℕ → K) (e : RaTerm) : (e.simplify).eval ρ = e.eval ρ := by
  induction e with
  | zero => simp [simplify]
  | one => simp [simplify]
  | var i => simp [simplify]
  | add a b iha ihb => rw [simplify, eval_mkAdd, iha, ihb, eval_add]
  | mul a b iha ihb => rw [simplify, eval_mkMul, iha, ihb, eval_mul]
  | star a ih => rw [simplify, eval_mkStar, ih, eval_star]
  | conv a ih => rw [simplify, eval_convPush, ih, eval_conv]

/-- Terms with the same normal form have the same value. -/
theorem eval_eq_of_normEq {e f : RaTerm} (h : norm e = norm f) (ρ : ℕ → K) :
    eval ρ e = eval ρ f := by
  rw [← eval_norm ρ e, ← eval_norm ρ f, h]

/-- The `Bool`-valued version of `eval_eq_of_normEq`, for use by the `ra` tactic. -/
theorem eval_eq_of_normEq' {e f : RaTerm} (h : normEq e f = true) (ρ : ℕ → K) :
    eval ρ e = eval ρ f :=
  eval_eq_of_normEq (by simpa [normEq] using h) ρ

/-- If `e + f` and `f` have the same normal form, then `e ≤ f`. -/
theorem eval_le_of_normLe {e f : RaTerm} (h : norm (add e f) = norm f) (ρ : ℕ → K) :
    eval ρ e ≤ eval ρ f := by
  have := eval_eq_of_normEq h ρ
  rw [eval_add] at this
  exact add_eq_right_iff_le.1 this

/-- The `Bool`-valued version of `eval_le_of_normLe`, for use by the `ra` tactic. -/
theorem eval_le_of_normLe' {e f : RaTerm} (h : normLe e f = true) (ρ : ℕ → K) :
    eval ρ e ≤ eval ρ f :=
  eval_le_of_normLe (by simpa [normLe, normEq] using h) ρ

end Correct

end RaTerm
