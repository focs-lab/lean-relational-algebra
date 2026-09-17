import RelationAlgebra.Examples.Imp
import RelationAlgebra.Decide.HKATTactic

/-!
# The assignment model for Paterson's flowcharts

This follows Damien Pous's `examples/paterson.v` at revision
`2d2af3631929399bbac56f57b3e15302d8697e1c`. A state has four temporary locations and one
input/output location. The interpretations of `f`, `g`, and `P` are arbitrary.

We work directly in the existing relational KAT. The syntax below is used to compute
substitution and to erase assignments to unread variables, with proved semantic laws.
-/

open scoped Computability SetRel KAT

namespace Paterson

/-- Four work variables and the input/output cell. -/
inductive Loc | y1 | y2 | y3 | y4 | io deriving DecidableEq

/-- A natural-valued store, as in Pous's formalization. -/
abbrev State := Loc → ℕ

/-- An interpretation of the uninterpreted function and predicate symbols. -/
structure Interpretation where
  f : ℕ → ℕ
  g : ℕ → ℕ → ℕ
  p : ℕ → Bool

/-- Arithmetic expressions over the five locations. -/
inductive AExpr
  | var : Loc → AExpr
  | zero : AExpr
  | f : AExpr → AExpr
  | g : AExpr → AExpr → AExpr

/-- Boolean expressions used at branch points. -/
inductive BExpr
  | pred : AExpr → BExpr
  | top | bot
  | and : BExpr → BExpr → BExpr
  | or : BExpr → BExpr → BExpr
  | not : BExpr → BExpr

namespace AExpr

def eval (M : Interpretation) (s : State) : AExpr → ℕ
  | .var x => s x
  | .zero => 0
  | .f e => M.f (eval M s e)
  | .g e d => M.g (eval M s e) (eval M s d)

/-- Whether the expression avoids reading a given location. -/
def free (x : Loc) : AExpr → Bool
  | .var y => decide (x ≠ y)
  | .zero => true
  | .f e => free x e
  | .g e d => free x e && free x d

def subst (x : Loc) (v : AExpr) : AExpr → AExpr
  | .var y => if x = y then v else .var y
  | .zero => .zero
  | .f e => .f (subst x v e)
  | .g e d => .g (subst x v e) (subst x v d)

theorem subst_free (x : Loc) (v e : AExpr) (h : e.free x = true) : AExpr.subst x v e = e := by
  induction e with
  | var y =>
    have hxy : x ≠ y := of_decide_eq_true h
    simp [subst, hxy]
  | zero => rfl
  | f e ih => simp only [subst, ih h]
  | g e f he hf =>
    obtain ⟨he', hf'⟩ := Bool.and_eq_true_iff.mp h
    simp only [subst, he he', hf hf']

theorem free_subst (x : Loc) (v e : AExpr) (h : v.free x = true) :
    (AExpr.subst x v e).free x = true := by
  induction e with
  | var y =>
    by_cases hh : x = y
    · subst y; simpa [subst] using h
    · simp [subst, free, hh]
  | zero => rfl
  | f e ih => exact ih
  | g e f he hf => simp [subst, free, he, hf]

end AExpr

namespace BExpr

def eval (M : Interpretation) (s : State) : BExpr → Bool
  | .pred e => M.p (e.eval M s)
  | .top => true
  | .bot => false
  | .and b c => eval M s b && eval M s c
  | .or b c => eval M s b || eval M s c
  | .not b => !(eval M s b)

def free (x : Loc) : BExpr → Bool
  | .pred e => e.free x
  | .top | .bot => true
  | .and b c | .or b c => free x b && free x c
  | .not b => free x b

def subst (x : Loc) (v : AExpr) : BExpr → BExpr
  | .pred e => .pred (AExpr.subst x v e)
  | .top => .top
  | .bot => .bot
  | .and b c => .and (subst x v b) (subst x v c)
  | .or b c => .or (subst x v b) (subst x v c)
  | .not b => .not (subst x v b)

theorem subst_free (x : Loc) (v : AExpr) (b : BExpr) (h : b.free x = true) :
    b.subst x v = b := by
  induction b with
  | pred e => simp only [subst, AExpr.subst_free x v e h]
  | top => rfl
  | bot => rfl
  | and b c hb hc | or b c hb hc =>
    obtain ⟨hb', hc'⟩ := Bool.and_eq_true_iff.mp h
    simp only [subst, hb hb', hc hc']
  | not b hb => simp only [subst, hb h]

/-- A Boolean expression denotes a test in the relational model. -/
def denote (M : Interpretation) (b : BExpr) : Set State := {s | b.eval M s = true}

@[simp] theorem denote_top (M : Interpretation) : top.denote M = ⊤ := by
  ext s; simp [denote, eval]

@[simp] theorem denote_bot (M : Interpretation) : bot.denote M = ⊥ := by
  ext s; simp [denote, eval]

@[simp] theorem denote_and (M : Interpretation) (b c : BExpr) :
    (and b c).denote M = b.denote M ⊓ c.denote M := by
  ext s; simp [denote, eval]

@[simp] theorem denote_or (M : Interpretation) (b c : BExpr) :
    (or b c).denote M = b.denote M ⊔ c.denote M := by
  ext s; simp [denote, eval]

@[simp] theorem denote_not (M : Interpretation) (b : BExpr) :
    (not b).denote M = (b.denote M)ᶜ := by
  ext s; simp [denote, eval]

end BExpr

/-- Updating a cell after evaluating its right-hand side in the old state. -/
def update (M : Interpretation) (x : Loc) (e : AExpr) (s : State) : State :=
  Function.update s x (e.eval M s)

/-- The graph of a deterministic store operation, oriented in execution order. -/
def graph (f : State → State) : SetRel State State := {st | st.2 = f st.1}

@[simp] theorem graph_mul (f g : State → State) : graph f * graph g = graph (g ∘ f) := by
  ext ⟨s, t⟩
  change (∃ u, u = f s ∧ t = g u) ↔ t = g (f s)
  simp

/-- Assignment interpreted in the existing relational KAT. -/
def assign (M : Interpretation) (x : Loc) (e : AExpr) : SetRel State State :=
  graph (update M x e)

@[simp] theorem eval_update (M : Interpretation) (x : Loc) (v e : AExpr) (s : State) :
    e.eval M (update M x v s) = (AExpr.subst x v e).eval M s := by
  induction e with
  | var y =>
    by_cases h : x = y
    · subst y; simp [AExpr.eval, AExpr.subst, update]
    · simp [AExpr.eval, AExpr.subst, update, h, Ne.symm h]
  | zero => rfl
  | f e ih => simp only [AExpr.eval, AExpr.subst, ih]
  | g e f he hf => simp only [AExpr.eval, AExpr.subst, he, hf]

@[simp] theorem eval_update_test (M : Interpretation) (x : Loc) (v : AExpr) (b : BExpr)
    (s : State) : b.eval M (update M x v s) = (b.subst x v).eval M s := by
  induction b <;> simp_all [BExpr.eval, BExpr.subst]

/-- Sequential assignments to one cell collapse by substitution (Angus–Kozen (8)). -/
theorem assign_assign (M : Interpretation) (x : Loc) (e f : AExpr) :
    assign M x e * assign M x f = assign M x (AExpr.subst x e f) := by
  rw [assign, assign, graph_mul]
  congr 1
  funext s
  change Function.update (Function.update s x (e.eval M s)) x
    (f.eval M (update M x e s)) = Function.update s x ((AExpr.subst x e f).eval M s)
  rw [eval_update, Function.update_idem]

/-- Substitute the first assignment into a later right-hand side (Angus–Kozen (7)). -/
theorem assign_subst (M : Interpretation) (x y : Loc) (e f : AExpr)
    (he : e.free x = true) :
    assign M x e * assign M y f = assign M x e * assign M y (AExpr.subst x e f) := by
  simp only [assign, graph_mul]
  congr 1
  funext s
  change Function.update (update M x e s) y (f.eval M (update M x e s)) =
    Function.update (update M x e s) y ((AExpr.subst x e f).eval M (update M x e s))
  rw [eval_update, eval_update, AExpr.subst_free x e _ (AExpr.free_subst x e f he)]

/-- Reordering independent assignments (Angus–Kozen (6)). -/
theorem assign_swap (M : Interpretation) (x y : Loc) (e f : AExpr)
    (hxy : x ≠ y) (he : e.free y = true) :
    assign M x e * assign M y f = assign M y (AExpr.subst x e f) * assign M x e := by
  simp only [assign, graph_mul]
  congr 1
  funext s
  change Function.update (Function.update s x (e.eval M s)) y
    (f.eval M (update M x e s)) = Function.update (Function.update s y
    ((AExpr.subst x e f).eval M s)) x (e.eval M (update M y (AExpr.subst x e f) s))
  rw [eval_update, eval_update, AExpr.subst_free y _ _ he]
  exact Function.update_comm hxy _ _ _

/-- Two assignments commute when neither reads the cell written by the other. -/
theorem assign_comm (M : Interpretation) (x y : Loc) (e f : AExpr)
    (hxy : x ≠ y) (he : e.free y = true) (hf : f.free x = true) :
    assign M x e * assign M y f = assign M y f * assign M x e := by
  rw [assign_swap M x y e f hxy he, AExpr.subst_free x e f hf]

/-- Moving a test through an assignment substitutes its expression (Angus–Kozen (9)). -/
theorem test_assign (M : Interpretation) (x : Loc) (e : AExpr) (b : BExpr) :
    (⌜(b.subst x e).denote M⌝ : SetRel State State) * assign M x e =
      assign M x e * ⌜b.denote M⌝ := by
  ext ⟨s, t⟩
  simp only [IMP.mem_test_mul, IMP.mem_mul_test]
  change ((b.subst x e).eval M s = true ∧ t = update M x e s) ↔
    (t = update M x e s ∧ b.eval M t = true)
  constructor
  · rintro ⟨hb, rfl⟩
    exact ⟨rfl, by rwa [eval_update_test]⟩
  · rintro ⟨rfl, hb⟩
    exact ⟨by rwa [eval_update_test] at hb, rfl⟩

/-- An assignment commutes with every test that does not read its target cell. -/
theorem test_assign_comm (M : Interpretation) (x : Loc) (e : AExpr) (b : BExpr)
    (h : b.free x = true) :
    (⌜b.denote M⌝ : SetRel State State) * assign M x e = assign M x e * ⌜b.denote M⌝ := by
  rw [← test_assign, BExpr.subst_free x e b h]

/-- If an update makes two tests agree, their disagreement afterwards is impossible. -/
theorem same_value (f : State → State) (a b : Set State)
    (h : ∀ s, f s ∈ a ↔ f s ∈ b) :
    graph f * ⌜a ⊓ bᶜ ⊔ aᶜ ⊓ b⌝ ≤ (0 : SetRel State State) := by
  intro ⟨s, t⟩ hst
  obtain ⟨hst', ht⟩ := IMP.mem_mul_test.mp hst
  change t = f s at hst'
  subst t
  change (f s ∈ a ∧ f s ∉ b) ∨ (f s ∉ a ∧ f s ∈ b) at ht
  rcases ht with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact hb ((h s).mp ha)
  · exact ha ((h s).mpr hb)

/-- Regular program syntax, used only for verified dead-store elimination. -/
inductive Prog
  | test : BExpr → Prog
  | assign : Loc → AExpr → Prog
  | seq : Prog → Prog → Prog
  | choice : Prog → Prog → Prog
  | star : Prog → Prog

namespace Prog

def denote (M : Interpretation) : Prog → SetRel State State
  | .test b => ⌜b.denote M⌝
  | .assign x e => Paterson.assign M x e
  | .seq p q => denote M p * denote M q
  | .choice p q => denote M p + denote M q
  | .star p => (denote M p)∗

/-- Whether a program never reads a location, including in its tests. -/
def dontRead (y : Loc) : Prog → Bool
  | .test b => b.free y
  | .assign _ e => e.free y
  | .seq p q | .choice p q => dontRead y p && dontRead y q
  | .star p => dontRead y p

/-- Remove writes to a location. The correctness theorem requires it to be unread. -/
def gc (y : Loc) : Prog → Prog
  | .test b => .test b
  | .assign x e => if x = y then .test .top else .assign x e
  | .seq p q => .seq (gc y p) (gc y q)
  | .choice p q => .choice (gc y p) (gc y q)
  | .star p => .star (gc y p)

private theorem gc_invariants (M : Interpretation) (y : Loc) (p : Prog)
    (h : p.dontRead y = true) :
    (p.gc y).denote M * Paterson.assign M y .zero = Paterson.assign M y .zero * (p.gc y).denote M ∧
    p.denote M * Paterson.assign M y .zero = Paterson.assign M y .zero * (p.gc y).denote M := by
  induction p with
  | test b =>
    exact ⟨test_assign_comm M y .zero b h, test_assign_comm M y .zero b h⟩
  | assign x e =>
    by_cases hxy : x = y
    · subst x
      simp only [gc, ↓reduceIte, denote]
      have ht : (⌜BExpr.top.denote M⌝ : SetRel State State) = 1 := by
        have hb : BExpr.top.denote M = ⊤ := by ext s; simp [BExpr.denote, BExpr.eval]
        rw [hb, KAT.test_top]
      rw [ht, one_mul, mul_one, assign_assign]
      exact ⟨rfl, rfl⟩
    · simp only [gc, hxy, ↓reduceIte, denote]
      exact ⟨assign_comm M x y e .zero hxy h rfl,
        assign_comm M x y e .zero hxy h rfl⟩
  | seq p q hp hq =>
    obtain ⟨hp', hq'⟩ := Bool.and_eq_true_iff.mp h
    obtain ⟨hp1, hp2⟩ := hp hp'
    obtain ⟨hq1, hq2⟩ := hq hq'
    simp only [gc, denote]
    constructor
    · rw [mul_assoc, hq1, ← mul_assoc, hp1, mul_assoc]
    · rw [mul_assoc, hq2, ← mul_assoc, hp2, mul_assoc]
  | choice p q hp hq =>
    obtain ⟨hp', hq'⟩ := Bool.and_eq_true_iff.mp h
    obtain ⟨hp1, hp2⟩ := hp hp'
    obtain ⟨hq1, hq2⟩ := hq hq'
    simp only [gc, denote, add_mul, mul_add, hp1, hp2, hq1, hq2, and_self]
  | star p hp =>
    obtain ⟨hp1, hp2⟩ := hp h
    exact ⟨KleeneAlgebra.kstar_mul_eq_mul_kstar_of_eq hp1,
      KleeneAlgebra.kstar_mul_eq_mul_kstar_of_eq hp2⟩

/-- Angus–Kozen Lemma 4.5: writes to an unread variable are irrelevant if it is
cleared afterwards. Both sides include the final clearing assignment. -/
theorem gc_correct (M : Interpretation) (y : Loc) (p : Prog)
    (h : p.dontRead y = true) :
    (p.gc y).denote M * Paterson.assign M y .zero = p.denote M * Paterson.assign M y .zero := by
  obtain ⟨h1, h2⟩ := gc_invariants M y p h
  exact h1.trans h2.symm

end Prog
end Paterson
