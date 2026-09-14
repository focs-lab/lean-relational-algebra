import RelationAlgebra.Kleene.Complete

/-!
# Regular expressions as terms of Kleene algebra

`KleeneAlgebra.Term` is the syntax of Kleene algebra over variables `ℕ`.  A term can be
evaluated in any Kleene algebra (`Term.eval`), and in particular in the Kleene algebra of
languages over the alphabet `ℕ`, which gives its *language* (`Term.lang`).

The main theorem `Term.eval_eq_of_lang_eq` says that in a *complete* Kleene algebra
(`CompleteKleeneAlgebra`), two terms with the same language evaluate to the same element, for
every valuation of the variables.  This is the (easy) soundness half of Kozen's completeness
theorem, restricted to star-continuous algebras such as relations and languages; it is what
makes the `ka` tactic sound.
-/

open scoped Computability

namespace KleeneAlgebra

/-- Terms of Kleene algebra (regular expressions) over variables indexed by `ℕ`. -/
inductive Term : Type
  | zero : Term
  | one : Term
  | var : ℕ → Term
  | add : Term → Term → Term
  | mul : Term → Term → Term
  | star : Term → Term
  deriving DecidableEq, Repr, Inhabited

namespace Term

variable {K : Type*}

/-- Evaluate a term in a Kleene algebra under a valuation of the variables. -/
def eval [KleeneAlgebra K] (ρ : ℕ → K) : Term → K
  | zero => 0
  | one => 1
  | var i => ρ i
  | add a b => eval ρ a + eval ρ b
  | mul a b => eval ρ a * eval ρ b
  | star a => (eval ρ a)∗

/-- The language of a term: the regular language over `ℕ` it denotes. -/
def lang : Term → Language ℕ := eval fun i ↦ {[i]}

@[simp] theorem lang_zero : lang zero = 0 := rfl
@[simp] theorem lang_one : lang one = 1 := rfl
@[simp] theorem lang_var (i : ℕ) : lang (var i) = {[i]} := rfl
@[simp] theorem lang_add (a b : Term) : lang (add a b) = lang a + lang b := rfl
@[simp] theorem lang_mul (a b : Term) : lang (mul a b) = lang a * lang b := rfl
@[simp] theorem lang_star (a : Term) : lang (star a) = (lang a)∗ := rfl

section Sound

variable [CompleteKleeneAlgebra K] (ρ : ℕ → K)

/-- The value of a word: the product of the values of its letters. -/
def evalWord (w : List ℕ) : K := (w.map ρ).prod

@[simp] theorem evalWord_nil : evalWord ρ [] = 1 := rfl

@[simp] theorem evalWord_singleton (i : ℕ) : evalWord ρ [i] = ρ i := by
  simp [evalWord]

theorem evalWord_append (u v : List ℕ) : evalWord ρ (u ++ v) = evalWord ρ u * evalWord ρ v := by
  simp [evalWord]

/-- The join of the values of the words of a language. -/
def langSup (L : Language ℕ) : K := ⨆ w ∈ L, evalWord ρ w

theorem langSup_mono {L M : Language ℕ} (h : L ≤ M) : langSup ρ L ≤ langSup ρ M :=
  iSup₂_le fun w hw ↦ le_iSup₂_of_le w (h hw) le_rfl

theorem mem_singleton_lang {x y : List ℕ} : x ∈ ({y} : Language ℕ) ↔ x = y := Iff.rfl

theorem not_mem_zero_lang (x : List ℕ) : x ∉ (0 : Language ℕ) := fun h ↦ h

@[simp] theorem langSup_zero : langSup ρ 0 = 0 := by
  simp [langSup, CompleteKleeneAlgebra.bot_eq_zero, iSup_const]

@[simp] theorem langSup_one : langSup ρ 1 = 1 := by
  simp [langSup, Language.mem_one]

@[simp] theorem langSup_singleton (i : ℕ) : langSup ρ {[i]} = ρ i := by
  simp [langSup, mem_singleton_lang]

theorem langSup_add (L M : Language ℕ) : langSup ρ (L + M) = langSup ρ L + langSup ρ M := by
  simp only [langSup, add_eq_sup]
  exact iSup_union

theorem langSup_mul (L M : Language ℕ) : langSup ρ (L * M) = langSup ρ L * langSup ρ M := by
  apply le_antisymm
  · refine iSup₂_le fun w hw ↦ ?_
    obtain ⟨u, hu, v, hv, rfl⟩ := Language.mem_mul.1 hw
    rw [evalWord_append]
    exact mul_le_mul' (le_iSup₂_of_le u hu le_rfl) (le_iSup₂_of_le v hv le_rfl)
  · unfold langSup
    rw [CompleteKleeneAlgebra.iSup_mul]
    refine iSup_le fun u ↦ ?_
    rw [CompleteKleeneAlgebra.iSup_mul]
    refine iSup_le fun hu ↦ ?_
    rw [CompleteKleeneAlgebra.mul_iSup]
    refine iSup_le fun v ↦ ?_
    rw [CompleteKleeneAlgebra.mul_iSup]
    refine iSup_le fun hv ↦ ?_
    rw [← evalWord_append]
    exact le_iSup₂_of_le (u ++ v) (Language.mem_mul.2 ⟨u, hu, v, hv, rfl⟩) le_rfl

theorem langSup_iSup {ι : Sort*} (L : ι → Language ℕ) :
    langSup ρ (⨆ i, L i) = ⨆ i, langSup ρ (L i) := by
  apply le_antisymm
  · refine iSup₂_le fun w hw ↦ ?_
    obtain ⟨i, hi⟩ := Language.mem_iSup.1 hw
    exact le_iSup_of_le i (le_iSup₂_of_le w hi le_rfl)
  · exact iSup_le fun i ↦ iSup₂_le fun w hw ↦ le_iSup₂_of_le w (Language.mem_iSup.2 ⟨i, hw⟩) le_rfl

theorem langSup_pow (L : Language ℕ) (n : ℕ) : langSup ρ (L ^ n) = langSup ρ L ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, langSup_mul, ih]

theorem langSup_kstar (L : Language ℕ) : langSup ρ L∗ = (langSup ρ L)∗ := by
  rw [Language.kstar_eq_iSup_pow, CompleteKleeneAlgebra.kstar_eq_iSup_pow, langSup_iSup]
  simp only [langSup_pow]

/-- A term evaluates to the join of the values of the words of its language. -/
theorem eval_eq_langSup (e : Term) : eval ρ e = langSup ρ (lang e) := by
  induction e with
  | zero => simp [eval]
  | one => simp [eval]
  | var i => simp [eval]
  | add a b iha ihb => rw [eval, iha, ihb, lang_add, langSup_add]
  | mul a b iha ihb => rw [eval, iha, ihb, lang_mul, langSup_mul]
  | star a ih => rw [eval, ih, lang_star, langSup_kstar]

/-- **Soundness**: terms with the same language are equal in every complete Kleene algebra. -/
theorem eval_eq_of_lang_eq {e f : Term} (h : lang e = lang f) : eval ρ e = eval ρ f := by
  rw [eval_eq_langSup, eval_eq_langSup, h]

theorem eval_le_of_lang_le {e f : Term} (h : lang e ≤ lang f) : eval ρ e ≤ eval ρ f := by
  rw [eval_eq_langSup, eval_eq_langSup]
  exact langSup_mono ρ h

end Sound

end Term

end KleeneAlgebra
