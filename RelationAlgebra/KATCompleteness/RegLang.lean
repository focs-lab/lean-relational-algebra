import RelationAlgebra.Decide.KACompleteness

/-!
# The Kleene algebra of regular languages, and its interpretation in any Kleene algebra

`RegLang` is the sub-Kleene-algebra of `Language ℕ` consisting of the languages denoted by a
regular expression, i.e. by a `KleeneAlgebra.Term`.

Its point is `RegLang.interp`: for every Kleene algebra `K` and valuation `ρ : ℕ → K` there is a
**Kleene algebra homomorphism** `RegLang → K` sending the language of a term to the value of
that term.  This map is well defined precisely because of Kozen's completeness theorem
(`KleeneAlgebra.Term.completeness_eq`): two terms with the same language have the same value in
every Kleene algebra.

This is the device that lets the completeness proof for Kleene algebra with tests be carried out
semantically, with no syntax for matrices: matrices over `RegLang` may be manipulated with the
ordinary matrix Kleene algebra, and `interp` transports the result into `K`.
-/

open scoped Computability

namespace RelationAlgebra

/-- A regular language over `ℕ`: one denoted by some `KleeneAlgebra.Term`. -/
def RegLang : Type := {L : Language ℕ // ∃ e : KleeneAlgebra.Term, e.lang = L}

namespace RegLang

/-- The underlying language. -/
def toLang (L : RegLang) : Language ℕ := L.1

theorem toLang_injective : Function.Injective toLang := Subtype.val_injective

@[ext] theorem ext {L M : RegLang} (h : L.toLang = M.toLang) : L = M := toLang_injective h

/-- The regular language of a term. -/
def ofTerm (e : KleeneAlgebra.Term) : RegLang := ⟨e.lang, e, rfl⟩

@[simp] theorem toLang_ofTerm (e : KleeneAlgebra.Term) : (ofTerm e).toLang = e.lang := rfl

theorem exists_term (L : RegLang) : ∃ e : KleeneAlgebra.Term, ofTerm e = L := by
  obtain ⟨L, e, he⟩ := L
  exact ⟨e, Subtype.ext he⟩

/-- A term denoting a given regular language. -/
noncomputable def term (L : RegLang) : KleeneAlgebra.Term := (exists_term L).choose

@[simp] theorem ofTerm_term (L : RegLang) : ofTerm L.term = L := (exists_term L).choose_spec

@[simp] theorem lang_term (L : RegLang) : L.term.lang = L.toLang :=
  congrArg toLang (ofTerm_term L)

/-! ### Terms for the auxiliary operations -/

/-- A term denoting `n • e`. -/
def nsmulTerm : ℕ → KleeneAlgebra.Term → KleeneAlgebra.Term
  | 0, _ => .zero
  | n + 1, e => .add (nsmulTerm n e) e

/-- A term denoting `e ^ n`. -/
def npowTerm : ℕ → KleeneAlgebra.Term → KleeneAlgebra.Term
  | 0, _ => .one
  | n + 1, e => .mul (npowTerm n e) e

/-- A term denoting the natural number `n`. -/
def natCastTerm : ℕ → KleeneAlgebra.Term
  | 0 => .zero
  | n + 1 => .add (natCastTerm n) .one

@[simp] theorem lang_nsmulTerm (n : ℕ) (e : KleeneAlgebra.Term) :
    (nsmulTerm n e).lang = n • e.lang := by
  induction n with
  | zero => simp [nsmulTerm]
  | succ n ih => rw [nsmulTerm, KleeneAlgebra.Term.lang_add, ih, succ_nsmul]

@[simp] theorem lang_npowTerm (n : ℕ) (e : KleeneAlgebra.Term) :
    (npowTerm n e).lang = e.lang ^ n := by
  induction n with
  | zero => simp [npowTerm]
  | succ n ih => rw [npowTerm, KleeneAlgebra.Term.lang_mul, ih, pow_succ]

@[simp] theorem lang_natCastTerm (n : ℕ) : (natCastTerm n).lang = (n : Language ℕ) := by
  induction n with
  | zero => simp [natCastTerm]
  | succ n ih =>
    rw [natCastTerm, KleeneAlgebra.Term.lang_add, ih, KleeneAlgebra.Term.lang_one,
      Nat.cast_succ]

/-! ### The Kleene algebra structure -/

instance : Zero RegLang := ⟨ofTerm .zero⟩
instance : One RegLang := ⟨ofTerm .one⟩
instance : Add RegLang :=
  ⟨fun L M => ⟨L.toLang + M.toLang, L.term.add M.term, by simp⟩⟩
instance : Mul RegLang :=
  ⟨fun L M => ⟨L.toLang * M.toLang, L.term.mul M.term, by simp⟩⟩
instance : KStar RegLang := ⟨fun L => ⟨L.toLang∗, L.term.star, by simp⟩⟩
instance : LE RegLang := ⟨fun L M => L.toLang ≤ M.toLang⟩
instance : LT RegLang := ⟨fun L M => L.toLang < M.toLang⟩
instance : Max RegLang := ⟨fun L M => L + M⟩
instance : Bot RegLang := ⟨0⟩
instance : SMul ℕ RegLang := ⟨fun n L => ⟨n • L.toLang, nsmulTerm n L.term, by simp⟩⟩
instance : Pow RegLang ℕ := ⟨fun L n => ⟨L.toLang ^ n, npowTerm n L.term, by simp⟩⟩
instance : NatCast RegLang := ⟨fun n => ⟨(n : Language ℕ), natCastTerm n, by simp⟩⟩

@[simp] theorem toLang_zero : (0 : RegLang).toLang = 0 := rfl
@[simp] theorem toLang_one : (1 : RegLang).toLang = 1 := rfl
@[simp] theorem toLang_add (L M : RegLang) : (L + M).toLang = L.toLang + M.toLang := rfl
@[simp] theorem toLang_mul (L M : RegLang) : (L * M).toLang = L.toLang * M.toLang := rfl
@[simp] theorem toLang_kstar (L : RegLang) : (L∗).toLang = L.toLang∗ := rfl
@[simp] theorem toLang_sup (L M : RegLang) : (L ⊔ M).toLang = L.toLang ⊔ M.toLang := by
  change (L + M).toLang = _
  rw [toLang_add, add_eq_sup]
@[simp] theorem toLang_bot : (⊥ : RegLang).toLang = ⊥ := rfl
theorem toLang_le {L M : RegLang} : L.toLang ≤ M.toLang ↔ L ≤ M := Iff.rfl
theorem toLang_lt {L M : RegLang} : L.toLang < M.toLang ↔ L < M := Iff.rfl
@[simp] theorem toLang_nsmul (n : ℕ) (L : RegLang) : (n • L).toLang = n • L.toLang := rfl
@[simp] theorem toLang_pow (L : RegLang) (n : ℕ) : (L ^ n).toLang = L.toLang ^ n := rfl
@[simp] theorem toLang_natCast (n : ℕ) : ((n : RegLang)).toLang = (n : Language ℕ) := rfl

noncomputable instance instKleeneAlgebra : KleeneAlgebra RegLang :=
  toLang_injective.kleeneAlgebra toLang toLang_le toLang_lt rfl rfl
    toLang_add toLang_mul toLang_nsmul toLang_pow toLang_natCast toLang_sup toLang_bot
    toLang_kstar

/-! ### Interpretation in an arbitrary Kleene algebra -/

section Interp

variable {K : Type*} [KleeneAlgebra K] (ρ : ℕ → K)

/-- The value of a regular language in a Kleene algebra: the value of any term denoting it.
This is well defined **because of Kozen's completeness theorem**: two terms with the same
language have the same value in every Kleene algebra. -/
noncomputable def interp (L : RegLang) : K := L.term.eval ρ

@[simp] theorem interp_ofTerm (e : KleeneAlgebra.Term) : interp ρ (ofTerm e) = e.eval ρ :=
  KleeneAlgebra.Term.completeness_eq (by simp) ρ

theorem ofTerm_term_add (L M : RegLang) : L + M = ofTerm (L.term.add M.term) := by
  ext
  simp

theorem ofTerm_term_mul (L M : RegLang) : L * M = ofTerm (L.term.mul M.term) := by
  ext
  simp

theorem ofTerm_term_kstar (L : RegLang) : L∗ = ofTerm L.term.star := by
  ext
  simp

@[simp] theorem interp_zero : interp ρ (0 : RegLang) = 0 := by
  change interp ρ (ofTerm .zero) = _
  simp [KleeneAlgebra.Term.eval]

@[simp] theorem interp_one : interp ρ (1 : RegLang) = 1 := by
  change interp ρ (ofTerm .one) = _
  simp [KleeneAlgebra.Term.eval]

@[simp] theorem interp_add (L M : RegLang) : interp ρ (L + M) = interp ρ L + interp ρ M := by
  rw [ofTerm_term_add, interp_ofTerm]
  rfl

@[simp] theorem interp_mul (L M : RegLang) : interp ρ (L * M) = interp ρ L * interp ρ M := by
  rw [ofTerm_term_mul, interp_ofTerm]
  rfl

@[simp] theorem interp_kstar (L : RegLang) : interp ρ (L∗) = (interp ρ L)∗ := by
  rw [ofTerm_term_kstar, interp_ofTerm]
  rfl

theorem interp_mono {L M : RegLang} (h : L ≤ M) : interp ρ L ≤ interp ρ M := by
  have hadd : L + M = M := add_eq_right_iff_le.2 h
  have := interp_add ρ L M
  rw [hadd] at this
  exact add_eq_right_iff_le.1 this.symm

end Interp

end RegLang

end RelationAlgebra
