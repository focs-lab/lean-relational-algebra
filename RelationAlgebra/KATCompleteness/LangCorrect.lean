import RelationAlgebra.KATCompleteness.Encode

/-!
# The language matrix computes the guarded strings

Fix `k` test variables.  `KAT.Completeness.langMat k e` is the matrix of languages attached to a
KAT term `e` by interpreting each action `p` as the matrix whose `(i, j)` entry is the single
letter `code i p j`.  This file proves that this matrix is *exactly* the encoding of the
guarded-string semantics of `e`: the `(i, j)` entry of `langMat k e` collects the words
`KAT.Completeness.word k i l` for the guarded strings `(αᵢ, l) ∈ e.gs k` whose last atom is `αⱼ`
(`KAT.Completeness.mem_langMat`).

Two features of the encoding make the induction go through:

* the source and target atoms are carried by the *matrix indices*, so a guarded string with no
  actions encodes as the empty word and the single-atom guarded strings give the identity matrix
  rather than a proper sub-identity;
* every letter records *both* of its endpoints, so the fusion product of guarded strings, which
  shares the middle atom, becomes plain concatenation of the encoded words
  (`KAT.Completeness.word_append`).

The consequence that is used downstream is that terms with the same guarded-string semantics have
the same language matrix (`KAT.Completeness.langMat_eq_of_gs_eq`), hence the same matrix of
regular languages (`KAT.Completeness.regMat_eq_of_gs_eq`), which is the form that can be
transported into an arbitrary Kleene algebra with tests.

## References

* Damien Pous, `relation-algebra`, `theories/kat_completeness.v`, after D. Kozen and F. Smith,
  *Kleene algebra with tests: completeness and decidability*, CSL'96.
-/

open scoped Computability KAT

namespace KAT.Completeness

variable {k : ℕ}

/-! ### Auxiliary lemmas on languages and matrices -/

/-- Membership in a singleton language. -/
theorem mem_singleton_lang {a w : List ℕ} : w ∈ ({a} : Language ℕ) ↔ w = a := Iff.rfl

/-- Membership in a finite sum of languages. -/
theorem mem_finsetSum {ι : Type*} (s : Finset ι) (f : ι → Language ℕ) (w : List ℕ) :
    w ∈ ∑ x ∈ s, f x ↔ ∃ x ∈ s, w ∈ f x := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    simp only [Language.mem_add, ih, Finset.mem_insert]
    constructor
    · rintro (h | ⟨x, hx, hw⟩)
      · exact ⟨a, Or.inl rfl, h⟩
      · exact ⟨x, Or.inr hx, hw⟩
    · rintro ⟨x, rfl | hx, hw⟩
      · exact Or.inl hw
      · exact Or.inr ⟨x, hx, hw⟩

/-- A supremum of matrices is computed entrywise. -/
theorem matrix_iSup_apply {ι : Sort*} {m n K : Type*} [CompleteLattice K] (f : ι → Matrix m n K)
    (i : m) (j : n) : (⨆ x, f x) i j = ⨆ x, f x i j := by
  rw [← sSup_range, Matrix.sSup_apply, iSup_range]

/-! ### Unfolding the language matrix -/

theorem langMat_zero : langMat k .zero = 0 := rfl
theorem langMat_one : langMat k .one = 1 := rfl
theorem langMat_test (b : BTerm) : langMat k (.test b) = testMat k (Language ℕ) b := rfl
theorem langMat_act (p : ℕ) (i j : Idx k) :
    langMat k (.act p) i j = ({[code i p j]} : Language ℕ) := rfl
theorem langMat_add (e f : KTerm) : langMat k (.add e f) = langMat k e + langMat k f := rfl
theorem langMat_mul (e f : KTerm) : langMat k (.mul e f) = langMat k e * langMat k f := rfl
theorem langMat_star (e : KTerm) : langMat k (.star e) = (langMat k e)∗ := rfl

/-! ### Guarded strings: concatenation -/

/-- The last atom of a concatenation of two tails. -/
theorem last_append (α : Atom) (l₁ l₂ : List (ℕ × Atom)) :
    GStr.last α (l₁ ++ l₂) = GStr.last (GStr.last α l₁) l₂ := by
  induction l₁ generalizing α with
  | nil => rfl
  | cons x l ih =>
    obtain ⟨p, β⟩ := x
    rw [List.cons_append, GStr.last_cons, GStr.last_cons, ih]

/-- **The fusion product becomes concatenation.**  Because every letter records both of its
endpoints, the word encoding a concatenated tail is the concatenation of the two words, the
second one started at the atom shared by the two halves. -/
theorem word_append {α : Atom} {i : ℕ} (h : idxNat k α = i) (l₁ l₂ : List (ℕ × Atom)) :
    word k i (l₁ ++ l₂) = word k i l₁ ++ word k (idxNat k (GStr.last α l₁)) l₂ := by
  induction l₁ generalizing α i with
  | nil =>
    rw [List.nil_append, word_nil, List.nil_append, GStr.last_nil, h]
  | cons x l ih =>
    obtain ⟨p, β⟩ := x
    rw [List.cons_append, word_cons, word_cons, GStr.last_cons, List.cons_append,
      ih (α := β) rfl]

/-! ### The correctness relation -/

/-- `Rep k X M` says that the matrix of languages `M` encodes the set of guarded strings `X`: the
`(i, j)` entry of `M` consists exactly of the encodings of the guarded strings of `X` running from
the atom of index `i` to the atom of index `j`. -/
def Rep (k : ℕ) (X : Set GStr) (M : Matrix (Idx k) (Idx k) (Language ℕ)) : Prop :=
  ∀ (i j : Idx k) (w : List ℕ), w ∈ M i j ↔
    ∃ l : List (ℕ × Atom), (atomOf k i, l) ∈ X ∧
      GStr.last (atomOf k i) l = atomOf k j ∧ word k i.val l = w

/-- The empty set of guarded strings is encoded by the zero matrix. -/
theorem rep_empty : Rep k ∅ 0 := by
  intro i j w
  simp only [Matrix.zero_apply]
  constructor
  · intro h
    exact absurd h (Language.notMem_zero w)
  · rintro ⟨l, hl, -, -⟩
    exact absurd hl (Set.notMem_empty _)

/-- The single-atom guarded strings are encoded by the identity matrix. -/
theorem rep_unitGS : Rep k (unitGS k) 1 := by
  intro i j w
  rw [Matrix.one_apply]
  constructor
  · intro h
    split_ifs at h with hij
    · subst hij
      rw [Language.mem_one] at h
      exact ⟨[], mem_unitGS.2 ⟨rfl, atomOf_mem k i⟩, rfl, h.symm⟩
    · exact absurd h (Language.notMem_zero w)
  · rintro ⟨l, hl, hlast, hw⟩
    obtain ⟨rfl, -⟩ := mem_unitGS.1 hl
    rw [GStr.last_nil] at hlast
    obtain rfl : i = j := atomOf_injective k hlast
    rw [if_pos rfl, Language.mem_one]
    exact hw.symm.trans (word_nil _)

/-- The guarded strings of a test are encoded by the diagonal matrix of that test. -/
theorem rep_test (b : BTerm) :
    Rep k ((KTerm.test b).gs k) (testMat k (Language ℕ) b) := by
  intro i j w
  simp only [testMat]
  constructor
  · intro h
    split_ifs at h with hij
    · obtain ⟨rfl, hb⟩ := hij
      rw [Language.mem_one] at h
      exact ⟨[], KTerm.mem_gs_test.2 ⟨rfl, atomOf_mem k i, hb⟩, rfl, h.symm⟩
    · exact absurd h (Language.notMem_zero w)
  · rintro ⟨l, hl, hlast, hw⟩
    obtain ⟨rfl, -, hb⟩ := KTerm.mem_gs_test.1 hl
    rw [GStr.last_nil] at hlast
    obtain rfl : i = j := atomOf_injective k hlast
    rw [if_pos ⟨rfl, hb⟩, Language.mem_one]
    exact hw.symm.trans (word_nil _)

/-- The guarded strings of a single action are encoded by the matrix of its letters. -/
theorem rep_act (p : ℕ) : Rep k ((KTerm.act p).gs k) (langMat k (.act p)) := by
  intro i j w
  rw [langMat_act]
  constructor
  · intro h
    rw [mem_singleton_lang] at h
    refine ⟨[(p, atomOf k j)], KTerm.mem_gs_act.2 ⟨atomOf k j, rfl, atomOf_mem k i,
      atomOf_mem k j⟩, rfl, ?_⟩
    rw [word_cons_atomOf, word_nil, h]
  · rintro ⟨l, hl, hlast, hw⟩
    obtain ⟨β, rfl, -, -⟩ := KTerm.mem_gs_act.1 hl
    rw [GStr.last_cons, GStr.last_nil] at hlast
    subst hlast
    rw [mem_singleton_lang, ← hw, word_cons_atomOf, word_nil]

/-- The union of two sets of guarded strings is encoded by the sum of their matrices. -/
theorem rep_union {X Y : Set GStr} {A B : Matrix (Idx k) (Idx k) (Language ℕ)}
    (hA : Rep k X A) (hB : Rep k Y B) : Rep k (X ∪ Y) (A + B) := by
  intro i j w
  rw [Matrix.add_apply, Language.mem_add, hA i j w, hB i j w]
  constructor
  · rintro (⟨l, hl, h₁, h₂⟩ | ⟨l, hl, h₁, h₂⟩)
    · exact ⟨l, Or.inl hl, h₁, h₂⟩
    · exact ⟨l, Or.inr hl, h₁, h₂⟩
  · rintro ⟨l, hl | hl, h₁, h₂⟩
    · exact Or.inl ⟨l, hl, h₁, h₂⟩
    · exact Or.inr ⟨l, hl, h₁, h₂⟩

/-- **The key step.**  The fusion product of two sets of guarded strings is encoded by the product
of their matrices: the shared middle atom becomes the summation index of the matrix product. -/
theorem rep_fuse {X Y : Set GStr} {A B : Matrix (Idx k) (Idx k) (Language ℕ)}
    (hX : ∀ g ∈ X, GStr.wf k g) (hA : Rep k X A) (hB : Rep k Y B) :
    Rep k (fuse X Y) (A * B) := by
  intro i j w
  rw [Matrix.mul_apply, mem_finsetSum]
  constructor
  · rintro ⟨m, -, hw⟩
    rw [Language.mem_mul] at hw
    obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := hw
    obtain ⟨l₁, hl₁, hlast₁, rfl⟩ := (hA i m w₁).1 hw₁
    obtain ⟨l₂, hl₂, hlast₂, rfl⟩ := (hB m j w₂).1 hw₂
    refine ⟨l₁ ++ l₂, mem_fuse.2 ⟨l₁, l₂, rfl, hl₁, by rw [hlast₁]; exact hl₂⟩, ?_, ?_⟩
    · rw [last_append, hlast₁]
      exact hlast₂
    · rw [word_append (idxNat_atomOf i) l₁ l₂, hlast₁, idxNat_atomOf]
  · rintro ⟨l, hl, hlast, rfl⟩
    obtain ⟨l₁, l₂, rfl, h₁, h₂⟩ := mem_fuse.1 hl
    obtain ⟨m, hm⟩ :=
      exists_atomOf (mem_allAtoms.2 (GStr.wf_last (k := k) _ _ (hX _ h₁)))
    rw [← hm] at h₂
    rw [last_append, ← hm] at hlast
    refine ⟨m, Finset.mem_univ m, ?_⟩
    rw [word_append (idxNat_atomOf i) l₁ l₂, ← hm, idxNat_atomOf]
    exact Language.append_mem_mul ((hA i m _).2 ⟨l₁, h₁, hm.symm, rfl⟩)
      ((hB m j _).2 ⟨l₂, h₂, hlast, rfl⟩)

/-- Iterated fusion is encoded by the matrix powers. -/
theorem rep_fusePow {X : Set GStr} {A : Matrix (Idx k) (Idx k) (Language ℕ)}
    (hX : ∀ g ∈ X, GStr.wf k g) (hA : Rep k X A) : ∀ n : ℕ, Rep k (fusePow k X n) (A ^ n)
  | 0 => by
    rw [pow_zero]
    exact rep_unitGS
  | n + 1 => by
    rw [pow_succ']
    exact rep_fuse hX hA (rep_fusePow hX hA n)

/-- The Kleene star of guarded strings is encoded by the matrix Kleene star. -/
theorem rep_star {X : Set GStr} {A : Matrix (Idx k) (Idx k) (Language ℕ)}
    (hX : ∀ g ∈ X, GStr.wf k g) (hA : Rep k X A) :
    Rep k (⋃ n, fusePow k X n) A∗ := by
  intro i j w
  rw [Matrix.kstar_eq_iSup_pow, matrix_iSup_apply, Language.mem_iSup]
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨l, hl, hlast, hw⟩ := (rep_fusePow hX hA n i j w).1 hn
    exact ⟨l, Set.mem_iUnion.2 ⟨n, hl⟩, hlast, hw⟩
  · rintro ⟨l, hl, hlast, hw⟩
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hl
    exact ⟨n, (rep_fusePow hX hA n i j w).2 ⟨l, hn, hlast, hw⟩⟩

/-! ### The main theorem -/

/-- **Correctness of the encoding.**  The language matrix of a KAT term encodes exactly its
guarded-string semantics. -/
theorem rep_langMat (e : KTerm) : Rep k (e.gs k) (langMat k e) := by
  induction e with
  | zero => exact rep_empty
  | one => exact rep_unitGS
  | test b => exact rep_test b
  | act p => exact rep_act p
  | add e f ihe ihf =>
    rw [langMat_add]
    exact rep_union ihe ihf
  | mul e f ihe ihf =>
    rw [langMat_mul]
    exact rep_fuse (KTerm.wf_of_mem_gs e) ihe ihf
  | star e ih =>
    rw [langMat_star]
    exact rep_star (KTerm.wf_of_mem_gs e) ih

/-- The `(i, j)` entry of the language matrix of `e` consists exactly of the encodings of the
guarded strings of `e` running from the atom of index `i` to the atom of index `j`. -/
theorem mem_langMat (e : KTerm) (i j : Idx k) (w : List ℕ) :
    w ∈ langMat k e i j ↔
      ∃ l : List (ℕ × Atom), (atomOf k i, l) ∈ e.gs k ∧
        GStr.last (atomOf k i) l = atomOf k j ∧ word k i.val l = w :=
  rep_langMat e i j w

/-- Terms with the same guarded-string semantics have the same language matrix. -/
theorem langMat_eq_of_gs_eq {e f : KTerm} (h : e.gs k = f.gs k) : langMat k e = langMat k f := by
  ext i j w
  rw [mem_langMat, mem_langMat, h]

/-- Terms with the same guarded-string semantics have the same matrix of regular languages. -/
theorem regMat_eq_of_gs_eq {e f : KTerm} (h : e.gs k = f.gs k) : regMat k e = regMat k f :=
  regMat_injective (langMat_eq_of_gs_eq h)

end KAT.Completeness
