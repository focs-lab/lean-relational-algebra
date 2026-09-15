import RelationAlgebra.KATCompleteness.AtomMatrix

/-!
# Encoding guarded strings as words

A guarded string `α₀ p₁ α₁ ⋯ pₙ αₙ` is encoded as the word

  `⟨α₀, p₁, α₁⟩ ⟨α₁, p₂, α₂⟩ ⋯ ⟨α_{n-1}, pₙ, αₙ⟩`

over the alphabet of *atom-action-atom* triples.  Two things make this encoding work where
naive encodings fail:

* the **source and target atoms are carried by the matrix indices**, so a guarded string with
  no actions encodes as the empty word and the single-atom strings become the identity matrix
  rather than a proper sub-identity;
* each letter records **both** of its endpoints, so the fusion product of guarded strings, which
  shares the middle atom, becomes plain concatenation of the encoded words.

`KAT.Completeness.word` is the encoding and `KAT.Completeness.langMat` the resulting matrix of
languages.
-/

open scoped Computability KAT

namespace KAT.Completeness

variable {k : ℕ}

/-- The letter for a transition from the atom of index `i` to the atom of index `j` on the
action `p`. -/
def code (i : Idx k) (p : ℕ) (j : Idx k) : ℕ := Nat.pair i.val (Nat.pair p j.val)

theorem code_injective {i i' : Idx k} {p p' : ℕ} {j j' : Idx k}
    (h : code i p j = code i' p' j') : i = i' ∧ p = p' ∧ j = j' := by
  rw [code, code] at h
  obtain ⟨h₁, h₂⟩ := Nat.pair_eq_pair.1 h
  obtain ⟨h₃, h₄⟩ := Nat.pair_eq_pair.1 h₂
  exact ⟨Fin.ext h₁, h₃, Fin.ext h₄⟩

/-- The position of an atom in the enumeration `allAtoms k`. -/
def idxNat (k : ℕ) (α : Atom) : ℕ := (allAtoms k).idxOf α

theorem idxNat_lt {α : Atom} (h : α ∈ allAtoms k) : idxNat k α < (allAtoms k).length :=
  List.idxOf_lt_length_of_mem h

theorem atomOf_idxNat {α : Atom} (h : α ∈ allAtoms k) :
    atomOf k ⟨idxNat k α, idxNat_lt h⟩ = α :=
  List.idxOf_get _

theorem idxNat_atomOf (i : Idx k) : idxNat k (atomOf k i) = i.val :=
  List.get_idxOf (nodup_allAtoms k) i

/-- The word encoding the tail of a guarded string, given the position of its current atom.
Every letter records both of its endpoints, so that the fusion product of guarded strings
becomes plain concatenation of words. -/
def word (k : ℕ) : ℕ → List (ℕ × Atom) → List ℕ
  | _, [] => []
  | i, (p, β) :: l => Nat.pair i (Nat.pair p (idxNat k β)) :: word k (idxNat k β) l

@[simp] theorem word_nil (i : ℕ) : word k i [] = [] := rfl

@[simp] theorem word_cons (i : ℕ) (p : ℕ) (β : Atom) (l : List (ℕ × Atom)) :
    word k i ((p, β) :: l) = Nat.pair i (Nat.pair p (idxNat k β)) :: word k (idxNat k β) l := rfl

theorem word_cons_atomOf (i j : Idx k) (p : ℕ) (l : List (ℕ × Atom)) :
    word k i.val ((p, atomOf k j) :: l) = code i p j :: word k j.val l := by
  rw [word_cons, idxNat_atomOf, code]

/-- The matrix of languages attached to a KAT term: the `(i, j)` entry collects the encodings of
the guarded strings running from the atom of index `i` to the atom of index `j`. -/
noncomputable def langMat (k : ℕ) : KTerm → Matrix (Idx k) (Idx k) (Language ℕ) :=
  evalMat fun p i j => ({[code i p j]} : Language ℕ)

/-- The same matrix, with entries recorded as *regular* languages.  This is the form that can be
transported into an arbitrary Kleene algebra. -/
noncomputable def regMat (k : ℕ) : KTerm → Matrix (Idx k) (Idx k) RelationAlgebra.RegLang :=
  evalMat fun p i j => RelationAlgebra.RegLang.ofTerm (.var (code i p j))

/-- Taking the underlying language is a Kleene algebra homomorphism. -/
theorem isKAHom_toLang :
    Matrix.IsKAHom (RelationAlgebra.RegLang.toLang) where
  map_zero := rfl
  map_one := rfl
  map_add := RelationAlgebra.RegLang.toLang_add
  map_mul := RelationAlgebra.RegLang.toLang_mul
  map_kstar := RelationAlgebra.RegLang.toLang_kstar

/-- The regular-language matrix determines the language matrix. -/
theorem langMat_eq_map (e : KTerm) :
    langMat k e = (regMat k e).map RelationAlgebra.RegLang.toLang := by
  rw [regMat, evalMat_map isKAHom_toLang, langMat]
  rfl

/-- Hence equal language matrices give equal regular-language matrices. -/
theorem regMat_injective {e f : KTerm} (h : langMat k e = langMat k f) :
    regMat k e = regMat k f := by
  rw [langMat_eq_map, langMat_eq_map] at h
  funext i j
  exact RelationAlgebra.RegLang.toLang_injective (congrFun (congrFun h i) j)

end KAT.Completeness
