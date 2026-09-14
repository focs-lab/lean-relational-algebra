import RelationAlgebra.KAT.Basic
import RelationAlgebra.Decide.Antimirov

/-!
# Guarded strings and derivatives for Kleene algebra with tests

The free model of KAT is the algebra of *guarded strings* `α₀ p₁ α₁ ⋯ pₙ αₙ`, alternating atoms
(complete truth assignments to the test variables) and actions.  This file sets up:

* `KAT.BTerm`, `KAT.KTerm`: Boolean terms over test variables `ℕ` and KAT terms over test terms
  and actions `ℕ`;
* atoms as lists of Booleans (`KAT.Atom`), the finite list `KAT.allAtoms k` of atoms for `k` test
  variables, and satisfaction `KAT.Atom.sat`;
* the guarded-string semantics `KAT.KTerm.gs k e : Set GStr`, with the fusion product for
  sequential composition;
* the "accepts an atom" predicate `KAT.KTerm.E` and the partial derivatives `KAT.KTerm.D` by
  a pair (atom, action), characterising membership in `gs` (`nil_mem_gs`, `cons_mem_gs`);
* a bisimulation checker and worklist exploration as in `RelationAlgebra.Decide.Antimirov`, with
  soundness theorem `KAT.KTerm.gs_eq_of_decideEq`.

The algebraic soundness (equal guarded-string sets give equal values in every complete KAT) is
proved in `RelationAlgebra.Decide.KATSound`.
-/

open scoped Computability

namespace KAT

/-! ### Syntax -/

/-- Boolean terms over test variables. -/
inductive BTerm : Type
  | top : BTerm
  | bot : BTerm
  | tvar : ℕ → BTerm
  | and : BTerm → BTerm → BTerm
  | or : BTerm → BTerm → BTerm
  | not : BTerm → BTerm
  deriving DecidableEq, Repr, Inhabited

/-- KAT terms: tests, actions, and the Kleene algebra operations. -/
inductive KTerm : Type
  | zero : KTerm
  | one : KTerm
  | test : BTerm → KTerm
  | act : ℕ → KTerm
  | add : KTerm → KTerm → KTerm
  | mul : KTerm → KTerm → KTerm
  | star : KTerm → KTerm
  deriving DecidableEq, Repr, Inhabited

/-- The test variables of a Boolean term. -/
def BTerm.tvars : BTerm → List ℕ
  | top => []
  | bot => []
  | tvar i => [i]
  | and a b => a.tvars ++ b.tvars
  | or a b => a.tvars ++ b.tvars
  | not a => a.tvars

/-- The test variables of a KAT term. -/
def KTerm.tvars : KTerm → List ℕ
  | zero => []
  | one => []
  | test b => b.tvars
  | act _ => []
  | add a b => a.tvars ++ b.tvars
  | mul a b => a.tvars ++ b.tvars
  | star a => a.tvars

/-- The actions of a KAT term. -/
def KTerm.acts : KTerm → List ℕ
  | zero => []
  | one => []
  | test _ => []
  | act p => [p]
  | add a b => a.acts ++ b.acts
  | mul a b => a.acts ++ b.acts
  | star a => a.acts

/-! ### Atoms -/

/-- An atom: a truth assignment to the test variables `0, …, k - 1`, as a list of length `k`. -/
abbrev Atom := List Bool

/-- Satisfaction of a Boolean term by an atom (variables beyond the length are `false`). -/
def Atom.sat (α : Atom) : BTerm → Bool
  | .top => true
  | .bot => false
  | .tvar i => α.getD i false
  | .and a b => α.sat a && α.sat b
  | .or a b => α.sat a || α.sat b
  | .not a => !α.sat a

/-- All atoms for `k` test variables. -/
def allAtoms : ℕ → List Atom
  | 0 => [[]]
  | k + 1 => (allAtoms k).map (true :: ·) ++ (allAtoms k).map (false :: ·)

theorem mem_allAtoms {k : ℕ} {α : Atom} : α ∈ allAtoms k ↔ α.length = k := by
  induction k generalizing α with
  | zero => simp [allAtoms]
  | succ k ih =>
    cases α with
    | nil => simp [allAtoms]
    | cons b α =>
      cases b <;> simp [allAtoms, ih]

/-! ### Guarded strings -/

/-- A guarded string `α₀ p₁ α₁ ⋯ pₙ αₙ`, as the initial atom and the list of (action, atom)
pairs. -/
abbrev GStr := Atom × List (ℕ × Atom)

/-- The last atom of a guarded string. -/
def GStr.last : Atom → List (ℕ × Atom) → Atom
  | α, [] => α
  | _, (_, β) :: l => GStr.last β l

@[simp] theorem GStr.last_nil (α : Atom) : GStr.last α [] = α := rfl
@[simp] theorem GStr.last_cons (α β : Atom) (p : ℕ) (l : List (ℕ × Atom)) :
    GStr.last α ((p, β) :: l) = GStr.last β l := rfl

/-- The fusion product of two sets of guarded strings: concatenate when the last atom of the
first string is the first atom of the second, identifying the two. -/
def fuse (X Y : Set GStr) : Set GStr :=
  {g | ∃ α l₁ l₂, g = (α, l₁ ++ l₂) ∧ (α, l₁) ∈ X ∧ (GStr.last α l₁, l₂) ∈ Y}

theorem mem_fuse {X Y : Set GStr} {α : Atom} {l : List (ℕ × Atom)} :
    (α, l) ∈ fuse X Y ↔ ∃ l₁ l₂, l = l₁ ++ l₂ ∧ (α, l₁) ∈ X ∧ (GStr.last α l₁, l₂) ∈ Y := by
  constructor
  · rintro ⟨α', l₁, l₂, h, h₁, h₂⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact ⟨l₁, l₂, rfl, h₁, h₂⟩
  · rintro ⟨l₁, l₂, rfl, h₁, h₂⟩
    exact ⟨α, l₁, l₂, rfl, h₁, h₂⟩

/-- The guarded strings consisting of a single atom (the semantics of `1`). -/
def unitGS (k : ℕ) : Set GStr := {g | g.2 = [] ∧ g.1 ∈ allAtoms k}

theorem mem_unitGS {k : ℕ} {α : Atom} {l : List (ℕ × Atom)} :
    (α, l) ∈ unitGS k ↔ l = [] ∧ α ∈ allAtoms k := Iff.rfl

/-- Iterated fusion product. -/
def fusePow (k : ℕ) (X : Set GStr) : ℕ → Set GStr
  | 0 => unitGS k
  | n + 1 => fuse X (fusePow k X n)

/-- The guarded-string semantics of a KAT term, for `k` test variables. -/
def KTerm.gs (k : ℕ) : KTerm → Set GStr
  | zero => ∅
  | one => unitGS k
  | test b => {g | g.2 = [] ∧ g.1 ∈ allAtoms k ∧ g.1.sat b = true}
  | act p => {g | ∃ α β, g = (α, [(p, β)]) ∧ α ∈ allAtoms k ∧ β ∈ allAtoms k}
  | add a b => a.gs k ∪ b.gs k
  | mul a b => fuse (a.gs k) (b.gs k)
  | star a => ⋃ n, fusePow k (a.gs k) n

namespace KTerm

variable {k : ℕ}

theorem mem_gs_test {b : BTerm} {α : Atom} {l : List (ℕ × Atom)} :
    (α, l) ∈ (test b).gs k ↔ l = [] ∧ α ∈ allAtoms k ∧ α.sat b = true := Iff.rfl

theorem mem_gs_act {p : ℕ} {α : Atom} {l : List (ℕ × Atom)} :
    (α, l) ∈ (act p).gs k ↔ ∃ β, l = [(p, β)] ∧ α ∈ allAtoms k ∧ β ∈ allAtoms k := by
  constructor
  · rintro ⟨α', β, h, hα, hβ⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact ⟨β, rfl, hα, hβ⟩
  · rintro ⟨β, rfl, hα, hβ⟩
    exact ⟨α, β, rfl, hα, hβ⟩

theorem mem_gs_add {a b : KTerm} {g : GStr} : g ∈ (add a b).gs k ↔ g ∈ a.gs k ∨ g ∈ b.gs k :=
  Iff.rfl

theorem mem_gs_mul {a b : KTerm} {α : Atom} {l : List (ℕ × Atom)} :
    (α, l) ∈ (mul a b).gs k ↔
      ∃ l₁ l₂, l = l₁ ++ l₂ ∧ (α, l₁) ∈ a.gs k ∧ (GStr.last α l₁, l₂) ∈ b.gs k :=
  mem_fuse

theorem mem_gs_star {a : KTerm} {g : GStr} :
    g ∈ (star a).gs k ↔ ∃ n, g ∈ fusePow k (a.gs k) n :=
  Set.mem_iUnion

/-- The first atom of a guarded string in the semantics is an atom for `k` variables. -/
theorem fst_mem_allAtoms_of_mem_gs : ∀ (e : KTerm) {α : Atom} {l : List (ℕ × Atom)},
    (α, l) ∈ e.gs k → α ∈ allAtoms k
  | zero, _, _, h => absurd h (Set.notMem_empty _)
  | one, _, _, h => (mem_unitGS.1 h).2
  | test _, _, _, h => (mem_gs_test.1 h).2.1
  | act _, _, _, h => by
    obtain ⟨_, _, hα, _⟩ := mem_gs_act.1 h
    exact hα
  | add a b, _, _, h => by
    rcases h with h | h
    · exact fst_mem_allAtoms_of_mem_gs a h
    · exact fst_mem_allAtoms_of_mem_gs b h
  | mul a _, _, _, h => by
    obtain ⟨l₁, l₂, _, h₁, _⟩ := mem_gs_mul.1 h
    exact fst_mem_allAtoms_of_mem_gs a h₁
  | star a, _, _, h => by
    obtain ⟨n, hn⟩ := mem_gs_star.1 h
    cases n with
    | zero => exact hn.2
    | succ n =>
      obtain ⟨l₁, l₂, _, h₁, _⟩ := mem_fuse.1 hn
      exact fst_mem_allAtoms_of_mem_gs a h₁

/-! ### Derivatives -/

/-- Does the term accept the single-atom guarded string `α`? -/
def E (α : Atom) : KTerm → Bool
  | zero => false
  | one => true
  | test b => α.sat b
  | act _ => false
  | add a b => E α a || E α b
  | mul a b => E α a && E α b
  | star _ => true

/-- Partial derivatives of a KAT term by an atom and an action. -/
def D (α : Atom) (p : ℕ) : KTerm → List KTerm
  | zero => []
  | one => []
  | test _ => []
  | act q => if q = p then [test .top] else []
  | add a b => D α p a ++ D α p b
  | mul a b => (D α p a).map (fun t ↦ mul t b) ++ (if E α a then D α p b else [])
  | star a => (D α p a).map (fun t ↦ mul t (star a))

theorem nil_mem_gs {α : Atom} (hα : α ∈ allAtoms k) :
    ∀ e : KTerm, (α, []) ∈ e.gs k ↔ E α e = true
  | zero => by simp [gs, E]
  | one => by simp [gs, mem_unitGS, hα, E]
  | test b => by simp [mem_gs_test, hα, E]
  | act p => by simp [mem_gs_act, E]
  | add a b => by
    simp only [mem_gs_add, E, Bool.or_eq_true]
    rw [nil_mem_gs hα a, nil_mem_gs hα b]
  | mul a b => by
    simp only [E, Bool.and_eq_true]
    rw [mem_gs_mul, ← nil_mem_gs hα a, ← nil_mem_gs hα b]
    constructor
    · rintro ⟨l₁, l₂, h, h₁, h₂⟩
      obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 h.symm
      exact ⟨h₁, h₂⟩
    · rintro ⟨h₁, h₂⟩
      exact ⟨[], [], rfl, h₁, h₂⟩
  | star a => by
    simp only [E, iff_true]
    exact mem_gs_star.2 ⟨0, rfl, hα⟩

theorem cons_mem_gs {α : Atom} (hα : α ∈ allAtoms k) (p : ℕ) (β : Atom) :
    ∀ (e : KTerm) (l : List (ℕ × Atom)),
      (α, (p, β) :: l) ∈ e.gs k ↔ ∃ t ∈ D α p e, (β, l) ∈ t.gs k
  | zero, l => by simp [gs, D]
  | one, l => by simp [gs, mem_unitGS, D]
  | test b, l => by simp [mem_gs_test, D]
  | act q, l => by
    simp only [mem_gs_act, D]
    constructor
    · rintro ⟨β', h, -, hβ'⟩
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := List.cons_eq_cons.1 h |>.imp Prod.mk.inj id
      exact ⟨test .top, by simp, rfl, hβ', rfl⟩
    · rintro ⟨t, ht, hl⟩
      split_ifs at ht with hq
      · subst hq
        simp only [List.mem_singleton] at ht
        subst ht
        obtain ⟨rfl, hβ, -⟩ := mem_gs_test.1 hl
        exact ⟨β, rfl, hα, hβ⟩
      · simp at ht
  | add a b, l => by
    simp only [mem_gs_add, D, List.mem_append, cons_mem_gs hα p β a l, cons_mem_gs hα p β b l]
    constructor
    · rintro (⟨t, ht, hl⟩ | ⟨t, ht, hl⟩)
      · exact ⟨t, Or.inl ht, hl⟩
      · exact ⟨t, Or.inr ht, hl⟩
    · rintro ⟨t, ht | ht, hl⟩
      · exact Or.inl ⟨t, ht, hl⟩
      · exact Or.inr ⟨t, ht, hl⟩
  | mul a b, l => by
    simp only [D, List.mem_append, List.mem_map]
    constructor
    · intro h
      obtain ⟨l₁, l₂, hl, h₁, h₂⟩ := mem_gs_mul.1 h
      cases l₁ with
      | nil =>
        simp only [List.nil_append] at hl
        subst hl
        have ha : E α a = true := (nil_mem_gs hα a).1 h₁
        simp only [GStr.last_nil] at h₂
        obtain ⟨t, ht, hl⟩ := (cons_mem_gs hα p β b l).1 h₂
        exact ⟨t, Or.inr (by simpa [ha] using ht), hl⟩
      | cons x l₁' =>
        obtain ⟨p', β'⟩ := x
        simp only [List.cons_append] at hl
        obtain ⟨hx, rfl⟩ := List.cons_eq_cons.1 hl
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hx
        obtain ⟨t, ht, hl'⟩ := (cons_mem_gs hα p β a l₁').1 h₁
        refine ⟨mul t b, Or.inl ⟨t, ht, rfl⟩, ?_⟩
        exact mem_gs_mul.2 ⟨l₁', l₂, rfl, hl', by simpa using h₂⟩
    · rintro ⟨t, ht | ht, hl⟩
      · obtain ⟨t', ht', rfl⟩ := ht
        obtain ⟨l₁, l₂, rfl, h₁, h₂⟩ := mem_gs_mul.1 hl
        exact mem_gs_mul.2 ⟨(p, β) :: l₁, l₂, rfl, (cons_mem_gs hα p β a l₁).2 ⟨t', ht', h₁⟩,
          by simpa using h₂⟩
      · by_cases ha : E α a = true
        · simp only [ha, if_true] at ht
          exact mem_gs_mul.2 ⟨[], (p, β) :: l, rfl, (nil_mem_gs hα a).2 ha,
            by simpa using (cons_mem_gs hα p β b l).2 ⟨t, ht, hl⟩⟩
        · simp [ha] at ht
  | star a, l => by
    simp only [D, List.mem_map]
    constructor
    · intro h
      obtain ⟨n, hn⟩ := mem_gs_star.1 h
      clear h
      induction n generalizing α l with
      | zero => simp [fusePow, unitGS] at hn
      | succ n ih =>
        obtain ⟨l₁, l₂, hl, h₁, h₂⟩ := mem_fuse.1 hn
        cases l₁ with
        | nil =>
          simp only [List.nil_append] at hl
          subst hl
          exact ih hα l (by simpa using h₂)
        | cons x l₁' =>
          obtain ⟨p', β'⟩ := x
          simp only [List.cons_append] at hl
          obtain ⟨hx, rfl⟩ := List.cons_eq_cons.1 hl
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hx
          obtain ⟨t, ht, hl'⟩ := (cons_mem_gs hα p β a l₁').1 h₁
          refine ⟨mul t (star a), ⟨t, ht, rfl⟩, ?_⟩
          exact mem_gs_mul.2 ⟨l₁', l₂, rfl, hl', mem_gs_star.2 ⟨n, by simpa using h₂⟩⟩
    · rintro ⟨t, ⟨t', ht', rfl⟩, hl⟩
      obtain ⟨l₁, l₂, rfl, h₁, h₂⟩ := mem_gs_mul.1 hl
      obtain ⟨n, hn⟩ := mem_gs_star.1 h₂
      refine mem_gs_star.2 ⟨n + 1, mem_fuse.2 ⟨(p, β) :: l₁, l₂, rfl, ?_, by simpa using hn⟩⟩
      exact (cons_mem_gs hα p β a l₁).2 ⟨t', ht', h₁⟩

theorem D_eq_nil_of_not_mem_acts (α : Atom) (p : ℕ) :
    ∀ e : KTerm, p ∉ e.acts → D α p e = []
  | zero, _ => rfl
  | one, _ => rfl
  | test _, _ => rfl
  | act q, h => by
    simp only [acts, List.mem_singleton] at h
    simp [D, Ne.symm h]
  | add a b, h => by
    simp only [acts, List.mem_append, not_or] at h
    simp [D, D_eq_nil_of_not_mem_acts α p a h.1, D_eq_nil_of_not_mem_acts α p b h.2]
  | mul a b, h => by
    simp only [acts, List.mem_append, not_or] at h
    simp [D, D_eq_nil_of_not_mem_acts α p a h.1, D_eq_nil_of_not_mem_acts α p b h.2]
  | star a, h => by
    simp [D, D_eq_nil_of_not_mem_acts α p a h]

/-! ### Sets of terms -/

/-- The semantics of a set (list) of terms. -/
def gss (k : ℕ) (S : List KTerm) : Set GStr := {g | ∃ t ∈ S, g ∈ t.gs k}

theorem mem_gss {S : List KTerm} {g : GStr} : g ∈ gss k S ↔ ∃ t ∈ S, g ∈ t.gs k := Iff.rfl

@[simp] theorem gss_singleton (t : KTerm) : gss k [t] = t.gs k := by
  ext g; simp [mem_gss]

/-- Acceptance of an atom by a set of terms. -/
def ES (α : Atom) (S : List KTerm) : Bool := S.any (E α)

/-- Partial derivative of a set of terms. -/
def DS (α : Atom) (p : ℕ) (S : List KTerm) : List KTerm := S.flatMap (D α p)

/-- The actions of a set of terms. -/
def actsS (S : List KTerm) : List ℕ := S.flatMap acts

theorem nil_mem_gss_iff {α : Atom} (hα : α ∈ allAtoms k) (S : List KTerm) :
    (α, []) ∈ gss k S ↔ ES α S = true := by
  simp [mem_gss, ES, List.any_eq_true, nil_mem_gs hα]

theorem cons_mem_gss_iff {α : Atom} (hα : α ∈ allAtoms k) (p : ℕ) (β : Atom) (S : List KTerm)
    (l : List (ℕ × Atom)) : (α, (p, β) :: l) ∈ gss k S ↔ (β, l) ∈ gss k (DS α p S) := by
  simp only [mem_gss, DS, List.mem_flatMap, cons_mem_gs hα]
  constructor
  · rintro ⟨t, ht, t', ht', hl⟩
    exact ⟨t', ⟨t, ht, ht'⟩, hl⟩
  · rintro ⟨t', ⟨t, ht, ht'⟩, hl⟩
    exact ⟨t, ht, t', ht', hl⟩

theorem DS_eq_nil_of_not_mem_actsS (α : Atom) (p : ℕ) (S : List KTerm) (h : p ∉ actsS S) :
    DS α p S = [] := by
  simp only [actsS, List.mem_flatMap, not_exists, not_and] at h
  simp only [DS, List.flatMap_eq_nil_iff]
  exact fun t ht ↦ D_eq_nil_of_not_mem_acts α p t (h t ht)

/-- Set-equality of two lists of terms. -/
def setEq (S T : List KTerm) : Bool := S.all (· ∈ T) && T.all (· ∈ S)

theorem gss_eq_of_setEq {S T : List KTerm} (h : setEq S T = true) : gss k S = gss k T := by
  simp only [setEq, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  ext g
  simp only [mem_gss]
  exact ⟨fun ⟨t, ht, hg⟩ ↦ ⟨t, h.1 t ht, hg⟩, fun ⟨t, ht, hg⟩ ↦ ⟨t, h.2 t ht, hg⟩⟩

/-! ### Bisimulations -/

/-- A pair of states. -/
abbrev Pair := List KTerm × List KTerm

/-- Membership up to set-equality. -/
def memUpTo (p : Pair) (R : List Pair) : Bool :=
  R.any fun q ↦ setEq p.1 q.1 && setEq p.2 q.2

/-- Bisimulation check for `k` test variables. -/
def isBisim (k : ℕ) (R : List Pair) : Bool :=
  R.all fun p ↦ (allAtoms k).all fun α ↦ (ES α p.1 == ES α p.2) &&
    (actsS p.1 ++ actsS p.2).all fun q ↦ memUpTo (DS α q p.1, DS α q p.2) R

theorem gss_eq_of_isBisim_aux {R : List Pair} (hR : isBisim k R = true) :
    ∀ (l : List (ℕ × Atom)) (α : Atom) (p : Pair), p ∈ R →
      ((α, l) ∈ gss k p.1 ↔ (α, l) ∈ gss k p.2) := by
  intro l
  induction l with
  | nil =>
    intro α p hp
    by_cases hα : α ∈ allAtoms k
    · simp only [isBisim, List.all_eq_true, Bool.and_eq_true, beq_iff_eq] at hR
      rw [nil_mem_gss_iff hα, nil_mem_gss_iff hα, (hR p hp α hα).1]
    · constructor <;> intro h <;> obtain ⟨t, -, ht⟩ := h <;>
        exact absurd (fst_mem_allAtoms_of_mem_gs t ht) hα
  | cons x l ih =>
    obtain ⟨q, β⟩ := x
    intro α p hp
    by_cases hα : α ∈ allAtoms k
    · rw [cons_mem_gss_iff hα, cons_mem_gss_iff hα]
      by_cases hq : q ∈ actsS p.1 ++ actsS p.2
      · have hR' := hR
        simp only [isBisim, List.all_eq_true, Bool.and_eq_true, beq_iff_eq] at hR'
        have hmem := (hR' p hp α hα).2 q hq
        simp only [memUpTo, List.any_eq_true, Bool.and_eq_true] at hmem
        obtain ⟨r, hr, h₁, h₂⟩ := hmem
        rw [gss_eq_of_setEq h₁, gss_eq_of_setEq h₂]
        exact ih β r hr
      · simp only [List.mem_append, not_or] at hq
        rw [DS_eq_nil_of_not_mem_actsS α q _ hq.1, DS_eq_nil_of_not_mem_actsS α q _ hq.2]
    · constructor <;> intro h <;> obtain ⟨t, -, ht⟩ := h <;>
        exact absurd (fst_mem_allAtoms_of_mem_gs t ht) hα

/-- States related by a bisimulation have the same guarded-string semantics. -/
theorem gss_eq_of_isBisim {R : List Pair} (hR : isBisim k R = true) {S T : List KTerm}
    (h : memUpTo (S, T) R = true) : gss k S = gss k T := by
  simp only [memUpTo, List.any_eq_true, Bool.and_eq_true] at h
  obtain ⟨q, hq, h₁, h₂⟩ := h
  rw [gss_eq_of_setEq h₁, gss_eq_of_setEq h₂]
  ext ⟨α, l⟩
  exact gss_eq_of_isBisim_aux hR l α q hq

/-! ### The decision procedure -/

/-- Worklist exploration. -/
def explore (k : ℕ) : ℕ → List Pair → List Pair → Option (List Pair)
  | 0, _, _ => none
  | _ + 1, visited, [] => some visited
  | fuel + 1, visited, p :: todo =>
    if memUpTo p visited then explore k fuel visited todo
    else
      let next := (allAtoms k).flatMap fun α ↦
        (actsS p.1 ++ actsS p.2).map fun q ↦ (DS α q p.1, DS α q p.2)
      explore k fuel (p :: visited) (next ++ todo)

/-- Decide whether two KAT terms have the same guarded strings over `k` test variables. -/
def decideEq (k : ℕ) (e f : KTerm) (fuel : ℕ := 1000) : Bool :=
  match explore k fuel [] [([e], [f])] with
  | some R => isBisim k R && memUpTo ([e], [f]) R
  | none => false

/-- Decide inclusion of guarded-string semantics. -/
def decideLe (k : ℕ) (e f : KTerm) (fuel : ℕ := 1000) : Bool := decideEq k (add e f) f fuel

/-- **Soundness of the checker.** -/
theorem gs_eq_of_decideEq {e f : KTerm} {fuel : ℕ} (h : decideEq k e f fuel = true) :
    e.gs k = f.gs k := by
  unfold decideEq at h
  split at h
  · rw [Bool.and_eq_true] at h
    simpa using gss_eq_of_isBisim h.1 h.2
  · exact absurd h Bool.false_ne_true

theorem gs_le_of_decideLe {e f : KTerm} {fuel : ℕ} (h : decideLe k e f fuel = true) :
    e.gs k ⊆ f.gs k := by
  have := gs_eq_of_decideEq h
  change e.gs k ∪ f.gs k = f.gs k at this
  rw [← this]
  exact Set.subset_union_left

end KTerm

end KAT
