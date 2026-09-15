import Mathlib.Computability.Language
import Mathlib.Order.Hom.BoundedLattice
import RelationAlgebra.KAT.Defs
import RelationAlgebra.Kleene.Complete
import RelationAlgebra.Kleene.Quantale

/-!
# The model of finite traces

A *trace* over a type of states `σ` and a type of actions `α` is a word in which every action is
preceded and followed by a state, `s₀ a₁ s₁ ⋯ aₙ sₙ`.  We represent it as the pair of its initial
state and its list of steps, `Trace σ α := σ × List (α × σ)`.  Two traces compose exactly when the
first one ends in the state where the second one starts, and the shared state is *not* duplicated:
the product is the **fusion product**, not plain concatenation.

A *trace language* is a set of traces.  `TraceLang σ α` is a complete Kleene algebra with tests,
the tests being the subsets of states:

* `0 = ∅`, `+ = ∪`, `≤ = ⊆` (the complete lattice of `Set`),
* `1 = {t | t.2 = []}`, the traces reduced to a single state,
* `x * y = fuse x y`, the fusion product,
* `x∗ = ⨆ n, x ^ n`, obtained from the quantale structure through
  `KleeneAlgebra.ofQuantale`,
* `KAT.test P = ofStates P = {t | t.2 = [] ∧ t.1 ∈ P}` for `P : Set σ`.

Two specialisations matter:

* taking `σ := Unit` gives back the languages of finite words: `TraceLang.languageOrderIso`
  is an isomorphism onto Mathlib's `Language α`, and `toLanguage_zero`, `toLanguage_one`,
  `toLanguage_add`, `toLanguage_mul`, `toLanguage_kstar` say that it preserves the Kleene
  algebra structure;
* taking the states to be the atoms of a Boolean algebra of tests gives the *guarded string
  languages* `GuardedLang`, with respect to which KAT is complete.  `TraceLang.katOfHom`
  transports the KAT structure along a map from an abstract Boolean algebra of tests to the
  sets of states.  See the section `Guarded strings` below.

Since `TraceLang σ α` is reducibly `Set (Trace σ α)`, and `Set` already carries (scoped,
pointwise) `+` and `*` instances in Mathlib, the ring-like instances here are **scoped**: write
`open scoped TraceLang` to activate them, exactly as for `SetRel` in
`RelationAlgebra.Models.Rel`.

## References

This is a port of the `traces.v` and `glang.v` theories of Damien Pous'
[relation-algebra](https://github.com/damien-pous/relation-algebra) library for Rocq/Coq, whose
organisation we follow.  We only develop the untyped model; the typed model of `traces.v` has no
counterpart here.
-/

open scoped Computability

/-- A finite trace: an initial state followed by a list of (action, state) steps. -/
abbrev Trace (σ α : Type*) := σ × List (α × σ)

namespace Trace

variable {σ α : Type*}

/-- The state reached after performing the steps `l` from the state `s`. -/
def lastOf : σ → List (α × σ) → σ
  | s, [] => s
  | _, (_, s') :: l => lastOf s' l

@[simp] theorem lastOf_nil (s : σ) : lastOf (α := α) s [] = s := rfl

@[simp] theorem lastOf_cons (s s' : σ) (a : α) (l : List (α × σ)) :
    lastOf s ((a, s') :: l) = lastOf s' l := rfl

@[simp] theorem lastOf_append (s : σ) (l₁ l₂ : List (α × σ)) :
    lastOf s (l₁ ++ l₂) = lastOf (lastOf s l₁) l₂ := by
  induction l₁ generalizing s with
  | nil => rfl
  | cons p l ih => obtain ⟨a, s'⟩ := p; simpa using ih s'

/-- The final state of a trace. -/
def last (t : Trace σ α) : σ := lastOf t.1 t.2

@[simp] theorem last_mk (s : σ) (l : List (α × σ)) : last (s, l) = lastOf s l := rfl

@[simp] theorem last_nil (s : σ) : last (σ := σ) (α := α) (s, []) = s := rfl

/-- Fusion of two traces: the steps are concatenated, the shared state being counted once.  This
is meaningful when `t.last = u.1`; see `Trace.last_append`. -/
def append (t u : Trace σ α) : Trace σ α := (t.1, t.2 ++ u.2)

@[simp] theorem append_fst (t u : Trace σ α) : (t.append u).1 = t.1 := rfl

@[simp] theorem append_snd (t u : Trace σ α) : (t.append u).2 = t.2 ++ u.2 := rfl

theorem last_append {t u : Trace σ α} (h : t.last = u.1) : (t.append u).last = u.last := by
  obtain ⟨s, l⟩ := t
  obtain ⟨s', l'⟩ := u
  simp only [last_mk, append, lastOf_append]
  rw [show lastOf s l = s' from h]

end Trace

/-- A trace language: a set of traces. -/
abbrev TraceLang (σ α : Type*) := Set (Trace σ α)

namespace TraceLang

variable {σ α : Type*}

/-! ### The Kleene algebra structure -/

/-- The fusion product of two trace languages: concatenate a trace of `x` with a trace of `y`
starting in the state where the first one ends, sharing that state. -/
def fuse (x y : TraceLang σ α) : TraceLang σ α :=
  {t | ∃ l₁ l₂, t.2 = l₁ ++ l₂ ∧ (t.1, l₁) ∈ x ∧ (Trace.lastOf t.1 l₁, l₂) ∈ y}

/-- Trace languages multiply by fusion. -/
scoped instance instMul : Mul (TraceLang σ α) := ⟨fuse⟩

/-- The unit is the set of traces reduced to a single state. -/
scoped instance instOne : One (TraceLang σ α) := ⟨{t | t.2 = []}⟩

theorem mul_def (x y : TraceLang σ α) : x * y = fuse x y := rfl

theorem one_def : (1 : TraceLang σ α) = {t | t.2 = []} := rfl

theorem mem_mul {x y : TraceLang σ α} {t : Trace σ α} :
    t ∈ x * y ↔ ∃ l₁ l₂, t.2 = l₁ ++ l₂ ∧ (t.1, l₁) ∈ x ∧ (Trace.lastOf t.1 l₁, l₂) ∈ y :=
  Iff.rfl

theorem mem_mul_mk {x y : TraceLang σ α} {s : σ} {l : List (α × σ)} :
    (s, l) ∈ x * y ↔ ∃ l₁ l₂, l = l₁ ++ l₂ ∧ (s, l₁) ∈ x ∧ (Trace.lastOf s l₁, l₂) ∈ y :=
  Iff.rfl

theorem mem_one {t : Trace σ α} : t ∈ (1 : TraceLang σ α) ↔ t.2 = [] := Iff.rfl

theorem append_mem_mul {x y : TraceLang σ α} {t u : Trace σ α} (ht : t ∈ x) (hu : u ∈ y)
    (h : t.last = u.1) : t.append u ∈ x * y := by
  obtain ⟨s, l⟩ := t
  obtain ⟨s', l'⟩ := u
  refine ⟨l, l', rfl, ht, ?_⟩
  change (Trace.lastOf s l, l') ∈ y
  rw [show Trace.lastOf s l = s' from h]
  exact hu

theorem fuse_assoc (x y z : TraceLang σ α) : fuse (fuse x y) z = fuse x (fuse y z) := by
  ext ⟨s, l⟩
  constructor
  · rintro ⟨l₁, l₃, rfl, ⟨la, lb, rfl, hx, hy⟩, hz⟩
    exact ⟨la, lb ++ l₃, by simp, hx, lb, l₃, rfl, hy, by simpa using hz⟩
  · rintro ⟨la, l₂, rfl, hx, lb, lc, rfl, hy, hz⟩
    exact ⟨la ++ lb, lc, by simp, ⟨la, lb, rfl, hx, hy⟩, by simpa using hz⟩

/-- Trace languages form a monoid under the fusion product. -/
scoped instance instMonoid : Monoid (TraceLang σ α) where
  mul_assoc := fuse_assoc
  one_mul x := by
    ext ⟨s, l⟩
    constructor
    · rintro ⟨l₁, l₂, rfl, (rfl : l₁ = []), h⟩
      simpa using h
    · intro h
      exact ⟨[], l, rfl, rfl, h⟩
  mul_one x := by
    ext ⟨s, l⟩
    constructor
    · rintro ⟨l₁, l₂, rfl, h, (rfl : l₂ = [])⟩
      simpa using h
    · intro h
      exact ⟨l, [], (List.append_nil l).symm, h, rfl⟩
  npow := npowRec

/-- The fusion product distributes over arbitrary unions. -/
scoped instance instIsQuantale : IsQuantale (TraceLang σ α) where
  mul_sSup_distrib x S := by
    ext ⟨s, l⟩
    simp only [Set.sSup_eq_sUnion, Set.iSup_eq_iUnion, Set.mem_iUnion, Set.mem_sUnion,
      mem_mul_mk, exists_prop]
    constructor
    · rintro ⟨l₁, l₂, hl, hx, y, hy, h⟩
      exact ⟨y, hy, l₁, l₂, hl, hx, h⟩
    · rintro ⟨y, hy, l₁, l₂, hl, hx, h⟩
      exact ⟨l₁, l₂, hl, hx, y, hy, h⟩
  sSup_mul_distrib S y := by
    ext ⟨s, l⟩
    simp only [Set.sSup_eq_sUnion, Set.iSup_eq_iUnion, Set.mem_iUnion, Set.mem_sUnion,
      mem_mul_mk, exists_prop]
    constructor
    · rintro ⟨l₁, l₂, hl, ⟨x, hx, h⟩, hy⟩
      exact ⟨x, hx, l₁, l₂, hl, h, hy⟩
    · rintro ⟨x, hx, l₁, l₂, hl, h, hy⟩
      exact ⟨l₁, l₂, hl, ⟨x, hx, h⟩, hy⟩

/-- Trace languages form an idempotent semiring, with `+ = ∪` and `0 = ∅`. -/
scoped instance instIdemSemiring : IdemSemiring (TraceLang σ α) :=
  IdemSemiring.ofQuantale (TraceLang σ α)

/-- Trace languages form a Kleene algebra, with `x∗ = ⨆ n, x ^ n`. -/
scoped instance instKleeneAlgebra : KleeneAlgebra (TraceLang σ α) :=
  KleeneAlgebra.ofQuantale (TraceLang σ α)

/-- Trace languages form a complete Kleene algebra. -/
scoped instance instCompleteKleeneAlgebra : CompleteKleeneAlgebra (TraceLang σ α) where
  __ := instKleeneAlgebra
  __ := (inferInstance : CompleteLattice (Set (Trace σ α)))
  mul_sSup_distrib := IsQuantale.mul_sSup_distrib
  sSup_mul_distrib := IsQuantale.sSup_mul_distrib

theorem zero_def : (0 : TraceLang σ α) = ∅ := rfl

theorem add_def (x y : TraceLang σ α) : x + y = x ∪ y := rfl

theorem le_def {x y : TraceLang σ α} : x ≤ y ↔ x ⊆ y := Iff.rfl

theorem mem_zero {t : Trace σ α} : t ∉ (0 : TraceLang σ α) := id

theorem mem_add {x y : TraceLang σ α} {t : Trace σ α} : t ∈ x + y ↔ t ∈ x ∨ t ∈ y := Iff.rfl

/-- `x∗ = ⨆ n, x ^ n`: the trace model is star-continuous. -/
theorem kstar_eq_iSup_pow (x : TraceLang σ α) : x∗ = ⨆ n : ℕ, x ^ n :=
  CompleteKleeneAlgebra.kstar_eq_iSup_pow x

theorem mem_kstar {x : TraceLang σ α} {t : Trace σ α} : t ∈ x∗ ↔ ∃ n : ℕ, t ∈ x ^ n := by
  rw [kstar_eq_iSup_pow, Set.iSup_eq_iUnion]
  exact Set.mem_iUnion

theorem mem_pow_zero {x : TraceLang σ α} {t : Trace σ α} : t ∈ x ^ 0 ↔ t.2 = [] := by
  rw [pow_zero]; exact mem_one

theorem mem_pow_succ {x : TraceLang σ α} {s : σ} {l : List (α × σ)} {n : ℕ} :
    (s, l) ∈ x ^ (n + 1) ↔
      ∃ l₁ l₂, l = l₁ ++ l₂ ∧ (s, l₁) ∈ x ∧ (Trace.lastOf s l₁, l₂) ∈ x ^ n := by
  rw [pow_succ']; exact mem_mul_mk

/-! ### Decomposing a trace of `x∗` -/

/-- `FuseChain x s ls` says that the blocks of steps `ls` are the step lists of consecutive
traces of `x`, the first one starting in state `s` and each subsequent one starting where the
previous one ends. -/
def FuseChain (x : TraceLang σ α) : σ → List (List (α × σ)) → Prop
  | _, [] => True
  | s, l :: ls => (s, l) ∈ x ∧ FuseChain x (Trace.lastOf s l) ls

@[simp] theorem fuseChain_nil {x : TraceLang σ α} (s : σ) : FuseChain x s [] := trivial

@[simp] theorem fuseChain_cons {x : TraceLang σ α} (s : σ) (l : List (α × σ))
    (ls : List (List (α × σ))) :
    FuseChain x s (l :: ls) ↔ (s, l) ∈ x ∧ FuseChain x (Trace.lastOf s l) ls := Iff.rfl

/-- Membership in `x ^ n`: the steps split into `n` consecutive fusible blocks, each a trace
of `x`. -/
theorem mem_pow_iff {x : TraceLang σ α} {n : ℕ} :
    ∀ {s : σ} {l : List (α × σ)}, (s, l) ∈ x ^ n ↔
      ∃ ls : List (List (α × σ)), ls.length = n ∧ l = ls.flatten ∧ FuseChain x s ls := by
  induction n with
  | zero =>
    intro s l
    rw [mem_pow_zero]
    constructor
    · rintro (rfl : l = [])
      exact ⟨[], rfl, rfl, trivial⟩
    · rintro ⟨ls, hlen, rfl, -⟩
      rw [List.length_eq_zero_iff.1 hlen, List.flatten_nil]
  | succ n ih =>
    intro s l
    rw [mem_pow_succ]
    constructor
    · rintro ⟨l₁, l₂, rfl, hx, h⟩
      obtain ⟨ls, hlen, rfl, hch⟩ := ih.1 h
      exact ⟨l₁ :: ls, by simp [hlen], by simp, hx, hch⟩
    · rintro ⟨ls, hlen, rfl, hch⟩
      obtain ⟨l₁, ls, rfl⟩ : ∃ l₁ ls', ls = l₁ :: ls' := by
        cases ls with
        | nil => simp at hlen
        | cons l₁ ls' => exact ⟨l₁, ls', rfl⟩
      obtain ⟨hx, hch⟩ := hch
      refine ⟨l₁, ls.flatten, by simp, hx, ih.2 ⟨ls, by simpa using hlen, rfl, hch⟩⟩

/-- Membership in `x∗`: the steps split into finitely many consecutive fusible blocks, each a
trace of `x`. -/
theorem mem_kstar_iff_fuseChain {x : TraceLang σ α} {s : σ} {l : List (α × σ)} :
    (s, l) ∈ x∗ ↔ ∃ ls : List (List (α × σ)), l = ls.flatten ∧ FuseChain x s ls := by
  rw [mem_kstar]
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨ls, -, hl, hch⟩ := mem_pow_iff.1 hn
    exact ⟨ls, hl, hch⟩
  · rintro ⟨ls, hl, hch⟩
    exact ⟨ls.length, mem_pow_iff.2 ⟨ls, rfl, hl, hch⟩⟩

/-! ### Tests: sets of states -/

/-- The trace language associated with a set of states `P`: all traces reduced to a single
state lying in `P`. -/
def ofStates (P : Set σ) : TraceLang σ α := {t | t.2 = [] ∧ t.1 ∈ P}

theorem mem_ofStates {P : Set σ} {t : Trace σ α} : t ∈ ofStates P ↔ t.2 = [] ∧ t.1 ∈ P := Iff.rfl

theorem mem_ofStates_mk {P : Set σ} {s : σ} {l : List (α × σ)} :
    (s, l) ∈ (ofStates P : TraceLang σ α) ↔ l = [] ∧ s ∈ P := Iff.rfl

@[simp] theorem ofStates_empty : (ofStates ∅ : TraceLang σ α) = 0 := by
  ext ⟨s, l⟩; simp [mem_ofStates_mk, zero_def]

@[simp] theorem ofStates_univ : (ofStates Set.univ : TraceLang σ α) = 1 := by
  ext ⟨s, l⟩; simp [mem_ofStates_mk, one_def]

theorem ofStates_union (P Q : Set σ) :
    (ofStates (P ∪ Q) : TraceLang σ α) = ofStates P + ofStates Q := by
  ext ⟨s, l⟩
  simp only [mem_ofStates_mk, Set.mem_union, mem_add, mem_ofStates_mk]
  tauto

theorem ofStates_inter (P Q : Set σ) :
    (ofStates (P ∩ Q) : TraceLang σ α) = ofStates P * ofStates Q := by
  ext ⟨s, l⟩
  constructor
  · rintro ⟨hl, hP, hQ⟩
    exact ⟨[], l, rfl, ⟨rfl, hP⟩, hl, hQ⟩
  · rintro ⟨l₁, l₂, rfl, ⟨(rfl : l₁ = []), hP⟩, hl₂, hQ⟩
    exact ⟨by simpa using hl₂, hP, hQ⟩

theorem ofStates_le_one (P : Set σ) : (ofStates P : TraceLang σ α) ≤ 1 := fun _ h ↦ h.1

theorem ofStates_injective : Function.Injective (ofStates : Set σ → TraceLang σ α) := by
  intro P Q h
  ext s
  have := congrArg (fun x : TraceLang σ α ↦ (s, ([] : List (α × σ))) ∈ x) h
  simpa [mem_ofStates_mk] using this

/-- Trace languages form a Kleene algebra with tests, the tests being the sets of states. -/
scoped instance instKAT : KleeneAlgebraWithTests (Set σ) (TraceLang σ α) where
  test := ofStates
  test_bot := ofStates_empty
  test_top := ofStates_univ
  test_sup := ofStates_union
  test_inf := ofStates_inter

theorem test_def (P : Set σ) : (KAT.test P : TraceLang σ α) = ofStates P := rfl

/-! ### Actions -/

/-- The trace language of a single action `a`: all traces `s a s'` with one step, labelled `a`. -/
def ofAction (a : α) : TraceLang σ α := {t | ∃ s s', t = (s, [(a, s')])}

theorem mem_ofAction {a : α} {s : σ} {l : List (α × σ)} :
    (s, l) ∈ (ofAction a : TraceLang σ α) ↔ ∃ s', l = [(a, s')] := by
  constructor
  · rintro ⟨s₀, s', h⟩
    obtain ⟨-, rfl⟩ := Prod.mk.injEq .. ▸ h
    exact ⟨s', rfl⟩
  · rintro ⟨s', rfl⟩
    exact ⟨s, s', rfl⟩

theorem mk_mem_ofAction (a : α) (s s' : σ) : (s, [(a, s')]) ∈ (ofAction a : TraceLang σ α) :=
  ⟨s, s', rfl⟩

theorem snd_of_mem_ofAction {a : α} {t : Trace σ α}
    (h : t ∈ (ofAction a : TraceLang σ α)) : ∃ s', t.2 = [(a, s')] := by
  obtain ⟨s, s', rfl⟩ := h
  exact ⟨s', rfl⟩

theorem ofAction_ne_zero [Nonempty σ] (a : α) : (ofAction a : TraceLang σ α) ≠ 0 := by
  intro h
  exact mem_zero (h ▸ mk_mem_ofAction a (Classical.arbitrary σ) (Classical.arbitrary σ))

theorem ofAction_injective [Nonempty σ] :
    Function.Injective (ofAction : α → TraceLang σ α) := by
  intro a b h
  have hmem : (Classical.arbitrary σ, [(a, Classical.arbitrary σ)]) ∈
      (ofAction b : TraceLang σ α) := h ▸ mk_mem_ofAction a _ _
  obtain ⟨s', hs'⟩ := mem_ofAction.1 hmem
  simp only [List.cons.injEq, Prod.mk.injEq, and_true] at hs'
  exact hs'.1

theorem ofStates_mul_ofAction (P : Set σ) (a : α) :
    (ofStates P : TraceLang σ α) * ofAction a = {t | ∃ s s', t = (s, [(a, s')]) ∧ s ∈ P} := by
  ext ⟨s, l⟩
  constructor
  · rintro ⟨l₁, l₂, rfl, ⟨(rfl : l₁ = []), hP⟩, h⟩
    obtain ⟨s', rfl⟩ := mem_ofAction.1 h
    exact ⟨s, s', rfl, hP⟩
  · rintro ⟨s₀, s', h, hP⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ h
    exact ⟨[], [(a, s')], rfl, ⟨rfl, hP⟩, mk_mem_ofAction a s s'⟩

/-! ### Languages of finite words

Traces over a one-element state type are exactly words: the states carry no information.  This
section makes the isomorphism with Mathlib's `Language α` explicit.
-/

end TraceLang

namespace Trace

variable {α : Type*}

/-- The word underlying a trace over a one-element state type. -/
def toWord (t : Trace Unit α) : List α := t.2.map Prod.fst

/-- The trace over a one-element state type underlying a word. -/
def ofWord (w : List α) : Trace Unit α := ((), w.map fun a ↦ (a, ()))

@[simp] theorem ofWord_snd (w : List α) : (ofWord w).2 = w.map fun a ↦ (a, ()) := rfl

@[simp] theorem toWord_ofWord (w : List α) : toWord (ofWord w) = w := by
  simp [toWord, ofWord, List.map_map, Function.comp_def]

@[simp] theorem ofWord_toWord (t : Trace Unit α) : ofWord (toWord t) = t := by
  obtain ⟨u, l⟩ := t
  simp only [toWord, ofWord, Prod.mk.injEq, true_and]
  induction l with
  | nil => rfl
  | cons p l ih => obtain ⟨a, u'⟩ := p; simpa using ih

theorem ofWord_append (w₁ w₂ : List α) :
    ofWord (w₁ ++ w₂) = (ofWord w₁).append (ofWord w₂) := by
  simp [ofWord, append]

theorem ofWord_injective : Function.Injective (ofWord : List α → Trace Unit α) :=
  Function.LeftInverse.injective toWord_ofWord

end Trace

namespace TraceLang

variable {α : Type*}

/-- The language of words underlying a trace language over a one-element state type. -/
def toLanguage (x : TraceLang Unit α) : Language α := Trace.ofWord ⁻¹' x

/-- The trace language over a one-element state type underlying a language of words. -/
def ofLanguage (L : Language α) : TraceLang Unit α := Trace.toWord ⁻¹' L

theorem mem_toLanguage {x : TraceLang Unit α} {w : List α} :
    w ∈ toLanguage x ↔ Trace.ofWord w ∈ x := Iff.rfl

theorem mem_ofLanguage {L : Language α} {t : Trace Unit α} :
    t ∈ ofLanguage L ↔ Trace.toWord t ∈ L := Iff.rfl

@[simp] theorem toLanguage_ofLanguage (L : Language α) : toLanguage (ofLanguage L) = L := by
  ext w; simp [mem_toLanguage, mem_ofLanguage]

@[simp] theorem ofLanguage_toLanguage (x : TraceLang Unit α) : ofLanguage (toLanguage x) = x := by
  ext t; simp [mem_toLanguage, mem_ofLanguage]

theorem toLanguage_injective : Function.Injective (toLanguage : TraceLang Unit α → Language α) :=
  Function.LeftInverse.injective ofLanguage_toLanguage

@[simp] theorem toLanguage_zero : toLanguage (0 : TraceLang Unit α) = 0 := rfl

@[simp] theorem toLanguage_one : toLanguage (1 : TraceLang Unit α) = 1 := by
  ext w
  simp [mem_toLanguage, one_def]

@[simp] theorem toLanguage_add (x y : TraceLang Unit α) :
    toLanguage (x + y) = toLanguage x + toLanguage y := rfl

@[simp] theorem toLanguage_mul (x y : TraceLang Unit α) :
    toLanguage (x * y) = toLanguage x * toLanguage y := by
  ext w
  simp only [mem_toLanguage, mem_mul, Language.mem_mul]
  constructor
  · rintro ⟨l₁, l₂, hl, hx, hy⟩
    refine ⟨l₁.map Prod.fst, ?_, l₂.map Prod.fst, ?_, ?_⟩
    · rwa [show Trace.ofWord (l₁.map Prod.fst) = ((), l₁) from Trace.ofWord_toWord ((), l₁)]
    · rwa [show Trace.ofWord (l₂.map Prod.fst) = ((), l₂) from Trace.ofWord_toWord ((), l₂)]
    · rw [← List.map_append, ← hl, Trace.ofWord_snd, List.map_map, Function.comp_def]
      simp
  · rintro ⟨w₁, hx, w₂, hy, rfl⟩
    refine ⟨(Trace.ofWord w₁).2, (Trace.ofWord w₂).2, ?_, hx, hy⟩
    simp [Trace.ofWord]

@[simp] theorem toLanguage_pow (x : TraceLang Unit α) (n : ℕ) :
    toLanguage (x ^ n) = toLanguage x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, toLanguage_mul, ih]

theorem toLanguage_iSup {ι : Sort*} (f : ι → TraceLang Unit α) :
    toLanguage (⨆ i, f i) = ⨆ i, toLanguage (f i) := by
  ext w
  simp only [toLanguage, Set.iSup_eq_iUnion, Set.preimage_iUnion]
  rfl

@[simp] theorem toLanguage_kstar (x : TraceLang Unit α) : toLanguage x∗ = (toLanguage x)∗ := by
  rw [kstar_eq_iSup_pow, Language.kstar_eq_iSup_pow, toLanguage_iSup]
  exact iSup_congr fun n ↦ toLanguage_pow x n

theorem toLanguage_le_toLanguage {x y : TraceLang Unit α} :
    toLanguage x ≤ toLanguage y ↔ x ≤ y := by
  constructor
  · intro h t ht
    have h1 : Trace.toWord t ∈ toLanguage x := by rwa [mem_toLanguage, Trace.ofWord_toWord]
    have h2 : Trace.ofWord (Trace.toWord t) ∈ y := mem_toLanguage.1 (h h1)
    rwa [Trace.ofWord_toWord] at h2
  · exact fun h _ hw ↦ h hw

/-- Trace languages over a one-element state type are exactly languages of finite words. -/
def languageEquiv : TraceLang Unit α ≃ Language α where
  toFun := toLanguage
  invFun := ofLanguage
  left_inv := ofLanguage_toLanguage
  right_inv := toLanguage_ofLanguage

@[simp] theorem languageEquiv_apply (x : TraceLang Unit α) : languageEquiv x = toLanguage x := rfl

@[simp] theorem languageEquiv_symm_apply (L : Language α) :
    languageEquiv.symm L = ofLanguage L := rfl

/-- The isomorphism between trace languages over a one-element state type and languages of
finite words is multiplicative. -/
def languageMulEquiv : TraceLang Unit α ≃* Language α where
  __ := languageEquiv
  map_mul' := toLanguage_mul

/-- The isomorphism between trace languages over a one-element state type and languages of
finite words is an order isomorphism. -/
def languageOrderIso : TraceLang Unit α ≃o Language α where
  __ := languageEquiv
  map_rel_iff' := toLanguage_le_toLanguage

/-! ### Guarded strings

Taking the states to be the *atoms* of a Boolean algebra of tests yields the model of **guarded
string languages**, the free KAT (Kozen–Smith).  A guarded string `α₀ p₁ α₁ ⋯ pₙ αₙ` is exactly a
trace whose states are atoms, and the fusion product above is the usual fusion product of guarded
strings.

Nothing new is needed: `TraceLang.instKAT` already exhibits `TraceLang σ α` as a KAT over
`Set σ`.  When the tests form an abstract Boolean algebra `T` mapping to `Set σ` (for instance,
`T` the Boolean expressions over test variables and `σ` the atoms, with `f b` the set of atoms
satisfying `b`), the KAT structure transports along that map: see `TraceLang.katOfHom`.

A concrete, computational development of guarded strings over the atoms `List Bool` — with
derivatives and the bisimulation checker used by the `kat` tactic — is carried out independently
in `RelationAlgebra.Decide.GuardedString`; there `KAT.GStr` is the same representation as
`Trace (List Bool) ℕ` here, and `KAT.fuse` is `TraceLang.fuse` restricted to well-formed atoms.
-/

variable {σ : Type*}

/-- Transporting the KAT structure along a map of tests: if `T` is a Boolean algebra of tests
mapped to sets of states by a bounded lattice homomorphism `f`, then `TraceLang σ α` is a Kleene
algebra with tests over `T`.  This is the general form of the guarded string model of
`glang.v`, where `T` is the Boolean algebra of test expressions and `f b` is the set of atoms
satisfying `b`. -/
@[reducible] def katOfHom {T : Type*} [BooleanAlgebra T] (f : BoundedLatticeHom T (Set σ)) :
    KAT T (TraceLang σ α) where
  test P := ofStates (f P)
  test_bot := by rw [map_bot]; exact ofStates_empty
  test_top := by rw [map_top, Set.top_eq_univ]; exact ofStates_univ
  test_sup a b := by rw [map_sup]; exact ofStates_union _ _
  test_inf a b := by rw [map_inf]; exact ofStates_inter _ _

theorem katOfHom_test {T : Type*} [BooleanAlgebra T] (f : BoundedLatticeHom T (Set σ)) (P : T) :
    @KAT.test T (TraceLang σ α) _ _ (katOfHom f) P = ofStates (f P) := rfl

end TraceLang

/-- Guarded string languages: trace languages whose states are thought of as the atoms of a
Boolean algebra of tests.  See the section `Guarded strings` above and the independent
development in `RelationAlgebra.Decide.GuardedString`. -/
abbrev GuardedLang (σ α : Type*) := TraceLang σ α
