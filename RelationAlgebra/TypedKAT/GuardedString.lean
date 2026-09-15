import RelationAlgebra.TypedKAT.Syntax

/-!
# Typed guarded-string semantics

`PathTyped src tgt X actions Y` says that the actions form a composable path from `X` to
`Y`. In particular, the empty path can only go from an object to itself.
`Language src tgt k X Y` is a set of guarded strings together with proofs that every string
follows such a path and that all its atoms have length `k`.

The language operations enforce the same endpoints as `TypedKAT.Term`. Composition uses
fusion: the final atom of the first string must equal the initial atom of the second.
`Term.lang` gives the semantics of typed expressions in these languages.

`Term.strings_lang` proves that forgetting the typing proofs gives exactly the existing
guarded-string semantics of the erased expression. This is a statement about languages,
not an algebraic untyping or completeness theorem. It gives a bridge to the existing
derivative checker. `RelationAlgebra.TypedKATCompleteness.Main` supplies the separate
completeness proof and reflection lemmas for arbitrary typed KATs.

This development follows the typed syntax and guarded-string semantics of Damien Pous's
[`relation-algebra`](https://github.com/damien-pous/relation-algebra) (`theories/gregex.v`,
`glang.v`, `traces.v`, and `kat_untyping.v`), revision
`2d2af3631929399bbac56f57b3e15302d8697e1c`.
-/

namespace TypedKAT

universe u

variable {I : Type u} {src tgt : ℕ → I} {X Y Z : I}

/-- The actions form a path with the specified endpoints. Atoms carry Boolean valuations,
so object typing is determined entirely by the actions. -/
def PathTyped (src tgt : ℕ → I) : I → List ℕ → I → Prop
  | X, [], Y => X = Y
  | X, a :: l, Y => X = src a ∧ PathTyped src tgt (tgt a) l Y

namespace PathTyped

@[simp] theorem nil : PathTyped src tgt X [] Y ↔ X = Y := Iff.rfl

@[simp] theorem cons (a : ℕ) (l : List ℕ) :
    PathTyped src tgt X (a :: l) Y ↔ X = src a ∧ PathTyped src tgt (tgt a) l Y := Iff.rfl

/-- A concatenated path has an intermediate object at every split. -/
theorem append_iff (l r : List ℕ) :
    PathTyped src tgt X (l ++ r) Z ↔
      ∃ Y, PathTyped src tgt X l Y ∧ PathTyped src tgt Y r Z := by
  induction l generalizing X with
  | nil => simp
  | cons a l ih =>
    simp only [List.cons_append, cons, ih]
    constructor
    · rintro ⟨h, Y, hl, hr⟩
      exact ⟨Y, ⟨h, hl⟩, hr⟩
    · rintro ⟨Y, ⟨h, hl⟩, hr⟩
      exact ⟨h, Y, hl, hr⟩

theorem append {l r : List ℕ} (hl : PathTyped src tgt X l Y)
    (hr : PathTyped src tgt Y r Z) : PathTyped src tgt X (l ++ r) Z :=
  (append_iff l r).2 ⟨Y, hl, hr⟩

/-- Relabelling objects preserves paths, including when distinct objects are identified. -/
theorem map {J : Type*} (f : I → J) {l : List ℕ} (h : PathTyped src tgt X l Y) :
    PathTyped (f ∘ src) (f ∘ tgt) (f X) l (f Y) := by
  induction l generalizing X with
  | nil => exact congrArg f h
  | cons a l ih => exact ⟨congrArg f h.1, ih h.2⟩

end PathTyped

/-- A guarded-string language from `X` to `Y` using atoms of length `k`. The fields certify
path typing and atom bounds; they do not assert any algebraic completeness result. -/
structure Language (src tgt : ℕ → I) (k : ℕ) (X Y : I) where
  /-- The underlying set, using the representation shared with the untyped checker. -/
  strings : Set KAT.GStr
  /-- Every action sequence has the claimed endpoints. -/
  pathTyped : ∀ g ∈ strings, PathTyped src tgt X (g.2.map Prod.fst) Y
  /-- Every atom has the declared length. -/
  wellFormed : ∀ g ∈ strings, KAT.GStr.wf k g

namespace Language

variable {k : ℕ}

@[ext] theorem ext {L M : Language src tgt k X Y} (h : L.strings = M.strings) : L = M := by
  cases L
  cases M
  cases h
  rfl

theorem strings_injective : Function.Injective (strings : Language src tgt k X Y → _) :=
  fun _ _ h ↦ ext h

/-- The empty language, between any two objects. -/
def zero : Language src tgt k X Y where
  strings := ∅
  pathTyped _ h := False.elim h
  wellFormed _ h := False.elim h

/-- The identity language: all single atoms of length `k`, at one object. -/
def one : Language src tgt k X X where
  strings := KAT.unitGS k
  pathTyped _ h := by simp [h.1]
  wellFormed := KAT.GStr.wf_unitGS

/-- The language of a Boolean test, embedded at one object. -/
def test (b : KAT.BTerm) : Language src tgt k X X where
  strings := (KAT.KTerm.test b).gs k
  pathTyped _ h := by simp [KAT.KTerm.gs] at h; simp [h.1]
  wellFormed := KAT.KTerm.wf_of_mem_gs (.test b)

/-- The language of one action, with its declared source and target. -/
def act (a : ℕ) : Language src tgt k (src a) (tgt a) where
  strings := (KAT.KTerm.act a).gs k
  pathTyped _ h := by
    obtain ⟨α, β, rfl, _, _⟩ := h
    simp
  wellFormed := KAT.KTerm.wf_of_mem_gs (.act a)

/-- Union of parallel languages. -/
def add (L M : Language src tgt k X Y) : Language src tgt k X Y where
  strings := L.strings ∪ M.strings
  pathTyped g h := h.elim (L.pathTyped g) (M.pathTyped g)
  wellFormed g h := h.elim (L.wellFormed g) (M.wellFormed g)

/-- Fusion of languages with matching endpoints. In addition to the object boundary, the
two strings must agree on the atom where they meet (enforced by `KAT.fuse`). -/
def comp (L : Language src tgt k X Y) (M : Language src tgt k Y Z) :
    Language src tgt k X Z where
  strings := KAT.fuse L.strings M.strings
  pathTyped _ h := by
    obtain ⟨α, l, r, rfl, hl, hr⟩ := h
    simpa only [List.map_append] using (L.pathTyped _ hl).append (M.pathTyped _ hr)
  wellFormed := KAT.GStr.wf_fuse L.wellFormed M.wellFormed

/-- A fixed number of repetitions of an endomorphism language. -/
def pow (L : Language src tgt k X X) : ℕ → Language src tgt k X X
  | 0 => one
  | n + 1 => comp L (pow L n)

@[simp] theorem strings_pow (L : Language src tgt k X X) (n : ℕ) :
    (L.pow n).strings = KAT.fusePow k L.strings n := by
  induction n with
  | zero => rfl
  | succ n ih => change KAT.fuse L.strings (L.pow n).strings = _; rw [ih]; rfl

/-- Zero or more repetitions of an endomorphism language. -/
def star (L : Language src tgt k X X) : Language src tgt k X X where
  strings := ⋃ n, (L.pow n).strings
  pathTyped g h := by
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 h
    exact (L.pow n).pathTyped g hn
  wellFormed g h := by
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 h
    exact (L.pow n).wellFormed g hn

@[simp] theorem strings_star (L : Language src tgt k X X) :
    L.star.strings = ⋃ n, KAT.fusePow k L.strings n := by
  simp only [star, strings_pow]

end Language

namespace Term

/-- Interpret expressions as typed guarded-string languages. A finite bound is part of the
semantics; applying algebraic completeness will additionally require `e.tvarsBelow k`. -/
def lang (k : ℕ) : {A B : I} → Term src tgt A B → Language src tgt k A B
  | _, _, .zero => .zero
  | _, _, .one => .one
  | _, _, .test b => .test b
  | _, _, .act a => .act a
  | _, _, .add e f => .add (e.lang k) (f.lang k)
  | _, _, .comp e f => .comp (e.lang k) (f.lang k)
  | _, _, .star e => .star (e.lang k)

/-- Erasure preserves the underlying guarded-string language exactly. In particular, it
does not introduce paths that violate the original source and target constraints. -/
@[simp] theorem strings_lang (e : Term src tgt X Y) (k : ℕ) :
    (e.lang k).strings = e.erase.gs k := by
  induction e with
  | zero => rfl
  | one => rfl
  | test _ => rfl
  | act _ => rfl
  | add e f he hf => exact congrArg₂ (· ∪ ·) he hf
  | comp e f he hf => exact congrArg₂ KAT.fuse he hf
  | star e he => simp only [lang, Language.strings_star, he, erase, KAT.KTerm.gs]

/-- Every string accepted by an erased typed expression still has a valid typed path. -/
theorem pathTyped_of_mem_erase {e : Term src tgt X Y} {k : ℕ} {g : KAT.GStr}
    (h : g ∈ e.erase.gs k) : PathTyped src tgt X (g.2.map Prod.fst) Y :=
  (e.lang k).pathTyped g (by simpa only [strings_lang] using h)

/-- Equality of typed languages is equivalent to equality after forgetting typing proofs.
The connection to arbitrary typed KATs is proved in `TypedKATCompleteness/Main.lean`. -/
theorem lang_eq_iff (e f : Term src tgt X Y) (k : ℕ) :
    e.lang k = f.lang k ↔ e.erase.gs k = f.erase.gs k := by
  constructor
  · intro h
    simpa only [strings_lang] using congrArg Language.strings h
  · intro h
    apply Language.ext
    simpa only [strings_lang] using h

/-- A successful untyped certificate establishes equality of the typed *languages*.
`TypedKAT.Completeness.eval_eq_of_decideEq` supplies the step to arbitrary typed KATs. -/
theorem lang_eq_of_decideEq {e f : Term src tgt X Y} {k fuel : ℕ}
    (h : KAT.KTerm.decideEq k e.erase f.erase fuel = true) : e.lang k = f.lang k :=
  (lang_eq_iff e f k).2 (KAT.KTerm.gs_eq_of_decideEq h)

end Term
end TypedKAT
