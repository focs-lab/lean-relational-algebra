import RelationAlgebra.TypedKAT.GuardedString

/-!
# The typed guarded-string language model

`LanguageCat src tgt k` bundles the existing `TypedKAT.Language` hom-sets as a Kleene
category with tests. Objects wrap the action alphabet's objects, so this category instance
does not conflict with any category already defined on that type. Tests are sets of atoms
of length `k`, embedded as languages containing only those single atoms.

This is a model of all well-typed guarded-string languages at a fixed atom bound. The free
model of expressions modulo semantic equivalence and its universal property are developed
separately in `TypedKAT/Free.lean`. The model follows `glang.v` in Damien Pous'
`relation-algebra` library.
-/

open CategoryTheory
open scoped Computability

universe u

namespace TypedKAT

namespace Language

variable {I : Type u} {src tgt : ℕ → I} {k : ℕ} {W X Y Z : I}

instance : PartialOrder (Language src tgt k X Y) :=
  PartialOrder.lift strings strings_injective

instance : SemilatticeSup (Language src tgt k X Y) where
  sup := add
  le_sup_left _ _ := Set.subset_union_left
  le_sup_right _ _ := Set.subset_union_right
  sup_le _ _ _ := Set.union_subset

instance : OrderBot (Language src tgt k X Y) where
  bot := zero
  bot_le _ := Set.empty_subset _

@[simp] theorem le_def {L M : Language src tgt k X Y} : L ≤ M ↔ L.strings ⊆ M.strings :=
  Iff.rfl

@[simp] theorem strings_bot : (⊥ : Language src tgt k X Y).strings = ∅ := rfl

@[simp] theorem strings_sup (L M : Language src tgt k X Y) :
    (L ⊔ M).strings = L.strings ∪ M.strings := rfl

private theorem last_append (α : KAT.Atom) (l r : List (ℕ × KAT.Atom)) :
    KAT.GStr.last α (l ++ r) = KAT.GStr.last (KAT.GStr.last α l) r := by
  induction l generalizing α with
  | nil => rfl
  | cons p l ih => exact ih p.2

theorem comp_assoc (L : Language src tgt k W X) (M : Language src tgt k X Y)
    (N : Language src tgt k Y Z) : (L.comp M).comp N = L.comp (M.comp N) := by
  apply ext
  change KAT.fuse (KAT.fuse L.strings M.strings) N.strings =
    KAT.fuse L.strings (KAT.fuse M.strings N.strings)
  ext ⟨α, l⟩
  simp only [KAT.mem_fuse]
  constructor
  · rintro ⟨l₁, l₃, rfl, ⟨la, lb, rfl, hL, hM⟩, hN⟩
    exact ⟨la, lb ++ l₃, by simp, hL, lb, l₃, rfl, hM, by simpa [last_append] using hN⟩
  · rintro ⟨la, l₂, rfl, hL, lb, lc, rfl, hM, hN⟩
    exact ⟨la ++ lb, lc, by simp, ⟨la, lb, rfl, hL, hM⟩, by simpa [last_append] using hN⟩

@[simp] theorem one_comp (L : Language src tgt k X Y) : one.comp L = L := by
  apply ext
  ext ⟨α, l⟩
  change (α, l) ∈ KAT.fuse (KAT.unitGS k) L.strings ↔ _
  rw [KAT.mem_fuse]
  constructor
  · rintro ⟨l₁, l₂, rfl, ⟨rfl, _⟩, h⟩
    exact h
  · intro h
    exact ⟨[], l, rfl, ⟨rfl, KAT.mem_allAtoms.2 (L.wellFormed _ h).1⟩, h⟩

@[simp] theorem comp_one (L : Language src tgt k X Y) : L.comp one = L := by
  apply ext
  ext ⟨α, l⟩
  change (α, l) ∈ KAT.fuse L.strings (KAT.unitGS k) ↔ _
  rw [KAT.mem_fuse]
  constructor
  · rintro ⟨l₁, l₂, rfl, h, ⟨rfl, _⟩⟩
    simpa using h
  · intro h
    exact ⟨l, [], (List.append_nil l).symm, h,
      rfl, KAT.mem_allAtoms.2 (KAT.GStr.wf_last α l (L.wellFormed _ h))⟩

theorem comp_mono {L L' : Language src tgt k X Y} {M M' : Language src tgt k Y Z}
    (hL : L ≤ L') (hM : M ≤ M') : L.comp M ≤ L'.comp M' := by
  rintro _ ⟨α, l, r, rfl, hl, hr⟩
  exact ⟨α, l, r, rfl, hL hl, hM hr⟩

@[simp] theorem bot_comp (L : Language src tgt k Y Z) :
    (⊥ : Language src tgt k X Y).comp L = ⊥ := by
  apply ext
  ext ⟨α, l⟩
  simp [comp, KAT.mem_fuse]

@[simp] theorem comp_bot (L : Language src tgt k X Y) :
    L.comp (⊥ : Language src tgt k Y Z) = ⊥ := by
  apply ext
  ext ⟨α, l⟩
  simp [comp, KAT.mem_fuse]

theorem sup_comp (L M : Language src tgt k X Y) (N : Language src tgt k Y Z) :
    (L ⊔ M).comp N = L.comp N ⊔ M.comp N := by
  apply ext
  ext ⟨α, l⟩
  simp only [comp, strings_sup, KAT.mem_fuse, Set.mem_union]
  constructor
  · rintro ⟨l₁, l₂, hl, hL | hM, hN⟩
    · exact Or.inl ⟨l₁, l₂, hl, hL, hN⟩
    · exact Or.inr ⟨l₁, l₂, hl, hM, hN⟩
  · rintro (⟨l₁, l₂, hl, hL, hN⟩ | ⟨l₁, l₂, hl, hM, hN⟩)
    · exact ⟨l₁, l₂, hl, Or.inl hL, hN⟩
    · exact ⟨l₁, l₂, hl, Or.inr hM, hN⟩

theorem comp_sup (L : Language src tgt k X Y) (M N : Language src tgt k Y Z) :
    L.comp (M ⊔ N) = L.comp M ⊔ L.comp N := by
  apply ext
  ext ⟨α, l⟩
  simp only [comp, strings_sup, KAT.mem_fuse, Set.mem_union]
  constructor
  · rintro ⟨l₁, l₂, hl, hL, hM | hN⟩
    · exact Or.inl ⟨l₁, l₂, hl, hL, hM⟩
    · exact Or.inr ⟨l₁, l₂, hl, hL, hN⟩
  · rintro (⟨l₁, l₂, hl, hL, hM⟩ | ⟨l₁, l₂, hl, hL, hN⟩)
    · exact ⟨l₁, l₂, hl, hL, Or.inl hM⟩
    · exact ⟨l₁, l₂, hl, hL, Or.inr hN⟩

theorem pow_succ_right (L : Language src tgt k X X) (n : ℕ) :
    L.pow (n + 1) = (L.pow n).comp L := by
  induction n with
  | zero => simp [pow]
  | succ n ih =>
    change L.comp (L.pow (n + 1)) = (L.comp (L.pow n)).comp L
    rw [ih, comp_assoc]

theorem one_le_star (L : Language src tgt k X X) : one ≤ L.star :=
  fun _ h ↦ Set.mem_iUnion.2 ⟨0, h⟩

theorem comp_star_le_star (L : Language src tgt k X X) : L.comp L.star ≤ L.star := by
  rintro _ ⟨α, l, r, rfl, hl, hr⟩
  obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hr
  exact Set.mem_iUnion.2 ⟨n + 1, α, l, r, rfl, hl, hn⟩

theorem star_comp_le_star (L : Language src tgt k X X) : L.star.comp L ≤ L.star := by
  rintro _ ⟨α, l, r, rfl, hl, hr⟩
  obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hl
  apply Set.mem_iUnion.2
  refine ⟨n + 1, ?_⟩
  rw [pow_succ_right]
  exact ⟨α, l, r, rfl, hn, hr⟩

/-- Star induction with a rectangular morphism on the right. -/
theorem star_comp_le_self (L : Language src tgt k X X) (M : Language src tgt k X Y)
    (h : L.comp M ≤ M) : L.star.comp M ≤ M := by
  have hp : ∀ n, (L.pow n).comp M ≤ M := by
    intro n
    induction n with
    | zero => simp [pow]
    | succ n ih =>
      change (L.comp (L.pow n)).comp M ≤ M
      rw [comp_assoc]
      exact (comp_mono le_rfl ih).trans h
  rintro _ ⟨α, l, r, rfl, hl, hr⟩
  obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hl
  exact hp n ⟨α, l, r, rfl, hn, hr⟩

/-- Star induction with a rectangular morphism on the left. -/
theorem comp_star_le_self (L : Language src tgt k X X) (M : Language src tgt k Y X)
    (h : M.comp L ≤ M) : M.comp L.star ≤ M := by
  have hp : ∀ n, M.comp (L.pow n) ≤ M := by
    intro n
    induction n with
    | zero => simp [pow]
    | succ n ih =>
      rw [pow_succ_right, ← comp_assoc]
      exact (comp_mono ih le_rfl).trans h
  rintro _ ⟨α, l, r, rfl, hl, hr⟩
  obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hr
  exact hp n ⟨α, l, r, rfl, hl, hn⟩

/-- Iteration is also available directly on endomorphism languages, including concrete
language expressions whose inferred type has unfolded the category's hom-set. -/
instance : KStar (Language src tgt k X X) := ⟨star⟩

@[simp] theorem kstar_def (L : Language src tgt k X X) : L∗ = L.star := rfl

end Language

/-- Objects of the typed guarded-string language model. The wrapper keeps the category
instance separate from other interpretations of the same object alphabet. -/
structure LanguageCat {I : Type u} (src tgt : ℕ → I) (k : ℕ) where
  /-- The underlying object of the action alphabet. -/
  object : I

namespace LanguageCat

variable {I : Type u} {src tgt : ℕ → I} {k : ℕ}

instance : Category (LanguageCat src tgt k) where
  Hom X Y := Language src tgt k X.object Y.object
  id _ := Language.one
  comp := Language.comp
  id_comp := Language.one_comp
  comp_id := Language.comp_one
  assoc := Language.comp_assoc

instance : KleeneCategory (LanguageCat src tgt k) where
  homSemilatticeSup X Y :=
    inferInstanceAs (SemilatticeSup (Language src tgt k X.object Y.object))
  homOrderBot X Y := inferInstanceAs (OrderBot (Language src tgt k X.object Y.object))
  sup_comp := Language.sup_comp
  comp_sup := Language.comp_sup
  bot_comp := Language.bot_comp
  comp_bot := Language.comp_bot
  kstar := Language.star
  id_le_kstar := Language.one_le_star
  comp_kstar_le_kstar := Language.comp_star_le_star
  kstar_comp_le_kstar := Language.star_comp_le_star
  comp_kstar_le_self := Language.comp_star_le_self
  kstar_comp_le_self := Language.star_comp_le_self

end LanguageCat

/-- A Boolean valuation for exactly `k` primitive test variables. -/
abbrev BoundedAtom (k : ℕ) := {α : KAT.Atom // α.length = k}

namespace Language

variable {I : Type u} {src tgt : ℕ → I} {k : ℕ} {X : I}

/-- Embed a set of bounded atoms as a language of single atoms at one object. -/
def ofAtoms (P : Set (BoundedAtom k)) : Language src tgt k X X where
  strings := {g | g.2 = [] ∧ ∃ h : g.1.length = k, ⟨g.1, h⟩ ∈ P}
  pathTyped g h := by simp [h.1]
  wellFormed := by
    rintro ⟨α, l⟩ ⟨rfl, ha, _⟩
    exact ⟨ha, by simp⟩

@[simp] theorem mem_ofAtoms {P : Set (BoundedAtom k)} {α : KAT.Atom}
    {l : List (ℕ × KAT.Atom)} :
    (α, l) ∈ (ofAtoms P : Language src tgt k X X).strings ↔
      l = [] ∧ ∃ h : α.length = k, ⟨α, h⟩ ∈ P := Iff.rfl

@[simp] theorem ofAtoms_bot : (ofAtoms ⊥ : Language src tgt k X X) = ⊥ := by
  apply ext
  ext ⟨α, l⟩
  simp

@[simp] theorem ofAtoms_top : (ofAtoms ⊤ : Language src tgt k X X) = one := by
  apply ext
  ext ⟨α, l⟩
  simp [one, KAT.unitGS, KAT.mem_allAtoms]

theorem ofAtoms_sup (P Q : Set (BoundedAtom k)) :
    (ofAtoms (P ⊔ Q) : Language src tgt k X X) = ofAtoms P ⊔ ofAtoms Q := by
  apply ext
  ext ⟨α, l⟩
  simp only [mem_ofAtoms, strings_sup, Set.mem_union, Set.sup_eq_union]
  constructor
  · rintro ⟨hl, ha, hP | hQ⟩
    · exact Or.inl ⟨hl, ha, hP⟩
    · exact Or.inr ⟨hl, ha, hQ⟩
  · rintro (⟨hl, ha, hP⟩ | ⟨hl, ha, hQ⟩)
    · exact ⟨hl, ha, Or.inl hP⟩
    · exact ⟨hl, ha, Or.inr hQ⟩

theorem ofAtoms_inf (P Q : Set (BoundedAtom k)) :
    (ofAtoms (P ⊓ Q) : Language src tgt k X X) = (ofAtoms P).comp (ofAtoms Q) := by
  apply ext
  ext ⟨α, l⟩
  change (l = [] ∧ ∃ h : α.length = k, ⟨α, h⟩ ∈ P ∩ Q) ↔
    (α, l) ∈ KAT.fuse (ofAtoms P).strings (ofAtoms Q).strings
  rw [KAT.mem_fuse]
  constructor
  · rintro ⟨rfl, ha, hP, hQ⟩
    exact ⟨[], [], rfl, ⟨rfl, ha, hP⟩, rfl, ha, hQ⟩
  · rintro ⟨l₁, l₂, rfl, ⟨rfl, ha, hP⟩, ⟨rfl, _, hQ⟩⟩
    exact ⟨rfl, ha, hP, hQ⟩

/-- Different sets of atoms give different tests in the language model. -/
theorem ofAtoms_injective :
    Function.Injective (ofAtoms : Set (BoundedAtom k) → Language src tgt k X X) := by
  intro P Q h
  ext α
  have hm := congrArg (fun L : Language src tgt k X X ↦ (α.val, []) ∈ L.strings) h
  simpa only [mem_ofAtoms, true_and, exists_prop_of_true α.property] using (iff_of_eq hm)

end Language

namespace LanguageCat

variable {I : Type u} {src tgt : ℕ → I} {k : ℕ}

/-- Tests at an object are sets of bounded atoms. Naming the object here helps Lean infer
the language category when elaborating the typed test notation. -/
abbrev Tests (_X : LanguageCat src tgt k) := Set (BoundedAtom k)

instance : TypedKAT (LanguageCat src tgt k) (fun _ ↦ Set (BoundedAtom k)) where
  test := Language.ofAtoms
  test_bot := Language.ofAtoms_bot
  test_top := Language.ofAtoms_top
  test_sup := Language.ofAtoms_sup
  test_inf := Language.ofAtoms_inf

/-- The canonical object interpretation. -/
def ofObject (X : I) : LanguageCat src tgt k := ⟨X⟩

/-- The canonical primitive test: look up one coordinate of an atom. Out-of-range test
indices are false, just as in `KAT.Atom.sat`; no bound is needed for semantic agreement. -/
def testVar (i : ℕ) : Set (BoundedAtom k) := {α | α.val.getD i false = true}

/-- A primitive test with its object recorded in the result type, for use with `⌞…⌟`. -/
def testVarAt (X : LanguageCat src tgt k) (i : ℕ) : Tests X := testVar i

theorem mem_eval_test (b : KAT.BTerm) (α : BoundedAtom k) :
    α ∈ b.eval (testVar (k := k)) ↔ α.val.sat b = true := by
  induction b with
  | top => simp [KAT.BTerm.eval, KAT.Atom.sat]
  | bot => simp [KAT.BTerm.eval, KAT.Atom.sat]
  | tvar _ => rfl
  | and b c hb hc => simp [KAT.BTerm.eval, KAT.Atom.sat, hb, hc]
  | or b c hb hc => simp [KAT.BTerm.eval, KAT.Atom.sat, hb, hc]
  | not b hb => simp [KAT.BTerm.eval, KAT.Atom.sat, hb]

/-- The canonical action interpretation has exactly its declared endpoints. -/
def action (a : ℕ) : ofObject (src := src) (tgt := tgt) (k := k) (src a) ⟶
    ofObject (tgt a) := Language.act a

end LanguageCat

namespace Term

variable {I : Type u} {src tgt : ℕ → I} {X Y : I}

/-- Ordinary interpretation in the bundled language model is the existing guarded-string
semantics, including its fixed-bound convention for test variables. -/
theorem eval_languageCat (e : Term src tgt X Y) (k : ℕ) :
    e.eval (T := fun _ : LanguageCat src tgt k ↦ Set (BoundedAtom k))
      (LanguageCat.ofObject (src := src) (tgt := tgt) (k := k))
      (fun _ ↦ LanguageCat.testVar (k := k)) LanguageCat.action = e.lang k := by
  induction e with
  | zero => rfl
  | one => rfl
  | act _ => rfl
  | test b =>
    apply Language.ext
    ext ⟨α, l⟩
    change (l = [] ∧ ∃ h : α.length = k,
      (⟨α, h⟩ : BoundedAtom k) ∈ b.eval LanguageCat.testVar) ↔
      l = [] ∧ α ∈ KAT.allAtoms k ∧ α.sat b = true
    simp only [LanguageCat.mem_eval_test, KAT.mem_allAtoms, exists_prop]
  | add e f he hf => exact congrArg₂ Language.add he hf
  | comp e f he hf => exact congrArg₂ Language.comp he hf
  | star e he => exact congrArg Language.star he

end Term
end TypedKAT
