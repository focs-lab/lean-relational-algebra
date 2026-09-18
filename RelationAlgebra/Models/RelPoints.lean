/- SPDX-License-Identifier: LGPL-3.0-or-later
Lean translation and extensions, 2026-09-18. See LICENSE and NOTICE.md. -/
import RelationAlgebra.TypedPoints
import Mathlib.Order.Atoms

/-!
# Points and atoms of heterogeneous relations

Upstream's algebraic points are singleton rows with a nonempty target; its atoms
are singleton pairs. Here, unlike in an arbitrary allegory, algebraic atoms agree
with lattice atoms. Empty carriers are allowed throughout.
-/

open CategoryTheory AllegoryCategory
universe u

namespace CategoryTheory.RelCat

variable {X Y : RelCat.{u}} {f : X ⟶ Y}

theorem isNonempty_iff : IsNonempty f ↔ ∃ x y, (x, y) ∈ f.rel := by
  constructor
  · intro h
    let U : RelCat.{u} := ULift.{u} Unit
    obtain ⟨x, _, y, hxy, _⟩ := h U U (a := (⟨()⟩, ⟨()⟩)) trivial
    exact ⟨x, y, hxy⟩
  · rintro ⟨x, y, hxy⟩ P Q ⟨p, q⟩ _
    exact ⟨x, trivial, y, hxy, trivial⟩

theorem isNonempty_iff_ne_bot : IsNonempty f ↔ f ≠ ⊥ := by
  rw [isNonempty_iff]
  constructor
  · rintro ⟨x, y, h⟩ he
    simp [he] at h
  · intro h
    by_contra! hn
    apply h
    ext ⟨x, y⟩
    exact iff_false_intro (hn x y)

theorem isNonemptyObject_iff (X : RelCat.{u}) : IsNonemptyObject X ↔ Nonempty X := by
  rw [IsNonemptyObject, isNonempty_iff]
  exact ⟨fun ⟨x, _, _⟩ ↦ ⟨x⟩, fun ⟨x⟩ ↦ ⟨x, x, rfl⟩⟩

theorem isVector_iff : IsVector f ↔ ∀ x y z, (x, y) ∈ f.rel → (x, z) ∈ f.rel := by
  constructor
  · intro h x y z hxy
    exact (show f ≫ (⊤ : Y ⟶ Y) ≤ f from h.le) (a := (x, z)) ⟨y, hxy, trivial⟩
  · intro h
    apply le_antisymm _ (le_comp_top f)
    rintro ⟨x, z⟩ ⟨y, hxy, _⟩
    exact h x y z hxy

/-- The row selecting exactly one source, with every possible target. -/
def row (x : X) : X ⟶ Y := .ofRel {xy | xy.1 = x}

@[simp] theorem row_mem (x x' : X) (y : Y) : (x', y) ∈ (row x).rel ↔ x' = x := Iff.rfl

theorem row_isPoint (x : X) [Nonempty Y] : IsPoint (row x : X ⟶ Y) := by
  refine ⟨isVector_iff.mpr (fun _ _ _ h ↦ h), injective_iff.mpr ?_, ?_⟩
  · intro x' x'' _ h' h''
    exact h'.trans h''.symm
  · obtain ⟨y⟩ := ‹Nonempty Y›
    exact isNonempty_iff.mpr ⟨x, y, rfl⟩

theorem isPoint_iff_exists_row : IsPoint f ↔ Nonempty Y ∧ ∃ x : X, f = row x := by
  constructor
  · intro h
    obtain ⟨x, y, hxy⟩ := isNonempty_iff.mp h.nonempty
    refine ⟨⟨y⟩, x, ?_⟩
    ext ⟨x', y'⟩
    change (x', y') ∈ f.rel ↔ x' = x
    constructor
    · intro hx'y'
      exact injective_iff.mp h.injective x' x y' hx'y'
        (isVector_iff.mp h.vector x y y' hxy)
    · intro he
      subst x'
      exact isVector_iff.mp h.vector x y y' hxy
  · rintro ⟨hn, x, rfl⟩
    letI := hn
    exact row_isPoint x

/-- The relation consisting of a single pair. -/
def singleton (x : X) (y : Y) : X ⟶ Y := .ofRel {(x, y)}

@[simp] theorem singleton_mem (x x' : X) (y y' : Y) :
    (x', y') ∈ (singleton x y).rel ↔ x' = x ∧ y' = y := by
  simp [singleton, Prod.mk.injEq]

theorem singleton_isAtom (x : X) (y : Y) : AllegoryCategory.IsAtom (singleton x y) := by
  refine ⟨?_, ?_, isNonempty_iff.mpr ⟨x, y, by simp⟩⟩
  · rintro ⟨x', x''⟩ ⟨y', h', y'', _, h''⟩
    exact ((singleton_mem ..).mp h').1.trans ((singleton_mem ..).mp h'').1.symm
  · rintro ⟨y', y''⟩ ⟨x', h', x'', _, h''⟩
    exact ((singleton_mem ..).mp h').2.trans ((singleton_mem ..).mp h'').2.symm

theorem isAtom_iff_exists_singleton :
    AllegoryCategory.IsAtom f ↔ ∃ (x : X) (y : Y), f = singleton x y := by
  constructor
  · intro h
    obtain ⟨x, y, hxy⟩ := isNonempty_iff.mp h.nonempty
    refine ⟨x, y, ?_⟩
    ext ⟨x', y'⟩
    change (x', y') ∈ f.rel ↔ (x', y') ∈ (singleton x y).rel
    rw [singleton_mem]
    constructor
    · intro hx'y'
      have hr := h.row
      have hc := h.column
      exact ⟨hr (a := (x', x)) ⟨y', hx'y', y, trivial, hxy⟩,
        hc (a := (y', y)) ⟨x', hx'y', x, trivial, hxy⟩⟩
    · rintro ⟨rfl, rfl⟩
      exact hxy
  · rintro ⟨x, y, rfl⟩
    exact singleton_isAtom x y

/-- The algebraic and lattice predicates agree for heterogeneous relations. -/
theorem isAtom_iff_lattice_isAtom : AllegoryCategory.IsAtom f ↔ _root_.IsAtom f := by
  rw [isAtom_iff_exists_singleton]
  constructor
  · rintro ⟨x, y, rfl⟩
    refine ⟨?_, ?_⟩
    · exact isNonempty_iff_ne_bot.mp (singleton_isAtom x y).nonempty
    · intro g hg
      by_contra hne
      exact hg.ne ((singleton_isAtom x y).eq_of_nonempty_le
        (isNonempty_iff_ne_bot.mpr hne) hg.le)
  · intro h
    obtain ⟨x, y, hxy⟩ := isNonempty_iff.mp (isNonempty_iff_ne_bot.mpr h.1)
    have hs : singleton x y ≤ f := by
      intro ⟨x', y'⟩ hm
      obtain ⟨rfl, rfl⟩ := (singleton_mem ..).mp hm
      exact hxy
    refine ⟨x, y, ?_⟩
    by_contra he
    have hb := h.2 _ (lt_of_le_of_ne hs (Ne.symm he))
    exact isNonempty_iff_ne_bot.mp (singleton_isAtom x y).nonempty hb

end CategoryTheory.RelCat
