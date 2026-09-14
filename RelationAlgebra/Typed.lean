import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.Category.RelCat
import Mathlib.Logic.Relation
import RelationAlgebra.Kleene.Basic

/-!
# Typed Kleene algebra: Kleene categories

The single-sorted notion of Kleene algebra (Mathlib's `KleeneAlgebra`) only speaks about
*square* objects: relations on a fixed type, square matrices, ...  Pous' `relation-algebra`
library is instead built on a *typed* (or many-object) presentation, where the operations act
on the hom-sets of a category.  This is the natural setting for heterogeneous relations
`SetRel α β`, rectangular matrices, and for the *rectangular* forms of the star induction
axioms, which are strictly more useful than their square instances (e.g. typed bisimulation
`f ≫ h ≤ h ≫ g → f∗ ≫ h ≤ h ≫ g∗` with `h : X ⟶ Y`).

This file defines `KleeneCategory C` for a category `C` (Mathlib's
`CategoryTheory.Category`): every hom-set `X ⟶ Y` is a join-semilattice with a least element
`⊥`, composition `≫` is bilinear (distributes over `⊔` and annihilates `⊥`), and every
endomorphism `f : X ⟶ X` has a Kleene star `f∗` satisfying Kozen's axioms in the rectangular
form (`str_refl`, `str_cons`, `str_snoc`, `str_ind_l`, `str_ind_r` in Pous' terminology).

## Main declarations

* `KleeneCategory C`: the class.  The hom lattices are instance fields, and `f∗` is available
  for `f : X ⟶ X` through a `KStar (X ⟶ X)` instance (`open scoped Computability`).
* `KleeneCategory.comp_le_comp` and friends: composition is monotone (`gcongr`).
* `KleeneCategory.instKleeneAlgebraEnd`: for every object `X`, the endomorphism monoid
  `CategoryTheory.End X` is a `KleeneAlgebra`, so all of Mathlib's Kleene algebra API and of
  `RelationAlgebra.Kleene.Basic` applies to endomorphisms.  Beware the reversal built into
  `CategoryTheory.End`: `f * g = g ≫ f` (`CategoryTheory.End.mul_def`).
* typed laws that genuinely need rectangular morphisms: the sliding rule
  `KleeneCategory.comp_kstar_eq_kstar_comp : f ≫ (g ≫ f)∗ = (f ≫ g)∗ ≫ f` for
  `f : X ⟶ Y`, `g : Y ⟶ X`, the bisimulation rules
  `KleeneCategory.kstar_comp_le_comp_kstar_of_le`, `KleeneCategory.kstar_comp_eq_comp_kstar_of_eq`,
  and the least-fixpoint characterisations `KleeneCategory.isLeast_kstar_comp`,
  `KleeneCategory.isLeast_comp_kstar`.
* Instances: every Kleene algebra `K` is a one-object Kleene category
  (`CategoryTheory.SingleObj.instKleeneCategory`), and the category `CategoryTheory.RelCat` of
  types and binary relations is a Kleene category with `f∗` the reflexive-transitive closure
  (`CategoryTheory.RelCat.instKleeneCategory`).

## Design notes

Mathlib's `CategoryTheory.End X` is a plain `def`, so instances on `X ⟶ X` are not found for
`End X` and vice-versa; we therefore give `End X` its own (definitionally equal) lattice
instances.  Since `End.mul_def : f * g = g ≫ f`, the *left* Kozen axioms on `End X` correspond
to the *right* typed axioms and conversely; the lemmas `KleeneCategory.End.add_def`,
`KleeneCategory.End.zero_def`, `KleeneCategory.End.kstar_def` (all `rfl`) translate.

For the relational model we use Mathlib's `CategoryTheory.RelCat`, whose morphisms are the
structure `RelCat.Hom X Y` wrapping a `SetRel X Y`; the lattice structure is transported
along `RelCat.Hom.rel` (`RelCat.Hom.le_iff`, `RelCat.Hom.rel_sup`, `RelCat.Hom.rel_bot`).
This keeps the file independent of the scoped single-sorted instances of
`RelationAlgebra.Models.Rel`.

## References

* [D. Pous, *Kleene Algebra with Tests and Coq tools for while programs*]
* The Rocq library `relation-algebra`, file `kleene.v`.
-/

open scoped Computability SetRel
open CategoryTheory

universe u v

/-- A **Kleene category** (typed Kleene algebra): a category whose hom-sets are join-semilattices
with a least element, such that composition is bilinear, together with a Kleene star on
endomorphisms satisfying Kozen's axioms in rectangular form. -/
class KleeneCategory (C : Type u) [Category.{v} C] where
  /-- Every hom-set is a join-semilattice. -/
  [homSemilatticeSup : ∀ X Y : C, SemilatticeSup (X ⟶ Y)]
  /-- Every hom-set has a least element `⊥` (the "zero morphism"). -/
  [homOrderBot : ∀ X Y : C, OrderBot (X ⟶ Y)]
  /-- Composition distributes over joins in its first argument. -/
  sup_comp {X Y Z : C} (f g : X ⟶ Y) (h : Y ⟶ Z) : (f ⊔ g) ≫ h = f ≫ h ⊔ g ≫ h
  /-- Composition distributes over joins in its second argument. -/
  comp_sup {X Y Z : C} (f : X ⟶ Y) (g h : Y ⟶ Z) : f ≫ (g ⊔ h) = f ≫ g ⊔ f ≫ h
  /-- `⊥` is absorbing for composition on the left. -/
  bot_comp {X Y Z : C} (f : Y ⟶ Z) : (⊥ : X ⟶ Y) ≫ f = ⊥
  /-- `⊥` is absorbing for composition on the right. -/
  comp_bot {X Y Z : C} (f : X ⟶ Y) : f ≫ (⊥ : Y ⟶ Z) = ⊥
  /-- The Kleene star of an endomorphism.  Use the notation `f∗` (see
  `KleeneCategory.instKStarHom`). -/
  kstar {X : C} : (X ⟶ X) → (X ⟶ X)
  /-- `𝟙 X ≤ f∗`. -/
  id_le_kstar {X : C} (f : X ⟶ X) : 𝟙 X ≤ kstar f
  /-- `f ≫ f∗ ≤ f∗`. -/
  comp_kstar_le_kstar {X : C} (f : X ⟶ X) : f ≫ kstar f ≤ kstar f
  /-- `f∗ ≫ f ≤ f∗`. -/
  kstar_comp_le_kstar {X : C} (f : X ⟶ X) : kstar f ≫ f ≤ kstar f
  /-- Rectangular right star induction: if `g ≫ f ≤ g` then `g ≫ f∗ ≤ g`. -/
  comp_kstar_le_self {X Y : C} (f : X ⟶ X) (g : Y ⟶ X) : g ≫ f ≤ g → g ≫ kstar f ≤ g
  /-- Rectangular left star induction: if `f ≫ g ≤ g` then `f∗ ≫ g ≤ g`. -/
  kstar_comp_le_self {X Y : C} (f : X ⟶ X) (g : X ⟶ Y) : f ≫ g ≤ g → kstar f ≫ g ≤ g

attribute [instance_reducible, instance] KleeneCategory.homSemilatticeSup
  KleeneCategory.homOrderBot

attribute [simp] KleeneCategory.sup_comp KleeneCategory.comp_sup KleeneCategory.bot_comp
  KleeneCategory.comp_bot

namespace KleeneCategory

variable {C : Type u} [Category.{v} C] [KleeneCategory C] {X Y Z : C}

/-- The Kleene star of an endomorphism, as Mathlib's `f∗` notation. -/
instance instKStarHom {X : C} : KStar (X ⟶ X) := ⟨KleeneCategory.kstar⟩

@[simp] theorem kstar_eq (f : X ⟶ X) : KleeneCategory.kstar f = f∗ := rfl

/-! ### Monotonicity of composition

Following Mathlib's convention for `mul_le_mul_left`/`mul_le_mul_right`, the suffix names the
position of the *varying* morphism. -/

@[gcongr]
theorem comp_le_comp_left {f g : X ⟶ Y} (hfg : f ≤ g) (h : Y ⟶ Z) : f ≫ h ≤ g ≫ h :=
  calc f ≫ h ≤ f ≫ h ⊔ g ≫ h := le_sup_left
    _ = (f ⊔ g) ≫ h := (sup_comp f g h).symm
    _ = g ≫ h := by rw [sup_eq_right.2 hfg]

@[gcongr]
theorem comp_le_comp_right {g h : Y ⟶ Z} (hgh : g ≤ h) (f : X ⟶ Y) : f ≫ g ≤ f ≫ h :=
  calc f ≫ g ≤ f ≫ g ⊔ f ≫ h := le_sup_left
    _ = f ≫ (g ⊔ h) := (comp_sup f g h).symm
    _ = f ≫ h := by rw [sup_eq_right.2 hgh]

@[gcongr]
theorem comp_le_comp {f g : X ⟶ Y} {h k : Y ⟶ Z} (hfg : f ≤ g) (hhk : h ≤ k) :
    f ≫ h ≤ g ≫ k :=
  (comp_le_comp_left hfg h).trans (comp_le_comp_right hhk g)

theorem monotone_comp_left (h : Y ⟶ Z) : Monotone fun f : X ⟶ Y ↦ f ≫ h :=
  fun _ _ hfg ↦ comp_le_comp_left hfg h

theorem monotone_comp_right (f : X ⟶ Y) : Monotone fun g : Y ⟶ Z ↦ f ≫ g :=
  fun _ _ hgh ↦ comp_le_comp_right hgh f

/-! ### Basic facts about the star, in rectangular form -/

theorem le_comp_kstar (f : X ⟶ Y) (g : Y ⟶ Y) : f ≤ f ≫ g∗ :=
  calc f = f ≫ 𝟙 Y := (Category.comp_id f).symm
    _ ≤ f ≫ g∗ := comp_le_comp_right (id_le_kstar g) f

theorem le_kstar_comp (f : X ⟶ X) (g : X ⟶ Y) : g ≤ f∗ ≫ g :=
  calc g = 𝟙 X ≫ g := (Category.id_comp g).symm
    _ ≤ f∗ ≫ g := comp_le_comp_left (id_le_kstar f) g

theorem comp_kstar_le {f : X ⟶ X} {g h : Y ⟶ X} (hgh : g ≤ h) (hh : h ≫ f ≤ h) :
    g ≫ f∗ ≤ h :=
  (comp_le_comp_left hgh _).trans (comp_kstar_le_self f h hh)

theorem kstar_comp_le {f : X ⟶ X} {g h : X ⟶ Y} (hgh : g ≤ h) (hh : f ≫ h ≤ h) :
    f∗ ≫ g ≤ h :=
  (comp_le_comp_right hgh _).trans (kstar_comp_le_self f h hh)

theorem kstar_le_of_comp_le_left {f g : X ⟶ X} (hg : 𝟙 X ≤ g) (h : g ≫ f ≤ g) : f∗ ≤ g :=
  (Category.id_comp _).symm.trans_le (comp_kstar_le hg h)

theorem kstar_le_of_comp_le_right {f g : X ⟶ X} (hg : 𝟙 X ≤ g) (h : f ≫ g ≤ g) : f∗ ≤ g :=
  (Category.comp_id _).symm.trans_le (kstar_comp_le hg h)

theorem comp_kstar_comp_le_kstar_comp (f : X ⟶ X) (g : X ⟶ Y) : f ≫ f∗ ≫ g ≤ f∗ ≫ g := by
  rw [← Category.assoc]
  exact comp_le_comp_left (comp_kstar_le_kstar f) g

theorem comp_kstar_comp_le_comp_kstar (f : X ⟶ X) (g : Y ⟶ X) : (g ≫ f∗) ≫ f ≤ g ≫ f∗ := by
  rw [Category.assoc]
  exact comp_le_comp_right (kstar_comp_le_kstar f) g

/-- `f∗ ≫ g` is the least solution `k` of `f ≫ k ⊔ g ≤ k`. -/
theorem isLeast_kstar_comp (f : X ⟶ X) (g : X ⟶ Y) :
    IsLeast {k | f ≫ k ⊔ g ≤ k} (f∗ ≫ g) :=
  ⟨sup_le (comp_kstar_comp_le_kstar_comp f g) (le_kstar_comp f g),
    fun _ (hk : f ≫ _ ⊔ g ≤ _) ↦ kstar_comp_le (le_sup_right.trans hk) (le_sup_left.trans hk)⟩

/-- `g ≫ f∗` is the least solution `k` of `k ≫ f ⊔ g ≤ k`. -/
theorem isLeast_comp_kstar (f : X ⟶ X) (g : Y ⟶ X) :
    IsLeast {k | k ≫ f ⊔ g ≤ k} (g ≫ f∗) :=
  ⟨sup_le (comp_kstar_comp_le_comp_kstar f g) (le_comp_kstar g f),
    fun _ (hk : _ ≫ f ⊔ g ≤ _) ↦ comp_kstar_le (le_sup_right.trans hk) (le_sup_left.trans hk)⟩

/-! ### Endomorphisms form a Kleene algebra -/

section End

variable (X)

/-- The join-semilattice structure of `End X = (X ⟶ X)`. -/
instance instSemilatticeSupEnd : SemilatticeSup (End X) := homSemilatticeSup X X

/-- The least element of `End X = (X ⟶ X)`. -/
instance instOrderBotEnd : OrderBot (End X) := homOrderBot X X

/-- Addition of endomorphisms is the join. -/
instance instAddEnd : Add (End X) := ⟨(· ⊔ ·)⟩

/-- The zero endomorphism is `⊥`. -/
instance instZeroEnd : Zero (End X) := ⟨⊥⟩

/-- The endomorphisms of an object of a Kleene category form a Kleene algebra, with
`f + g = f ⊔ g`, `0 = ⊥`, `f * g = g ≫ f` (Mathlib's convention for `CategoryTheory.End`) and
`f∗ = KleeneCategory.kstar f`. -/
instance instKleeneAlgebraEnd : KleeneAlgebra (End X) where
  __ := End.monoid
  __ := instSemilatticeSupEnd X
  __ := instOrderBotEnd X
  __ := instAddEnd X
  __ := instZeroEnd X
  add_assoc := sup_assoc
  zero_add := bot_sup_eq
  add_zero := sup_bot_eq
  add_comm := sup_comm
  nsmul := nsmulRec
  left_distrib f g h := sup_comp g h f
  right_distrib f g h := comp_sup h f g
  zero_mul := comp_bot
  mul_zero := bot_comp
  add_eq_sup _ _ := rfl
  kstar := KleeneCategory.kstar
  one_le_kstar := id_le_kstar
  mul_kstar_le_kstar := kstar_comp_le_kstar
  kstar_mul_le_kstar := comp_kstar_le_kstar
  mul_kstar_le_self := kstar_comp_le_self
  kstar_mul_le_self := comp_kstar_le_self

variable {X}

theorem End.add_def (f g : End X) : f + g = f ⊔ g := rfl

theorem End.zero_def : (0 : End X) = ⊥ := rfl

theorem End.kstar_def (f : End X) : f∗ = (End.asHom f)∗ := rfl

theorem End.le_def (f g : End X) : f ≤ g ↔ End.asHom f ≤ End.asHom g := Iff.rfl

end End

/-! ### Laws inherited from the endomorphism Kleene algebras -/

theorem le_kstar (f : X ⟶ X) : f ≤ f∗ := _root_.le_kstar (a := End.of f)

theorem kstar_mono {f g : X ⟶ X} (h : f ≤ g) : f∗ ≤ g∗ := _root_.kstar_mono (α := End X) h

theorem kstar_idem (f : X ⟶ X) : f∗∗ = f∗ := _root_.kstar_idem (End.of f)

theorem kstar_id : (𝟙 X)∗ = 𝟙 X := kstar_one (α := End X)

theorem kstar_comp_kstar (f : X ⟶ X) : f∗ ≫ f∗ = f∗ := kstar_mul_kstar (End.of f)

theorem kstar_comp_comm (f : X ⟶ X) : f∗ ≫ f = f ≫ f∗ :=
  (KleeneAlgebra.kstar_mul_comm (End.of f)).symm

theorem kstar_eq_id_iff {f : X ⟶ X} : f∗ = 𝟙 X ↔ f ≤ 𝟙 X := kstar_eq_one (a := End.of f)

theorem kstar_sup_id (f : X ⟶ X) : (f ⊔ 𝟙 X)∗ = f∗ := KleeneAlgebra.kstar_add_one (End.of f)

theorem kstar_id_sup (f : X ⟶ X) : (𝟙 X ⊔ f)∗ = f∗ := KleeneAlgebra.kstar_one_add (End.of f)

theorem kstar_sup_le (f g : X ⟶ X) : f∗ ⊔ g∗ ≤ (f ⊔ g)∗ :=
  KleeneAlgebra.kstar_add_le (a := End.of f) (b := End.of g)

/-- The **denesting rule**, typed: `(f ⊔ g)∗ = f∗ ≫ (g ≫ f∗)∗`. -/
theorem kstar_sup (f g : X ⟶ X) : (f ⊔ g)∗ = f∗ ≫ (g ≫ f∗)∗ :=
  KleeneAlgebra.kstar_add' (End.of f) (End.of g)

/-- The other **denesting rule**, typed: `(f ⊔ g)∗ = (f∗ ≫ g)∗ ≫ f∗`. -/
theorem kstar_sup' (f g : X ⟶ X) : (f ⊔ g)∗ = (f∗ ≫ g)∗ ≫ f∗ :=
  KleeneAlgebra.kstar_add (End.of f) (End.of g)

theorem kstar_kstar_comp_kstar (f g : X ⟶ X) : (f∗ ≫ g∗)∗ = (f ⊔ g)∗ :=
  (KleeneAlgebra.kstar_kstar_mul_kstar (End.of g) (End.of f)).trans
    (congrArg KStar.kstar (sup_comm (End.of g) (End.of f)))

/-- If `g` "commutes past" `f`, then `(f ⊔ g)∗ = f∗ ≫ g∗`. -/
theorem kstar_sup_of_comp_le_comp {f g : X ⟶ X} (h : g ≫ f ≤ f ≫ g) : (f ⊔ g)∗ = f∗ ≫ g∗ :=
  (congrArg KStar.kstar (sup_comm (End.of f) (End.of g))).trans
    (KleeneAlgebra.kstar_add_of_mul_le_mul (a := End.of g) (b := End.of f) h)

/-- If `f` and `g` commute, then `(f ⊔ g)∗ = f∗ ≫ g∗`. -/
theorem kstar_sup_of_comm {f g : X ⟶ X} (h : f ≫ g = g ≫ f) : (f ⊔ g)∗ = f∗ ≫ g∗ :=
  kstar_sup_of_comp_le_comp h.ge

/-! ### Typed sliding and bisimulation

These are the laws whose natural statements involve *rectangular* morphisms, and hence are not
instances of the single-sorted theory of `End X`. -/

/-- The **sliding rule**, typed: `f ≫ (g ≫ f)∗ = (f ≫ g)∗ ≫ f` for `f : X ⟶ Y`, `g : Y ⟶ X`. -/
theorem comp_kstar_eq_kstar_comp (f : X ⟶ Y) (g : Y ⟶ X) :
    f ≫ (g ≫ f)∗ = (f ≫ g)∗ ≫ f := by
  apply le_antisymm
  · refine comp_kstar_le (le_kstar_comp (f ≫ g) f) ?_
    calc ((f ≫ g)∗ ≫ f) ≫ (g ≫ f) = ((f ≫ g)∗ ≫ (f ≫ g)) ≫ f := by simp only [Category.assoc]
      _ ≤ (f ≫ g)∗ ≫ f := comp_le_comp_left (kstar_comp_le_kstar (f ≫ g)) f
  · refine kstar_comp_le (le_comp_kstar f (g ≫ f)) ?_
    calc (f ≫ g) ≫ (f ≫ (g ≫ f)∗) = f ≫ ((g ≫ f) ≫ (g ≫ f)∗) := by simp only [Category.assoc]
      _ ≤ f ≫ (g ≫ f)∗ := comp_le_comp_right (comp_kstar_le_kstar (g ≫ f)) f

/-- Typed **bisimulation**, one direction: if `h : X ⟶ Y` simulates `f` by `g`, i.e.
`f ≫ h ≤ h ≫ g`, then `f∗ ≫ h ≤ h ≫ g∗`. -/
theorem kstar_comp_le_comp_kstar_of_le {f : X ⟶ X} {g : Y ⟶ Y} {h : X ⟶ Y}
    (hfg : f ≫ h ≤ h ≫ g) : f∗ ≫ h ≤ h ≫ g∗ :=
  kstar_comp_le (le_comp_kstar h g) <|
    calc f ≫ (h ≫ g∗) = (f ≫ h) ≫ g∗ := (Category.assoc _ _ _).symm
      _ ≤ (h ≫ g) ≫ g∗ := comp_le_comp_left hfg _
      _ = h ≫ (g ≫ g∗) := Category.assoc _ _ _
      _ ≤ h ≫ g∗ := comp_le_comp_right (comp_kstar_le_kstar g) h

/-- Typed **bisimulation**, the other direction: if `h ≫ g ≤ f ≫ h` then `h ≫ g∗ ≤ f∗ ≫ h`. -/
theorem comp_kstar_le_kstar_comp_of_le {f : X ⟶ X} {g : Y ⟶ Y} {h : X ⟶ Y}
    (hfg : h ≫ g ≤ f ≫ h) : h ≫ g∗ ≤ f∗ ≫ h :=
  comp_kstar_le (le_kstar_comp f h) <|
    calc (f∗ ≫ h) ≫ g = f∗ ≫ (h ≫ g) := Category.assoc _ _ _
      _ ≤ f∗ ≫ (f ≫ h) := comp_le_comp_right hfg _
      _ = (f∗ ≫ f) ≫ h := (Category.assoc _ _ _).symm
      _ ≤ f∗ ≫ h := comp_le_comp_left (kstar_comp_le_kstar f) h

/-- Typed **bisimulation**: if `h : X ⟶ Y` intertwines `f` and `g`, it intertwines `f∗` and
`g∗`. -/
theorem kstar_comp_eq_comp_kstar_of_eq {f : X ⟶ X} {g : Y ⟶ Y} {h : X ⟶ Y}
    (hfg : f ≫ h = h ≫ g) : f∗ ≫ h = h ≫ g∗ :=
  (kstar_comp_le_comp_kstar_of_le hfg.le).antisymm (comp_kstar_le_kstar_comp_of_le hfg.ge)

end KleeneCategory

/-! ### Every Kleene algebra is a one-object Kleene category -/

namespace CategoryTheory.SingleObj

/-- A Kleene algebra `K` is a Kleene category with a single object.  Recall that in
`SingleObj K` the morphisms are the elements of `K` and `f ≫ g = g * f`
(`CategoryTheory.SingleObj.comp_as_mul`). -/
instance instKleeneCategory (K : Type u) [KleeneAlgebra K] : KleeneCategory (SingleObj K) where
  homSemilatticeSup _ _ := inferInstanceAs (SemilatticeSup K)
  homOrderBot _ _ := inferInstanceAs (OrderBot K)
  sup_comp f g h := by
    change h * (f ⊔ g) = h * f ⊔ h * g
    rw [← add_eq_sup, ← add_eq_sup, mul_add]
  comp_sup f g h := by
    change (g ⊔ h) * f = g * f ⊔ h * f
    rw [← add_eq_sup, ← add_eq_sup, add_mul]
  bot_comp f := by
    change f * ⊥ = ⊥
    rw [bot_eq_zero, mul_zero]
  comp_bot f := by
    change ⊥ * f = ⊥
    rw [bot_eq_zero, zero_mul]
  kstar f := f∗
  id_le_kstar _ := one_le_kstar
  comp_kstar_le_kstar _ := kstar_mul_le_kstar
  kstar_comp_le_kstar _ := mul_kstar_le_kstar
  comp_kstar_le_self _ _ h := kstar_mul_le_self h
  kstar_comp_le_self _ _ h := mul_kstar_le_self h

theorem kstar_as_kstar {K : Type u} [KleeneAlgebra K] {x : SingleObj K} (f : x ⟶ x) :
    f∗ = (f : K)∗ :=
  rfl

end CategoryTheory.SingleObj

/-! ### The category of types and relations is a Kleene category -/

namespace CategoryTheory.RelCat

variable {X Y : RelCat.{u}}

namespace Hom

/-- Morphisms `X ⟶ Y` of `RelCat` are ordered by inclusion of the underlying relations, with
join the union. -/
instance instSemilatticeSup : SemilatticeSup (X ⟶ Y) where
  sup f g := ofRel (f.rel ∪ g.rel)
  le f g := f.rel ⊆ g.rel
  le_refl _ := Set.Subset.rfl
  le_trans _ _ _ := Set.Subset.trans
  le_antisymm f g h h' := Hom.ext f g (Set.Subset.antisymm h h')
  le_sup_left _ _ := Set.subset_union_left
  le_sup_right _ _ := Set.subset_union_right
  sup_le _ _ _ := Set.union_subset

/-- The empty relation is the least morphism `X ⟶ Y` of `RelCat`. -/
instance instOrderBot : OrderBot (X ⟶ Y) where
  bot := ofRel ∅
  bot_le f := Set.empty_subset f.rel

theorem le_iff {f g : X ⟶ Y} : f ≤ g ↔ f.rel ⊆ g.rel := Iff.rfl

@[simp] theorem rel_sup (f g : X ⟶ Y) : (f ⊔ g).rel = f.rel ∪ g.rel := rfl

@[simp] theorem rel_bot : (⊥ : X ⟶ Y).rel = ∅ := rfl

/-- The reflexive-transitive closure of a relation, as an endomorphism of `RelCat`. -/
def kstar (f : X ⟶ X) : X ⟶ X :=
  ofRel {p | Relation.ReflTransGen (· ~[f.rel] ·) p.1 p.2}

theorem rel_kstar (f : X ⟶ X) :
    (kstar f).rel = {p | Relation.ReflTransGen (· ~[f.rel] ·) p.1 p.2} :=
  rfl

@[simp] theorem rel_kstar_apply₂ (f : X ⟶ X) (x y : X) :
    x ~[(kstar f).rel] y ↔ Relation.ReflTransGen (· ~[f.rel] ·) x y :=
  Iff.rfl

end Hom

/-- `RelCat` is a Kleene category: relations are ordered by inclusion, composition is relational
composition, and the star is the reflexive-transitive closure. -/
instance instKleeneCategory : KleeneCategory RelCat.{u} where
  sup_comp f g h := by
    ext ⟨a, c⟩
    simp only [Hom.rel_comp, Hom.rel_sup, SetRel.mem_comp, Set.mem_union, or_and_right,
      exists_or]
  comp_sup f g h := by
    ext ⟨a, c⟩
    simp only [Hom.rel_comp, Hom.rel_sup, SetRel.mem_comp, Set.mem_union, and_or_left,
      exists_or]
  bot_comp f := by
    ext ⟨a, c⟩
    simp only [Hom.rel_comp, Hom.rel_bot, SetRel.empty_comp]
  comp_bot f := by
    ext ⟨a, c⟩
    simp only [Hom.rel_comp, Hom.rel_bot, SetRel.comp_empty]
  kstar := Hom.kstar
  id_le_kstar _ := by
    rintro ⟨a, b⟩ (h : a = b)
    subst h
    exact Relation.ReflTransGen.refl
  comp_kstar_le_kstar _ := by
    rintro ⟨a, c⟩ ⟨b, hab, hbc⟩
    exact Relation.ReflTransGen.head hab hbc
  kstar_comp_le_kstar _ := by
    rintro ⟨a, c⟩ ⟨b, hab, hbc⟩
    exact Relation.ReflTransGen.tail hab hbc
  comp_kstar_le_self f g h := by
    rintro ⟨a, c⟩ ⟨b, hab, hbc⟩
    replace hbc : Relation.ReflTransGen (· ~[f.rel] ·) b c := hbc
    induction hbc with
    | refl => exact hab
    | tail _ hcd ih => exact h ⟨_, ih, hcd⟩
  kstar_comp_le_self f g h := by
    rintro ⟨a, c⟩ ⟨b, hab, hbc⟩
    replace hab : Relation.ReflTransGen (· ~[f.rel] ·) a b := hab
    induction hab using Relation.ReflTransGen.head_induction_on with
    | refl => exact hbc
    | head hab' _ ih => exact h ⟨_, hab', ih⟩

theorem kstar_def (f : X ⟶ X) : f∗ = Hom.kstar f := rfl

@[simp] theorem rel_kstar_apply₂ (f : X ⟶ X) (x y : X) :
    x ~[(f∗).rel] y ↔ Relation.ReflTransGen (· ~[f.rel] ·) x y :=
  Iff.rfl

end CategoryTheory.RelCat
