import RelationAlgebra.KAT.FreeTest
import RelationAlgebra.TypedKAT.Semantics
import RelationAlgebra.TypedKAT.Hom

/-!
# The free typed Kleene algebra with tests

`FreeCat src tgt` has the given objects and typed expressions modulo semantic equality as
morphisms. Its tests at each object form `KAT.FreeTest`, the free Boolean algebra on `ℕ`.
The same variable number at different objects denotes independent generators.

`FreeCat.lift` extends any object map and valuations of actions and tests to a typed KAT
homomorphism. `FreeCat.lift_unique` and `FreeCat.existsUnique_lift` give the universal
property. Targets may have arbitrary object, morphism, and test universes; they need only
the ordinary typed KAT axioms, with no finiteness or continuity assumptions.

This packages the free-model construction of Damien Pous's `relation-algebra/gregex.v`
using semantic equality at all atom bounds and the existing typed completeness theorem.
-/

open CategoryTheory
open scoped Computability

universe u v w z

namespace TypedKAT

/-- The hom-set of typed expressions modulo semantic equality. -/
def FreeHom {I : Type u} (src tgt : ℕ → I) (X Y : I) :=
  Quotient (Term.semanticSetoid (src := src) (tgt := tgt) (X := X) (Y := Y))

namespace FreeHom

variable {I : Type u} {src tgt : ℕ → I} {W X Y Z : I}

/-- The class of a typed expression. -/
def ofTerm (e : Term src tgt X Y) : FreeHom src tgt X Y := Quotient.mk _ e

@[simp] theorem ofTerm_eq_iff {e f : Term src tgt X Y} :
    ofTerm e = ofTerm f ↔ e.SemEq f := Quotient.eq

/-- Every morphism of the free model is represented by a finite typed expression. -/
theorem ofTerm_surjective :
    Function.Surjective (ofTerm (src := src) (tgt := tgt) (X := X) (Y := Y)) :=
  fun p ↦ Quotient.inductionOn p fun e ↦ ⟨e, rfl⟩

/-- Prove a property of expression classes by choosing an arbitrary representative. -/
@[elab_as_elim] theorem inductionOn {P : FreeHom src tgt X Y → Prop}
    (p : FreeHom src tgt X Y) (h : ∀ e, P (ofTerm e)) : P p := Quotient.inductionOn p h

/-- Interpret a class at any finite atom bound. -/
def lang (k : ℕ) : FreeHom src tgt X Y → Language src tgt k X Y :=
  Quotient.lift (Term.lang k) (fun _ _ h ↦ h k)

@[simp] theorem lang_ofTerm (e : Term src tgt X Y) (k : ℕ) :
    lang k (ofTerm e) = e.lang k := rfl

/-- All finite-bound languages together separate expression classes. -/
@[ext] theorem ext {p q : FreeHom src tgt X Y} (h : ∀ k, lang k p = lang k q) : p = q := by
  refine Quotient.inductionOn₂ p q (fun _ _ h ↦ Quotient.sound h) h

private theorem languages_injective :
    Function.Injective (fun p : FreeHom src tgt X Y ↦ fun k ↦ lang k p) :=
  fun _ _ h ↦ ext (congrFun h)

instance : PartialOrder (FreeHom src tgt X Y) :=
  PartialOrder.lift (fun p k ↦ lang k p) languages_injective

/-- Zero as an expression class. -/
def zero : FreeHom src tgt X Y := ofTerm .zero

/-- Identity as an expression class. -/
def one : FreeHom src tgt X X := ofTerm .one

/-- Choice of expression classes. -/
def add : FreeHom src tgt X Y → FreeHom src tgt X Y → FreeHom src tgt X Y :=
  Quotient.map₂ Term.add (fun {_ _} he {_ _} hf ↦ he.add hf)

/-- Composition of expression classes with matching endpoints. -/
def comp : FreeHom src tgt X Y → FreeHom src tgt Y Z → FreeHom src tgt X Z :=
  Quotient.map₂ Term.comp (fun {_ _} he {_ _} hf ↦ he.comp hf)

/-- Iteration of an endomorphism class. -/
def star : FreeHom src tgt X X → FreeHom src tgt X X :=
  Quotient.map Term.star (fun _ _ h ↦ h.star)

/-- Embed a Boolean expression class at an object. -/
def test : KAT.FreeTest → FreeHom src tgt X X := Quotient.map Term.test (by
  intro b c h k
  apply Language.ext
  ext ⟨α, l⟩
  change (l = [] ∧ α ∈ KAT.allAtoms k ∧ α.sat b = true) ↔
    (l = [] ∧ α ∈ KAT.allAtoms k ∧ α.sat c = true)
  rw [h α])

@[simp] theorem lang_zero (k : ℕ) : lang k (zero : FreeHom src tgt X Y) = ⊥ := rfl
@[simp] theorem lang_one (k : ℕ) : lang k (one : FreeHom src tgt X X) = Language.one := rfl
@[simp] theorem lang_add (k : ℕ) (p q : FreeHom src tgt X Y) :
    lang k (add p q) = lang k p ⊔ lang k q :=
  Quotient.inductionOn₂ p q fun _ _ ↦ rfl
@[simp] theorem lang_comp (k : ℕ) (p : FreeHom src tgt X Y) (q : FreeHom src tgt Y Z) :
    lang k (comp p q) = (lang k p).comp (lang k q) :=
  Quotient.inductionOn₂ p q fun _ _ ↦ rfl
@[simp] theorem lang_star (k : ℕ) (p : FreeHom src tgt X X) :
    lang k (star p) = (lang k p).star := Quotient.inductionOn p fun _ ↦ rfl

@[simp] theorem lang_test (k : ℕ) (b : KAT.FreeTest) :
    lang k (test b : FreeHom src tgt X X) =
      Language.ofAtoms {α : BoundedAtom k | α.val ∈ b.atoms} := by
  refine Quotient.inductionOn b fun b ↦ ?_
  apply Language.ext
  ext ⟨α, l⟩
  change (l = [] ∧ α ∈ KAT.allAtoms k ∧ α.sat b = true) ↔ _
  simp only [Language.mem_ofAtoms, Set.mem_setOf_eq, KAT.FreeTest.atoms,
    KAT.mem_allAtoms, exists_prop]
  rfl

instance : SemilatticeSup (FreeHom src tgt X Y) where
  sup := add
  le_sup_left p q k := by
    change lang k p ≤ lang k (add p q)
    rw [lang_add]; exact le_sup_left
  le_sup_right p q k := by
    change lang k q ≤ lang k (add p q)
    rw [lang_add]; exact le_sup_right
  sup_le p q r hp hq k := by
    change lang k (add p q) ≤ lang k r
    rw [lang_add]; exact sup_le (hp k) (hq k)

instance : OrderBot (FreeHom src tgt X Y) where
  bot := zero
  bot_le _ _ := bot_le

@[simp] theorem one_comp (p : FreeHom src tgt X Y) : comp one p = p :=
  ext fun k ↦ by simp

@[simp] theorem comp_one (p : FreeHom src tgt X Y) : comp p one = p :=
  ext fun k ↦ by simp

instance : KStar (FreeHom src tgt X X) := ⟨star⟩

@[simp] theorem ofTerm_le_iff {e f : Term src tgt X Y} :
    ofTerm e ≤ ofTerm f ↔ e.SemLE f := Iff.rfl

@[simp] theorem ofTerm_zero : ofTerm (.zero : Term src tgt X Y) = zero := rfl
@[simp] theorem ofTerm_one : ofTerm (.one : Term src tgt X X) = one := rfl
@[simp] theorem ofTerm_add (e f : Term src tgt X Y) :
    ofTerm (e.add f) = add (ofTerm e) (ofTerm f) := rfl
@[simp] theorem ofTerm_comp (e : Term src tgt X Y) (f : Term src tgt Y Z) :
    ofTerm (e.comp f) = comp (ofTerm e) (ofTerm f) := rfl
@[simp] theorem ofTerm_star (e : Term src tgt X X) : ofTerm e.star = star (ofTerm e) := rfl
@[simp] theorem ofTerm_test (b : KAT.BTerm) :
    ofTerm (.test b : Term src tgt X X) = test (KAT.FreeTest.ofTerm b) := rfl

@[simp] theorem add_self (p : FreeHom src tgt X Y) : add p p = p := sup_idem p

/-- Test embedding in the free model is injective. -/
theorem test_injective : Function.Injective (test (src := src) (tgt := tgt) (X := X)) := by
  intro b c h
  apply KAT.FreeTest.atoms_injective
  ext α
  have hh := congrArg (fun p : FreeHom src tgt X X ↦ lang α.length p) h
  dsimp only at hh
  rw [lang_test, lang_test] at hh
  have hs := Language.ofAtoms_injective hh
  exact Set.ext_iff.mp hs ⟨α, rfl⟩

section Evaluation

variable {C : Type v} [Category.{w} C] [KleeneCategory C]
  {T : C → Type z} [∀ A, BooleanAlgebra (T A)] [TypedKAT C T]
  (o : I → C) (τ : ∀ A, ℕ → T (o A)) (ρ : ∀ a, o (src a) ⟶ o (tgt a))

/-- Interpretation descends to expression classes by typed completeness. -/
def eval : FreeHom src tgt X Y → (o X ⟶ o Y) :=
  Quotient.lift (Term.eval o τ ρ) (fun _ _ h ↦ h.eval_eq o τ ρ)

@[simp] theorem eval_ofTerm (e : Term src tgt X Y) :
    eval o τ ρ (ofTerm e) = e.eval o τ ρ := rfl
@[simp] theorem eval_zero : eval o τ ρ (zero : FreeHom src tgt X Y) = ⊥ := rfl
@[simp] theorem eval_one : eval o τ ρ (one : FreeHom src tgt X X) = 𝟙 (o X) := rfl
@[simp] theorem eval_add (p q : FreeHom src tgt X Y) :
    eval o τ ρ (add p q) = eval o τ ρ p ⊔ eval o τ ρ q :=
  Quotient.inductionOn₂ p q fun _ _ ↦ rfl
@[simp] theorem eval_comp (p : FreeHom src tgt X Y) (q : FreeHom src tgt Y Z) :
    eval o τ ρ (comp p q) = eval o τ ρ p ≫ eval o τ ρ q :=
  Quotient.inductionOn₂ p q fun _ _ ↦ rfl
@[simp] theorem eval_star (p : FreeHom src tgt X X) :
    eval o τ ρ (star p) = (eval o τ ρ p)∗ := Quotient.inductionOn p fun _ ↦ rfl
@[simp] theorem eval_test (b : KAT.FreeTest) :
    eval o τ ρ (test b : FreeHom src tgt X X) = TypedKAT.test (KAT.FreeTest.lift (τ X) b) :=
  Quotient.inductionOn b fun _ ↦ rfl

end Evaluation
end FreeHom

/-- Objects of the free typed KAT on the given action signature. -/
structure FreeCat {I : Type u} (src tgt : ℕ → I) where
  /-- The underlying object of the signature. -/
  object : I

namespace FreeCat

variable {I : Type u} {src tgt : ℕ → I}

instance : Category (FreeCat src tgt) where
  Hom X Y := FreeHom src tgt X.object Y.object
  id _ := FreeHom.one
  comp := FreeHom.comp
  id_comp p := FreeHom.ext fun k ↦ by simp
  comp_id p := FreeHom.ext fun k ↦ by simp
  assoc p q r := FreeHom.ext fun k ↦ by simp [Language.comp_assoc]

instance : KleeneCategory (FreeCat src tgt) where
  homSemilatticeSup X Y := inferInstanceAs (SemilatticeSup (FreeHom src tgt X.object Y.object))
  homOrderBot X Y := inferInstanceAs (OrderBot (FreeHom src tgt X.object Y.object))
  sup_comp p q r := FreeHom.ext fun k ↦ by
    change FreeHom.lang k (FreeHom.comp (FreeHom.add p q) r) =
      FreeHom.lang k (FreeHom.add (FreeHom.comp p r) (FreeHom.comp q r))
    simp only [FreeHom.lang_comp, FreeHom.lang_add, Language.sup_comp]
  comp_sup p q r := FreeHom.ext fun k ↦ by
    change FreeHom.lang k (FreeHom.comp p (FreeHom.add q r)) =
      FreeHom.lang k (FreeHom.add (FreeHom.comp p q) (FreeHom.comp p r))
    simp only [FreeHom.lang_comp, FreeHom.lang_add, Language.comp_sup]
  bot_comp p := FreeHom.ext fun k ↦ by
    change FreeHom.lang k (FreeHom.comp FreeHom.zero p) = FreeHom.lang k FreeHom.zero
    simp
  comp_bot p := FreeHom.ext fun k ↦ by
    change FreeHom.lang k (FreeHom.comp p FreeHom.zero) = FreeHom.lang k FreeHom.zero
    simp
  kstar := FreeHom.star
  id_le_kstar p k := by
    change Language.one ≤ FreeHom.lang k (FreeHom.star p)
    rw [FreeHom.lang_star]; exact Language.one_le_star _
  comp_kstar_le_kstar p k := by
    change FreeHom.lang k (FreeHom.comp p (FreeHom.star p)) ≤ FreeHom.lang k (FreeHom.star p)
    rw [FreeHom.lang_comp, FreeHom.lang_star]; exact Language.comp_star_le_star _
  kstar_comp_le_kstar p k := by
    change FreeHom.lang k (FreeHom.comp (FreeHom.star p) p) ≤ FreeHom.lang k (FreeHom.star p)
    rw [FreeHom.lang_comp, FreeHom.lang_star]; exact Language.star_comp_le_star _
  comp_kstar_le_self p q h k := by
    change FreeHom.lang k (FreeHom.comp q (FreeHom.star p)) ≤ FreeHom.lang k q
    rw [FreeHom.lang_comp, FreeHom.lang_star]
    exact Language.comp_star_le_self _ _ (by
      have hh : FreeHom.lang k (FreeHom.comp q p) ≤ FreeHom.lang k q := h k
      simpa only [FreeHom.lang_comp] using hh)
  kstar_comp_le_self p q h k := by
    change FreeHom.lang k (FreeHom.comp (FreeHom.star p) q) ≤ FreeHom.lang k q
    rw [FreeHom.lang_comp, FreeHom.lang_star]
    exact Language.star_comp_le_self _ _ (by
      have hh : FreeHom.lang k (FreeHom.comp p q) ≤ FreeHom.lang k q := h k
      simpa only [FreeHom.lang_comp] using hh)

/-- The tests at each object form an independent copy of the free Boolean algebra. -/
abbrev Tests (_X : FreeCat src tgt) := KAT.FreeTest

instance : TypedKAT (FreeCat src tgt) Tests where
  test := FreeHom.test
  test_bot := by
    intro X
    apply FreeHom.ext
    intro k
    rw [FreeHom.lang_test]
    simpa only [KAT.FreeTest.atoms_bot, Set.mem_empty_iff_false, Set.setOf_false] using
      Language.ofAtoms_bot
  test_top := by
    intro X
    apply FreeHom.ext
    intro k
    rw [FreeHom.lang_test]
    simpa only [KAT.FreeTest.atoms_top, Set.mem_univ, Set.setOf_true] using Language.ofAtoms_top
  test_sup := by
    intro X b c
    apply FreeHom.ext
    intro k
    change FreeHom.lang k (FreeHom.test (b ⊔ c)) =
      FreeHom.lang k (FreeHom.add (FreeHom.test b) (FreeHom.test c))
    simp only [FreeHom.lang_test, FreeHom.lang_add, KAT.FreeTest.atoms_sup]
    exact Language.ofAtoms_sup _ _
  test_inf := by
    intro X b c
    apply FreeHom.ext
    intro k
    change FreeHom.lang k (FreeHom.test (b ⊓ c)) =
      FreeHom.lang k (FreeHom.comp (FreeHom.test b) (FreeHom.test c))
    simp only [FreeHom.lang_test, FreeHom.lang_comp, KAT.FreeTest.atoms_inf]
    exact Language.ofAtoms_inf _ _

/-- The canonical object map into the free model. -/
def ofObject (X : I) : FreeCat src tgt := ⟨X⟩

/-- An action generator with its declared endpoints. -/
def action (a : ℕ) : ofObject (src := src) (tgt := tgt) (src a) ⟶ ofObject (tgt a) :=
  FreeHom.ofTerm (.act a)

/-- A test generator, with its object recorded for inference. -/
def testVar (X : FreeCat src tgt) (i : ℕ) : Tests X := KAT.FreeTest.var i

/-- Canonical interpretation sends each expression to its own quotient class. -/
@[simp] theorem eval_generators {X Y : I} (e : Term src tgt X Y) :
    e.eval (T := Tests) ofObject (fun X ↦ testVar (ofObject X)) action = FreeHom.ofTerm e := by
  induction e with
  | zero => rfl
  | one => rfl
  | act _ => rfl
  | test b =>
    change FreeHom.test (b.eval KAT.FreeTest.var) = _
    rw [KAT.FreeTest.eval_var]
    rfl
  | add e f he hf => simp only [Term.eval_add, he, hf]; rfl
  | comp e f he hf => simp only [Term.eval_comp, he, hf]; rfl
  | star e he => simp only [Term.eval_star, he]; rfl

section UniversalProperty

variable {C : Type v} [Category.{w} C] [KleeneCategory C]
  {T : C → Type z} [∀ A, BooleanAlgebra (T A)] [TypedKAT C T]
  (o : I → C) (τ : ∀ A, ℕ → T (o A)) (ρ : ∀ a, o (src a) ⟶ o (tgt a))

/-- The homomorphism extending the given object, test, and action interpretations. -/
def lift : Hom (Tests (src := src) (tgt := tgt)) T (fun X ↦ o X.object) where
  map := FreeHom.eval o τ ρ
  testMap X := KAT.FreeTest.lift (τ X.object)
  map_id _ := rfl
  map_comp := FreeHom.eval_comp o τ ρ
  map_bot := rfl
  map_sup := FreeHom.eval_add o τ ρ
  map_star := FreeHom.eval_star o τ ρ
  map_test := FreeHom.eval_test o τ ρ

@[simp] theorem lift_ofTerm {X Y : I} (e : Term src tgt X Y) :
    (lift o τ ρ).map (X := ofObject X) (Y := ofObject Y) (FreeHom.ofTerm e) = e.eval o τ ρ := rfl

@[simp] theorem lift_action (a : ℕ) : (lift o τ ρ).map (action a) = ρ a := rfl

@[simp] theorem lift_testVar (X : I) (i : ℕ) :
    (lift o τ ρ).testMap (ofObject X) (testVar (ofObject X) i) = τ X i := rfl

/-- Every homomorphism with these generator values computes the interpretation of a term. -/
theorem map_ofTerm (F : Hom (Tests (src := src) (tgt := tgt)) T (fun X ↦ o X.object))
    (ht : ∀ X i, F.testMap (ofObject X) (testVar (ofObject X) i) = τ X i)
    (ha : ∀ a, F.map (action a) = ρ a) {X Y : I} (e : Term src tgt X Y) :
    F.map (X := ofObject X) (Y := ofObject Y) (FreeHom.ofTerm e) = e.eval o τ ρ := by
  have ht' (X : I) : F.testMap (ofObject X) = KAT.FreeTest.lift (τ X) :=
    KAT.FreeTest.lift_unique (τ X) _ (ht X)
  induction e with
  | zero => exact F.map_bot
  | one => exact F.map_id _
  | act a => exact ha a
  | @test X b =>
    change F.map (TypedKAT.test (T := Tests (src := src) (tgt := tgt)) (KAT.FreeTest.ofTerm b) :
      ofObject X ⟶ ofObject X) = _
    rw [F.map_test, ht']
    rfl
  | @add X Y e f he hf =>
    exact (F.map_sup (X := ofObject X) (Y := ofObject Y) _ _).trans
      (congrArg₂ (· ⊔ ·) he hf)
  | @comp X Y Z e f he hf =>
    exact (F.map_comp (X := ofObject X) (Y := ofObject Y) (Z := ofObject Z) _ _).trans
      (congrArg₂ (fun p q ↦ p ≫ q) he hf)
  | @star X e he =>
    exact (F.map_star (X := ofObject X) _).trans (congrArg KStar.kstar he)

/-- The extension is unique among typed KAT homomorphisms over the specified object map. -/
theorem lift_unique (F : Hom (Tests (src := src) (tgt := tgt)) T (fun X ↦ o X.object))
    (ht : ∀ X i, F.testMap (ofObject X) (testVar (ofObject X) i) = τ X i)
    (ha : ∀ a, F.map (action a) = ρ a) : F = lift o τ ρ := by
  apply Hom.ext
  · intro X Y p
    exact Quotient.inductionOn p fun e ↦ map_ofTerm o τ ρ F ht ha e
  · intro X b
    exact congrArg (fun f : BoundedLatticeHom KAT.FreeTest (T (o X.object)) ↦ f b)
      (KAT.FreeTest.lift_unique (τ X.object) _ (ht X.object))

/-- **Universal property of the free typed KAT.** Every assignment of objects, independent
object-local tests, and well-typed actions has exactly one homomorphic extension. -/
theorem existsUnique_lift :
    ∃! F : Hom (Tests (src := src) (tgt := tgt)) T (fun X ↦ o X.object),
      (∀ X i, F.testMap (ofObject X) (testVar (ofObject X) i) = τ X i) ∧
      (∀ a, F.map (action a) = ρ a) :=
  ⟨lift o τ ρ, ⟨lift_testVar o τ ρ, lift_action o τ ρ⟩,
    fun F h ↦ lift_unique o τ ρ F h.1 h.2⟩

end UniversalProperty

/-- Interpreting the free model in its own generators fixes every expression class. -/
@[simp] theorem lift_generators_map {X Y : FreeCat src tgt} (p : X ⟶ Y) :
    (lift (T := Tests) ofObject (fun X ↦ testVar (ofObject X)) action).map
      (X := X) (Y := Y) p = p := by
  refine FreeHom.inductionOn p fun e ↦ ?_
  exact eval_generators e

end FreeCat
end TypedKAT
