import RelationAlgebra.Models.SetoidRel
import RelationAlgebra.TypedIteration
import RelationAlgebra.TypedResiduated
import RelationAlgebra.TypedKAT.Hom

/-!
# Heterogeneous relations between setoids

`HSetoidRel α β` consists of relations invariant under the two setoid equivalences.
`SetoidRelCat` bundles these into a typed KAT and relation category. Identity is setoid
 equivalence, and tests are subsets of the quotient. `toRelCat` interprets a morphism as
 a relation between quotient types, with an order isomorphism on each hom-set.

This is the heterogeneous construction of Damien Pous' `theories/srel.v` in
[relation-algebra](https://github.com/damien-pous/relation-algebra). The original
single-carrier `SetoidRel` interface is retained and connected by `squareOrderIso`.
-/

open CategoryTheory
open scoped Computability SetRel KleeneCategoryWithConverse ResiduatedKleeneCategory

universe u

/-- A heterogeneous relation invariant under both setoid equivalences. -/
structure HSetoidRel (α β : Type*) [Setoid α] [Setoid β] where
  /-- The underlying binary relation. -/
  rel : α → β → Prop
  /-- Invariance under the setoid equivalence. -/
  respects : ∀ {a a' : α} {b b' : β}, a ≈ a' → b ≈ b' → rel a b → rel a' b'

namespace HSetoidRel

variable {α β : Type*} [Setoid α] [Setoid β] {R S : HSetoidRel α β} {a : α} {b : β}

@[ext]
theorem ext (h : ∀ a b, R.rel a b ↔ S.rel a b) : R = S := by
  have hrel : R.rel = S.rel := funext fun a ↦ funext fun b ↦ propext (h a b)
  cases R
  cases S
  subst hrel
  rfl

/-! ### The complete Boolean algebra structure

Invariant relations are closed under all the Boolean and infinitary operations, so they form a
complete sublattice of `SetRel α β`. -/

/-- Invariant relations on a setoid form a complete lattice, with the pointwise order. -/
instance instCompleteLattice : CompleteLattice (HSetoidRel α β) where
  le R S := ∀ a b, R.rel a b → S.rel a b
  le_refl _ _ _ h := h
  le_trans _ _ _ hRS hST a b h := hST a b (hRS a b h)
  le_antisymm _ _ hRS hSR := ext fun a b ↦ ⟨hRS a b, hSR a b⟩
  sup R S := ⟨fun a b ↦ R.rel a b ∨ S.rel a b,
    fun h₁ h₂ h ↦ h.imp (R.respects h₁ h₂) (S.respects h₁ h₂)⟩
  le_sup_left _ _ _ _ h := Or.inl h
  le_sup_right _ _ _ _ h := Or.inr h
  sup_le _ _ _ hRT hST a b h := h.elim (hRT a b) (hST a b)
  inf R S := ⟨fun a b ↦ R.rel a b ∧ S.rel a b,
    fun h₁ h₂ h ↦ ⟨R.respects h₁ h₂ h.1, S.respects h₁ h₂ h.2⟩⟩
  inf_le_left _ _ _ _ h := h.1
  inf_le_right _ _ _ _ h := h.2
  le_inf _ _ _ hRS hRT a b h := ⟨hRS a b h, hRT a b h⟩
  sSup 𝒮 := ⟨fun a b ↦ ∃ R ∈ 𝒮, R.rel a b,
    fun h₁ h₂ h ↦ h.imp fun R hR ↦ ⟨hR.1, R.respects h₁ h₂ hR.2⟩⟩
  isLUB_sSup _ := ⟨fun R hR a b h ↦ ⟨R, hR, h⟩,
    fun _ hR a b h ↦ hR h.choose_spec.1 a b h.choose_spec.2⟩
  sInf 𝒮 := ⟨fun a b ↦ ∀ R ∈ 𝒮, R.rel a b,
    fun h₁ h₂ h R hR ↦ R.respects h₁ h₂ (h R hR)⟩
  isGLB_sInf _ := ⟨fun R hR a b h ↦ h R hR, fun _ hR a b h R hR' ↦ hR hR' a b h⟩
  top := ⟨fun _ _ ↦ True, fun _ _ _ ↦ trivial⟩
  bot := ⟨fun _ _ ↦ False, fun _ _ h ↦ h⟩
  le_top _ _ _ _ := trivial
  bot_le _ _ _ h := h.elim

theorem le_def : R ≤ S ↔ ∀ a b, R.rel a b → S.rel a b := Iff.rfl

@[simp] theorem rel_sup : (R ⊔ S).rel a b ↔ R.rel a b ∨ S.rel a b := Iff.rfl
@[simp] theorem rel_inf : (R ⊓ S).rel a b ↔ R.rel a b ∧ S.rel a b := Iff.rfl
@[simp] theorem rel_top : (⊤ : HSetoidRel α β).rel a b := trivial
@[simp] theorem rel_bot : ¬ (⊥ : HSetoidRel α β).rel a b := id

@[simp] theorem rel_sSup {𝒮 : Set (HSetoidRel α β)} : (sSup 𝒮).rel a b ↔ ∃ R ∈ 𝒮, R.rel a b :=
  Iff.rfl

@[simp] theorem rel_sInf {𝒮 : Set (HSetoidRel α β)} : (sInf 𝒮).rel a b ↔ ∀ R ∈ 𝒮, R.rel a b :=
  Iff.rfl

@[simp] theorem rel_iSup {ι : Sort*} {f : ι → HSetoidRel α β} :
    (⨆ i, f i).rel a b ↔ ∃ i, (f i).rel a b := by
  simp only [iSup, rel_sSup, Set.mem_range, exists_exists_eq_and]

/-- Invariant relations on a setoid form a Boolean algebra: the complement of an invariant
relation is invariant. -/
instance instBooleanAlgebra : BooleanAlgebra (HSetoidRel α β) where
  __ := instCompleteLattice
  compl R := ⟨fun a b ↦ ¬ R.rel a b,
    fun h₁ h₂ h hr ↦ h (R.respects (Setoid.symm h₁) (Setoid.symm h₂) hr)⟩
  le_sup_inf _ _ _ _ _ h := by simp only [rel_inf, rel_sup] at h ⊢; tauto
  inf_compl_le_bot _ _ _ h := h.2 h.1
  top_le_sup_compl R a b _ := Classical.em (R.rel a b)

@[simp] theorem rel_compl : (Rᶜ).rel a b ↔ ¬ R.rel a b := Iff.rfl

variable {γ δ : Type*} [Setoid γ] [Setoid δ]

/-- Composition across three possibly different setoids. -/
def comp (R : HSetoidRel α β) (S : HSetoidRel β γ) : HSetoidRel α γ :=
  ⟨fun a c ↦ ∃ b, R.rel a b ∧ S.rel b c, fun ha hc ⟨b, hab, hbc⟩ ↦
    ⟨b, R.respects ha (Setoid.refl _) hab, S.respects (Setoid.refl _) hc hbc⟩⟩

/-- The identity relation is the setoid equivalence. -/
def ident (α : Type*) [Setoid α] : HSetoidRel α α :=
  ⟨(· ≈ ·), fun ha hb h ↦ Setoid.trans (Setoid.symm ha) (Setoid.trans h hb)⟩

/-- Converse interchanges the two setoids. -/
def converse (R : HSetoidRel α β) : HSetoidRel β α :=
  ⟨fun b a ↦ R.rel a b, fun hb ha h ↦ R.respects ha hb h⟩

@[simp] theorem rel_comp (R : HSetoidRel α β) (S : HSetoidRel β γ) (a : α) (c : γ) :
    (comp R S).rel a c ↔ ∃ b, R.rel a b ∧ S.rel b c := Iff.rfl

@[simp] theorem rel_ident (a b : α) : (ident α).rel a b ↔ a ≈ b := Iff.rfl

@[simp] theorem rel_converse (R : HSetoidRel α β) (a : α) (b : β) :
    (converse R).rel b a ↔ R.rel a b := Iff.rfl

theorem comp_assoc (R : HSetoidRel α β) (S : HSetoidRel β γ) (T : HSetoidRel γ δ) :
    comp (comp R S) T = comp R (comp S T) := by
  ext a d
  constructor
  · rintro ⟨c, ⟨b, hab, hbc⟩, hcd⟩
    exact ⟨b, hab, c, hbc, hcd⟩
  · rintro ⟨b, hab, c, hbc, hcd⟩
    exact ⟨c, ⟨b, hab, hbc⟩, hcd⟩

@[simp] theorem ident_comp (R : HSetoidRel α β) : comp (ident α) R = R := by
  ext a b
  exact ⟨fun ⟨c, hac, hcb⟩ ↦ R.respects (Setoid.symm hac) (Setoid.refl _) hcb,
    fun h ↦ ⟨a, Setoid.refl _, h⟩⟩

@[simp] theorem comp_ident (R : HSetoidRel α β) : comp R (ident β) = R := by
  ext a b
  exact ⟨fun ⟨c, hac, hcb⟩ ↦ R.respects (Setoid.refl _) hcb hac,
    fun h ↦ ⟨b, h, Setoid.refl _⟩⟩

/-- On one carrier, the new representation agrees with the original model. -/
def squareOrderIso : HSetoidRel α α ≃o SetoidRel α where
  toFun R := ⟨R.rel, R.respects⟩
  invFun R := ⟨R.rel, R.respects⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- Reuse the verified setoid closure on endomorphisms. -/
def closure (R : HSetoidRel α α) : HSetoidRel α α :=
  squareOrderIso.symm (squareOrderIso R)∗

/-- Strictly the same closure operation as on the categorical endomorphisms. -/
instance : KStar (HSetoidRel α α) := ⟨closure⟩

theorem rel_closure (R : HSetoidRel α α) (a b : α) :
    (closure R).rel a b ↔ Relation.ReflTransGen (fun x y ↦ x ≈ y ∨ R.rel x y) a b :=
  SetoidRel.rel_kstar

/-- A test is an invariant subset, presented as a subset of the quotient. -/
def test (P : Set (Quotient (inferInstance : Setoid α))) : HSetoidRel α α :=
  squareOrderIso.symm (SetoidRel.ofSet P)

@[simp] theorem rel_test (P : Set (Quotient (inferInstance : Setoid α))) (a b : α) :
    (test P).rel a b ↔ a ≈ b ∧ ⟦a⟧ ∈ P := Iff.rfl

/-- Interpret an invariant relation on equivalence classes. -/
def toQuotient (R : HSetoidRel α β) :
    SetRel (Quotient (inferInstance : Setoid α)) (Quotient (inferInstance : Setoid β)) :=
  {p | ∃ a b, ⟦a⟧ = p.1 ∧ ⟦b⟧ = p.2 ∧ R.rel a b}

@[simp] theorem mem_toQuotient (R : HSetoidRel α β) (a : α) (b : β) :
    (⟦a⟧, ⟦b⟧) ∈ toQuotient R ↔ R.rel a b := by
  constructor
  · rintro ⟨a', b', ha, hb, h⟩
    exact R.respects (Quotient.exact ha) (Quotient.exact hb) h
  · intro h
    exact ⟨a, b, rfl, rfl, h⟩

/-- Relations between quotient types are exactly the invariant relations. -/
def quotientOrderIso : HSetoidRel α β ≃o
    SetRel (Quotient (inferInstance : Setoid α)) (Quotient (inferInstance : Setoid β)) where
  toFun := toQuotient
  invFun R := ⟨fun a b ↦ (⟦a⟧, ⟦b⟧) ∈ R, fun ha hb h ↦ by
    simpa only [Quotient.sound ha, Quotient.sound hb] using h⟩
  left_inv R := by ext a b; exact mem_toQuotient R a b
  right_inv R := by
    ext ⟨a, b⟩
    induction a using Quotient.inductionOn with | h a =>
      induction b using Quotient.inductionOn with | h b =>
        exact mem_toQuotient _ a b
  map_rel_iff' := by
    intro R S
    constructor
    · intro h a b hab
      exact (mem_toQuotient _ a b).mp (h ((mem_toQuotient _ a b).mpr hab))
    · intro h ⟨a, b⟩
      induction a using Quotient.inductionOn with | h a =>
        induction b using Quotient.inductionOn with | h b =>
          intro hab
          exact (mem_toQuotient _ _ _).mpr (h a b ((mem_toQuotient _ _ _).mp hab))

@[simp] theorem toQuotient_comp (R : HSetoidRel α β) (S : HSetoidRel β γ) :
    toQuotient (comp R S) = (toQuotient R).comp (toQuotient S) := by
  ext ⟨a, c⟩
  induction a using Quotient.inductionOn with | h a =>
    induction c using Quotient.inductionOn with | h c =>
      simp only [mem_toQuotient, rel_comp, SetRel.mem_comp]
      constructor
      · rintro ⟨b, hab, hbc⟩
        exact ⟨⟦b⟧, (mem_toQuotient _ _ _).mpr hab, (mem_toQuotient _ _ _).mpr hbc⟩
      · rintro ⟨b, hab, hbc⟩
        induction b using Quotient.inductionOn with | h b =>
          exact ⟨b, (mem_toQuotient _ _ _).mp hab, (mem_toQuotient _ _ _).mp hbc⟩

end HSetoidRel

/-- State spaces equipped with an equivalence relation. -/
structure SetoidRelCat where
  carrier : Type u
  [setoid : Setoid carrier]

namespace SetoidRelCat

instance : CoeSort SetoidRelCat.{u} (Type u) := ⟨carrier⟩
attribute [instance] setoid

/-- Bundle a setoid as an object of its relation category. -/
abbrev of (α : Type u) [Setoid α] : SetoidRelCat := ⟨α⟩

/-- Morphisms retain their bundled setoids, even when two objects share a carrier. -/
def Hom (X Y : SetoidRelCat.{u}) := @HSetoidRel X Y X.setoid Y.setoid

namespace Hom

variable {X Y : SetoidRelCat.{u}}

/-- Build a morphism from an invariant relation on the two bundled carriers. -/
def ofRel (r : X → Y → Prop)
    (h : ∀ {a a' : X} {b b' : Y}, X.setoid.r a a' → Y.setoid.r b b' → r a b → r a' b') :
    Hom X Y := @HSetoidRel.mk X Y X.setoid Y.setoid r h

/-- The relation on representatives, without needing an ambient setoid instance. -/
def rel (R : Hom X Y) : X → Y → Prop := @HSetoidRel.rel X Y X.setoid Y.setoid R

theorem respects (R : Hom X Y) {a a' : X} {b b' : Y}
    (ha : X.setoid.r a a') (hb : Y.setoid.r b b') (h : R.rel a b) : R.rel a' b' :=
  @HSetoidRel.respects X Y X.setoid Y.setoid R a a' b b' ha hb h

end Hom

instance : Category SetoidRelCat.{u} where
  Hom := Hom
  id X := HSetoidRel.ident X
  comp := HSetoidRel.comp
  id_comp := HSetoidRel.ident_comp
  comp_id := HSetoidRel.comp_ident
  assoc := HSetoidRel.comp_assoc

instance : KleeneCategory SetoidRelCat.{u} where
  homSemilatticeSup _ _ := inferInstanceAs (SemilatticeSup (HSetoidRel _ _))
  homOrderBot _ _ := inferInstanceAs (OrderBot (HSetoidRel _ _))
  sup_comp R S T := by
    apply HSetoidRel.ext
    intro a c
    change (∃ b, (R.rel a b ∨ S.rel a b) ∧ T.rel b c) ↔
      (∃ b, R.rel a b ∧ T.rel b c) ∨ (∃ b, S.rel a b ∧ T.rel b c)
    simp only [or_and_right, exists_or]
  comp_sup R S T := by
    apply HSetoidRel.ext
    intro a c
    change (∃ b, R.rel a b ∧ (S.rel b c ∨ T.rel b c)) ↔
      (∃ b, R.rel a b ∧ S.rel b c) ∨ (∃ b, R.rel a b ∧ T.rel b c)
    simp only [and_or_left, exists_or]
  bot_comp R := by
    apply HSetoidRel.ext
    intro a c
    exact ⟨fun ⟨_, h, _⟩ ↦ h, False.elim⟩
  comp_bot R := by
    apply HSetoidRel.ext
    intro a c
    exact ⟨fun ⟨_, _, h⟩ ↦ h, False.elim⟩
  kstar := HSetoidRel.closure
  id_le_kstar R a b h := (HSetoidRel.rel_closure _ _ _).mpr (.single (.inl h))
  comp_kstar_le_kstar R a c h := by
    obtain ⟨b, hab, hbc⟩ := h
    exact (HSetoidRel.rel_closure _ _ _).mpr
      ((HSetoidRel.rel_closure _ _ _).mp hbc |>.head (.inr hab))
  kstar_comp_le_kstar R a c h := by
    obtain ⟨b, hab, hbc⟩ := h
    exact (HSetoidRel.rel_closure _ _ _).mpr
      ((HSetoidRel.rel_closure _ _ _).mp hab |>.tail (.inr hbc))
  comp_kstar_le_self R S h a c hac := by
    obtain ⟨b, hab, hbc⟩ := hac
    have path := (HSetoidRel.rel_closure R b c).mp hbc
    clear hbc
    induction path with
    | refl => exact hab
    | tail _ step ih =>
      rcases step with heq | hr
      · exact S.respects (Setoid.refl _) heq ih
      · exact h _ _ ⟨_, ih, hr⟩
  kstar_comp_le_self R S h a c hac := by
    obtain ⟨b, hab, hbc⟩ := hac
    have path := (HSetoidRel.rel_closure R a b).mp hab
    clear hab
    induction path using Relation.ReflTransGen.head_induction_on with
    | refl => exact hbc
    | head step _ ih =>
      rcases step with heq | hr
      · exact S.respects (Setoid.symm heq) (Setoid.refl _) ih
      · exact h _ _ ⟨_, hr, ih⟩

instance : KleeneCategoryWithConverse SetoidRelCat.{u} where
  converse := HSetoidRel.converse
  converse_converse R := rfl
  converse_comp R S := by
    apply HSetoidRel.ext
    intro a c
    change (∃ b, R.rel c b ∧ S.rel b a) ↔ ∃ b, S.rel b a ∧ R.rel c b
    simp only [and_comm]
  converse_sup R S := rfl

instance : BooleanKleeneCategory SetoidRelCat.{u} where
  inf {X Y} := @Min.min (HSetoidRel X Y) _
  top {X Y} := (⊤ : HSetoidRel X Y)
  compl {X Y} := @Compl.compl (HSetoidRel X Y) _
  inf_le_left _ _ _ _ h := h.1
  inf_le_right _ _ _ _ h := h.2
  le_inf _ _ _ hf hg a b h := ⟨hf a b h, hg a b h⟩
  le_sup_inf _ _ _ _ _ h := by rcases h with ⟨h | h, h' | h'⟩ <;> tauto
  le_top _ _ _ _ := trivial
  inf_compl_le_bot _ _ _ h := h.2 h.1
  top_le_sup_compl R a b _ := Classical.em (R.rel a b)

instance : RelationCategory SetoidRelCat.{u} where
  dedekind R S T a c h := by
    obtain ⟨⟨b, hab, hbc⟩, hat⟩ := h
    exact ⟨b, ⟨hab, c, hat, hbc⟩, hbc, a, hab, hat⟩

instance : TypedKAT SetoidRelCat.{u} (fun X ↦ Set (Quotient X.setoid)) where
  test := HSetoidRel.test
  test_bot {X} := by
    apply HSetoidRel.ext
    intro a b
    exact ⟨fun h ↦ h.2, False.elim⟩
  test_top {X} := by
    apply HSetoidRel.ext
    intro a b
    exact ⟨And.left, fun h ↦ ⟨h, trivial⟩⟩
  test_sup P Q := by
    apply HSetoidRel.ext
    intro a b
    change (a ≈ b ∧ (⟦a⟧ ∈ P ∨ ⟦a⟧ ∈ Q)) ↔
      (a ≈ b ∧ ⟦a⟧ ∈ P) ∨ (a ≈ b ∧ ⟦a⟧ ∈ Q)
    tauto
  test_inf P Q := by
    apply HSetoidRel.ext
    intro a b
    change (a ≈ b ∧ (⟦a⟧ ∈ P ∧ ⟦a⟧ ∈ Q)) ↔
      ∃ c, (a ≈ c ∧ ⟦a⟧ ∈ P) ∧ (c ≈ b ∧ ⟦c⟧ ∈ Q)
    constructor
    · rintro ⟨hab, hp, hq⟩
      exact ⟨a, ⟨Setoid.refl _, hp⟩, hab, hq⟩
    · rintro ⟨c, ⟨hac, hp⟩, hcb, hq⟩
      exact ⟨Setoid.trans hac hcb, hp, by simpa only [Quotient.sound hac] using hq⟩

variable {X Y Z : SetoidRelCat.{u}}

/-- View a typed endomorphism in the original homogeneous API, with its setoid fixed. -/
def toSquare (R : X ⟶ X) : @SetoidRel X X.setoid :=
  @HSetoidRel.squareOrderIso X X.setoid R

@[simp] theorem rel_comp (R : X ⟶ Y) (S : Y ⟶ Z) (a : X) (c : Z) :
    (R ≫ S).rel a c ↔ ∃ b, R.rel a b ∧ S.rel b c := Iff.rfl

@[simp] theorem rel_id (a b : X) : ((𝟙 X) : HSetoidRel X X).rel a b ↔ a ≈ b := Iff.rfl

theorem rel_kstar (R : X ⟶ X) (a b : X) :
    (R∗).rel a b ↔ Relation.ReflTransGen (fun x y ↦ x ≈ y ∨ R.rel x y) a b :=
  HSetoidRel.rel_closure R a b

@[simp] theorem rel_converse (R : X ⟶ Y) (a : X) (b : Y) :
    Rᵒ.rel b a ↔ R.rel a b := Iff.rfl

@[simp] theorem rel_test (P : Set (Quotient X.setoid)) (a b : X) :
    (TypedKAT.test (T := fun X : SetoidRelCat ↦ Set (Quotient X.setoid)) P : X ⟶ X).rel a b ↔
      a ≈ b ∧ ⟦a⟧ ∈ P := Iff.rfl

/-- The square part agrees with the original setoid model, including its closure. -/
@[simp] theorem square_kstar (R : X ⟶ X) :
    HSetoidRel.squareOrderIso (R∗) = (HSetoidRel.squareOrderIso R)∗ := rfl

@[simp] theorem square_comp (R S : X ⟶ X) :
    HSetoidRel.squareOrderIso (R ≫ S) =
      HSetoidRel.squareOrderIso R * HSetoidRel.squareOrderIso S := rfl

/-- The categorical interpretation sends a setoid to its quotient type. -/
def toRelCat : SetoidRelCat.{u} ⥤ RelCat.{u} where
  obj X := Quotient X.setoid
  map R := .ofRel (HSetoidRel.toQuotient R)
  map_id X := by
    apply RelCat.Hom.ext
    ext ⟨a, b⟩
    induction a using Quotient.inductionOn with | h a =>
      induction b using Quotient.inductionOn with | h b =>
        exact (HSetoidRel.mem_toQuotient _ _ _).trans Quotient.eq.symm
  map_comp R S := RelCat.Hom.ext _ _ (HSetoidRel.toQuotient_comp R S)

/-- Quotient interpretation preserves and reflects inclusion, and represents every relation. -/
def homOrderIso : (X ⟶ Y) ≃o (toRelCat.obj X ⟶ toRelCat.obj Y) where
  toFun := toRelCat.map
  invFun R := HSetoidRel.quotientOrderIso.symm R.rel
  left_inv R := HSetoidRel.quotientOrderIso.left_inv R
  right_inv R := RelCat.Hom.ext _ _ (HSetoidRel.quotientOrderIso.right_inv R.rel)
  map_rel_iff' := HSetoidRel.quotientOrderIso.map_rel_iff'

instance : toRelCat.Faithful where
  map_injective h := homOrderIso.injective h

instance : toRelCat.Full where
  map_surjective := homOrderIso.surjective

@[simp] theorem map_inf (R S : X ⟶ Y) : toRelCat.map (R ⊓ S) = toRelCat.map R ⊓ toRelCat.map S :=
  homOrderIso.map_inf R S

@[simp] theorem map_compl (R : X ⟶ Y) : toRelCat.map Rᶜ = (toRelCat.map R)ᶜ := by
  apply RelCat.Hom.ext
  ext ⟨a, b⟩
  induction a using Quotient.inductionOn with | h a =>
    induction b using Quotient.inductionOn with | h b =>
      change (⟦a⟧, ⟦b⟧) ∈ HSetoidRel.toQuotient Rᶜ ↔
        ¬ (⟦a⟧, ⟦b⟧) ∈ HSetoidRel.toQuotient R
      simp only [HSetoidRel.mem_toQuotient, HSetoidRel.rel_compl]

@[simp] theorem map_kstar (R : X ⟶ X) : toRelCat.map R∗ = (toRelCat.map R)∗ := by
  apply RelCat.Hom.ext
  ext ⟨a, b⟩
  induction a using Quotient.inductionOn with | h a =>
    induction b using Quotient.inductionOn with | h b =>
      change (⟦a⟧, ⟦b⟧) ∈ HSetoidRel.toQuotient (R∗) ↔
        Relation.ReflTransGen (fun x y ↦ (x, y) ∈ HSetoidRel.toQuotient R) ⟦a⟧ ⟦b⟧
      rw [HSetoidRel.mem_toQuotient]
      change (HSetoidRel.closure R).rel a b ↔ _
      rw [HSetoidRel.rel_closure]
      constructor
      · intro path
        induction path with
        | refl => exact .refl
        | tail _ step ih =>
          rcases step with heq | hr
          · simpa only [Quotient.sound heq] using ih
          · exact ih.tail ((HSetoidRel.mem_toQuotient _ _ _).mpr hr)
      · intro path
        have lift : ∀ {q r : Quotient X.setoid},
            Relation.ReflTransGen (fun x y ↦ (x, y) ∈ HSetoidRel.toQuotient R) q r →
            ∀ a b, ⟦a⟧ = q → ⟦b⟧ = r →
              Relation.ReflTransGen (fun x y ↦ x ≈ y ∨ R.rel x y) a b := by
          intro q r h
          induction h with
          | refl =>
            intro a b ha hb
            exact .single (.inl (Quotient.exact (ha.trans hb.symm)))
          | @tail q r hpath hstep ih =>
            intro a b ha hb
            induction q using Quotient.inductionOn with | h c =>
              have hr : R.rel c b := (HSetoidRel.mem_toQuotient _ _ _).mp
                (by simpa only [hb] using hstep)
              exact (ih a c ha rfl).tail (.inr hr)
        exact lift path a b rfl rfl

@[simp] theorem map_converse (R : X ⟶ Y) : toRelCat.map Rᵒ = (toRelCat.map R)ᵒ := by
  apply RelCat.Hom.ext
  ext ⟨b, a⟩
  induction a using Quotient.inductionOn with | h a =>
    induction b using Quotient.inductionOn with | h b =>
      change (⟦b⟧, ⟦a⟧) ∈ HSetoidRel.toQuotient (HSetoidRel.converse R) ↔
          (⟦a⟧, ⟦b⟧) ∈ HSetoidRel.toQuotient R
      exact (HSetoidRel.mem_toQuotient (HSetoidRel.converse R) b a).trans
        (HSetoidRel.mem_toQuotient R a b).symm

/-- Quotient interpretation as a typed KAT homomorphism; the test map is the identity. -/
def toRelCatKAT : TypedKAT.Hom (D := RelCat.{u})
    (fun X : SetoidRelCat.{u} ↦ Set (Quotient X.setoid)) Set toRelCat.obj where
  map := toRelCat.map
  testMap _ := BoundedLatticeHom.id _
  map_id := toRelCat.map_id
  map_comp := toRelCat.map_comp
  map_bot := homOrderIso.map_bot
  map_sup := homOrderIso.map_sup
  map_star := map_kstar
  map_test P := by
    apply RelCat.Hom.ext
    ext ⟨a, b⟩
    induction a using Quotient.inductionOn with | h a =>
      induction b using Quotient.inductionOn with | h b =>
        change (⟦a⟧, ⟦b⟧) ∈ HSetoidRel.toQuotient (HSetoidRel.test P) ↔
          ⟦a⟧ = ⟦b⟧ ∧ ⟦a⟧ ∈ P
        simp only [HSetoidRel.mem_toQuotient, HSetoidRel.rel_test, Quotient.eq]

/-- Residuals quantify over representatives; invariance makes this independent of choice. -/
theorem rel_ldiv (R : X ⟶ Y) (T : X ⟶ Z) (b : Y) (c : Z) :
    (R ⇘ T).rel b c ↔ ∀ a, R.rel a b → T.rel a c := by
  classical
  change (¬ ∃ a, R.rel a b ∧ ¬ T.rel a c) ↔ _
  simp only [not_exists, not_and, not_not]

theorem rel_rdiv (T : X ⟶ Z) (S : Y ⟶ Z) (a : X) (b : Y) :
    (T ⇙ S).rel a b ↔ ∀ c, S.rel b c → T.rel a c := by
  classical
  change (¬ ∃ c, ¬ T.rel a c ∧ S.rel b c) ↔ _
  simp only [not_exists, not_and]
  exact forall_congr' fun _ ↦ by tauto

@[simp] theorem map_ldiv (R : X ⟶ Y) (T : X ⟶ Z) :
    toRelCat.map (R ⇘ T) = toRelCat.map R ⇘ toRelCat.map T := by
  rw [ResiduatedKleeneCategory.ldiv_eq_compl, map_compl, toRelCat.map_comp,
    map_converse, map_compl, ← ResiduatedKleeneCategory.ldiv_eq_compl]

@[simp] theorem map_rdiv (T : X ⟶ Z) (S : Y ⟶ Z) :
    toRelCat.map (T ⇙ S) = toRelCat.map T ⇙ toRelCat.map S := by
  rw [ResiduatedKleeneCategory.rdiv_eq_compl, map_compl, toRelCat.map_comp,
    map_converse, map_compl, ← ResiduatedKleeneCategory.rdiv_eq_compl]

end SetoidRelCat
