import RelationAlgebra.Models.FinRel
import RelationAlgebra.TypedIteration
import RelationAlgebra.TypedResiduated
import RelationAlgebra.TypedKAT.Hom

/-!
# The category of finite, decidable relations

`FinRelCat` bundles a finite type with its decidable equality. Its morphisms are the
existing Boolean-valued `FinRel`s, so composition, tests, converse, and closure remain
computable. `toRelCat` preserves the typed KAT structure, and `homOrderIso` identifies
each hom-set with all relations between the corresponding finite types.

This supplies the categorical part of `theories/fhrel.v` in Damien Pous' library
[relation-algebra](https://github.com/damien-pous/relation-algebra), developed upstream
by Christian Doczkal. The closure algorithm is the one already verified in `FinRel.lean`.
-/

open CategoryTheory
open scoped Computability SetRel KleeneCategoryWithConverse ResiduatedKleeneCategory

universe u

namespace FinRel

variable {α β γ δ : Type u}

/-- Heterogeneous converse is Boolean matrix transposition. -/
def converse (R : FinRel α β) : FinRel β α := fun b a ↦ R a b

@[simp] theorem converse_apply (R : FinRel α β) (a : α) (b : β) :
    converse R b a = R a b := rfl

@[simp] theorem comp_iff [Fintype β] {R : FinRel α β} {S : FinRel β γ} {a : α} {c : γ} :
    comp R S a c ↔ ∃ b, R a b ∧ S b c := by simp [comp]

theorem comp_assoc [Fintype β] [Fintype γ]
    (R : FinRel α β) (S : FinRel β γ) (T : FinRel γ δ) :
    comp (comp R S) T = comp R (comp S T) := by
  apply ext_iff'
  intro a d
  simp only [comp_iff]
  constructor
  · rintro ⟨c, ⟨b, hab, hbc⟩, hcd⟩
    exact ⟨b, hab, c, hbc, hcd⟩
  · rintro ⟨b, hab, c, hbc, hcd⟩
    exact ⟨c, ⟨b, hab, hbc⟩, hcd⟩

@[simp] theorem one_comp [Fintype α] [DecidableEq α] (R : FinRel α β) :
    comp 1 R = R := by apply ext_iff'; intro a b; simp

@[simp] theorem comp_one [Fintype β] [DecidableEq β] (R : FinRel α β) :
    comp R 1 = R := by apply ext_iff'; intro a b; simp

@[gcongr] theorem comp_mono [Fintype β] {R R' : FinRel α β} {S S' : FinRel β γ}
    (hR : R ≤ R') (hS : S ≤ S') : comp R S ≤ comp R' S' := by
  apply le_def.mpr
  intro a c h
  obtain ⟨b, hab, hbc⟩ := comp_iff.mp h
  exact comp_iff.mpr ⟨b, le_def.mp hR a b hab, le_def.mp hS b c hbc⟩

@[simp] theorem sup_comp [Fintype β] (R S : FinRel α β) (T : FinRel β γ) :
    comp (R ⊔ S) T = comp R T ⊔ comp S T := by
  apply ext_iff'; intro a c; simp [or_and_right, exists_or]

@[simp] theorem comp_sup [Fintype β] (R : FinRel α β) (S T : FinRel β γ) :
    comp R (S ⊔ T) = comp R S ⊔ comp R T := by
  apply ext_iff'; intro a c; simp [and_or_left, exists_or]

@[simp] theorem bot_comp [Fintype β] (R : FinRel β γ) :
    comp (⊥ : FinRel α β) R = ⊥ := by apply ext_iff'; intro a c; simp

@[simp] theorem comp_bot [Fintype β] (R : FinRel α β) :
    comp R (⊥ : FinRel β γ) = ⊥ := by apply ext_iff'; intro a c; simp

@[simp] theorem converse_converse (R : FinRel α β) : converse (converse R) = R := rfl

@[simp] theorem converse_comp [Fintype β] (R : FinRel α β) (S : FinRel β γ) :
    converse (comp R S) = comp (converse S) (converse R) := by
  apply ext_iff'; intro c a; simp [and_comm]

@[simp] theorem converse_sup (R S : FinRel α β) :
    converse (R ⊔ S) = converse R ⊔ converse S := rfl

@[simp] theorem toSetRel_comp [Fintype β] (R : FinRel α β) (S : FinRel β γ) :
    toSetRel (comp R S) = (toSetRel R).comp (toSetRel S) := by
  ext ⟨a, c⟩; simp [SetRel.mem_comp]

@[simp] theorem toSetRel_converse (R : FinRel α β) :
    toSetRel (converse R) = (toSetRel R).inv := rfl

/-- Every relation has a Boolean representation, classically. The forward map is computable. -/
noncomputable def heteroOrderIsoSetRel : FinRel α β ≃o SetRel α β := by
  classical
  exact
    { toFun := toSetRel
      invFun := fun R a b ↦ decide ((a, b) ∈ R)
      left_inv := fun R ↦ ext_iff' fun a b ↦ by simp
      right_inv := fun R ↦ Set.ext fun p ↦ by simp
      map_rel_iff' := toSetRel_le_iff }

end FinRel

/-- Finite state spaces with chosen computational data, viewed through relations. -/
structure FinRelCat where
  carrier : Type u
  [finite : Fintype carrier]
  [decidableEq : DecidableEq carrier]

namespace FinRelCat

-- Keep the computational Boolean operations when constructing category instances.
attribute [local instance] FinRel.instBooleanAlgebra

instance : CoeSort FinRelCat.{u} (Type u) := ⟨carrier⟩
attribute [instance] finite decidableEq

/-- Bundle a finite state space. -/
abbrev of (α : Type u) [Fintype α] [DecidableEq α] : FinRelCat := ⟨α⟩

instance : Category FinRelCat.{u} where
  Hom X Y := FinRel X Y
  id _ := 1
  comp := FinRel.comp
  id_comp := FinRel.one_comp
  comp_id := FinRel.comp_one
  assoc := FinRel.comp_assoc

instance instKleeneCategory : KleeneCategory FinRelCat.{u} where
  homSemilatticeSup _ _ := FinRel.instBooleanAlgebra.toSemilatticeSup
  homOrderBot _ _ := FinRel.instBooleanAlgebra.toBiheytingAlgebra.toOrderBot
  sup_comp := FinRel.sup_comp
  comp_sup := FinRel.comp_sup
  bot_comp := FinRel.bot_comp
  comp_bot := FinRel.comp_bot
  kstar R := FinRel.tc R
  id_le_kstar R := FinRel.one_le_tc R
  comp_kstar_le_kstar {X} R := mul_kstar_le_kstar (α := FinRel X X) (a := R)
  kstar_comp_le_kstar {X} R := kstar_mul_le_kstar (α := FinRel X X) (a := R)
  comp_kstar_le_self R S h := by
    apply FinRel.le_def.mpr
    intro a c hac
    obtain ⟨b, hab, hbc⟩ := FinRel.comp_iff.mp hac
    have path := (FinRel.kstar_iff R b c).mp hbc
    clear hac hbc
    induction path with
    | refl => exact hab
    | tail _ hcd ih => exact FinRel.le_def.mp h _ _ (FinRel.comp_iff.mpr ⟨_, ih, hcd⟩)
  kstar_comp_le_self R S h := by
    apply FinRel.le_def.mpr
    intro a c hac
    obtain ⟨b, hab, hbc⟩ := FinRel.comp_iff.mp hac
    have path := (FinRel.kstar_iff R a b).mp hab
    clear hac hab
    induction path using Relation.ReflTransGen.head_induction_on with
    | refl => exact hbc
    | head hab' _ ih => exact FinRel.le_def.mp h _ _ (FinRel.comp_iff.mpr ⟨_, hab', ih⟩)

instance : KleeneCategoryWithConverse FinRelCat.{u} where
  converse := FinRel.converse
  converse_converse := FinRel.converse_converse
  converse_comp := FinRel.converse_comp
  converse_sup := FinRel.converse_sup

instance : BooleanKleeneCategory FinRelCat.{u} where
  inf R S := fun a b ↦ R a b && S a b
  top := fun _ _ ↦ true
  compl R := fun a b ↦ !R a b
  inf_le_left {X Y} R S := inf_le_left (α := FinRel X Y) (a := R) (b := S)
  inf_le_right {X Y} R S := inf_le_right (α := FinRel X Y) (a := R) (b := S)
  le_inf {X Y} R S T := le_inf (α := FinRel X Y) (c := R) (a := S) (b := T)
  le_sup_inf {X Y} R S T := le_sup_inf (α := FinRel X Y) (x := R) (y := S) (z := T)
  le_top {X Y} R := le_top (α := FinRel X Y) (a := R)
  inf_compl_le_bot {X Y} R := (inf_compl_eq_bot (α := FinRel X Y) (a := R)).le
  top_le_sup_compl {X Y} R := (sup_compl_eq_top (α := FinRel X Y) (x := R)).ge

instance : RelationCategory FinRelCat.{u} where
  dedekind R S T := by
    apply FinRel.le_def.mpr
    intro a c h
    change (FinRel.comp R S a c && T a c) = true at h
    obtain ⟨hac, hat⟩ := Bool.and_eq_true_iff.mp h
    obtain ⟨b, hab, hbc⟩ := FinRel.comp_iff.mp hac
    apply FinRel.comp_iff.mpr
    refine ⟨b, ?_, ?_⟩
    · change (R ⊓ FinRel.comp T (FinRel.converse S)) a b
      exact Bool.and_eq_true_iff.mpr ⟨hab, FinRel.comp_iff.mpr ⟨c, hat, hbc⟩⟩
    · change (S ⊓ FinRel.comp (FinRel.converse R) T) b c
      exact Bool.and_eq_true_iff.mpr ⟨hbc, FinRel.comp_iff.mpr ⟨a, hab, hat⟩⟩

instance : TypedKAT FinRelCat.{u} (fun X ↦ X → Bool) where
  test := FinRel.ofPred
  test_bot {X} := by
    apply FinRel.ext
    intro a b
    change (decide (a = b) && false) = false
    simp
  test_top {X} := by
    apply FinRel.ext
    intro a b
    change (decide (a = b) && true) = decide (a = b)
    simp
  test_sup {X} p q := KAT.test_sup (K := FinRel X X) p q
  test_inf {X} p q := KAT.test_inf (K := FinRel X X) p q

/-- Both residuals are computable finite universal quantifiers. -/
instance : ResiduatedKleeneCategory FinRelCat.{u} where
  ldiv R T := fun b c ↦ decide (∀ a, R a b → T a c)
  rdiv T S := fun a b ↦ decide (∀ c, S b c → T a c)
  ldiv_spec R S T := by
    change (∀ b c, S b c → decide (∀ a, R a b → T a c) = true) ↔
      ∀ a c, FinRel.comp R S a c → T a c
    simp only [decide_eq_true_eq]
    constructor
    · intro h a c hac
      obtain ⟨b, hab, hbc⟩ := FinRel.comp_iff.mp hac
      exact h b c hbc a hab
    · intro h b c hbc a hab
      exact h a c (FinRel.comp_iff.mpr ⟨b, hab, hbc⟩)
  rdiv_spec R S T := by
    change (∀ a b, R a b → decide (∀ c, S b c → T a c) = true) ↔
      ∀ a c, FinRel.comp R S a c → T a c
    simp only [decide_eq_true_eq]
    constructor
    · intro h a c hac
      obtain ⟨b, hab, hbc⟩ := FinRel.comp_iff.mp hac
      exact h a b hab c hbc
    · intro h a b hab c hbc
      exact h a c (FinRel.comp_iff.mpr ⟨b, hab, hbc⟩)

variable {X Y Z : FinRelCat.{u}}

instance homDecidableEq : DecidableEq (X ⟶ Y) := FinRel.instDecidableEq

instance homDecidableLE (R S : X ⟶ Y) : Decidable (R ≤ S) := FinRel.decidableLE R S

@[simp] theorem comp_apply (R : X ⟶ Y) (S : Y ⟶ Z) (a : X) (c : Z) :
    (R ≫ S) a c ↔ ∃ b, R a b ∧ S b c := FinRel.comp_iff

@[simp] theorem id_apply (a b : X) : (𝟙 X) a b ↔ a = b := FinRel.one_iff

@[simp] theorem converse_apply (R : X ⟶ Y) (a : X) (b : Y) : Rᵒ b a = R a b := rfl

theorem kstar_apply (R : X ⟶ X) (a b : X) :
    R∗ a b ↔ Relation.ReflTransGen (fun x y ↦ R x y) a b := FinRel.kstar_iff R a b

theorem kplus_apply (R : X ⟶ X) (a b : X) :
    R⁺ a b ↔ Relation.TransGen (fun x y ↦ R x y) a b := by
  change FinRel.comp R (FinRel.tc R) a b ↔ _
  simp only [FinRel.comp_iff, ← FinRel.kstar_eq_tc, FinRel.kstar_iff]
  exact (Relation.TransGen.head'_iff (r := fun x y ↦ R x y)).symm

@[simp] theorem ldiv_apply (R : X ⟶ Y) (T : X ⟶ Z) (b : Y) (c : Z) :
    (R ⇘ T) b c ↔ ∀ a, R a b → T a c := by
  change decide (∀ a, R a b → T a c) = true ↔ _
  simp only [decide_eq_true_eq]

@[simp] theorem rdiv_apply (T : X ⟶ Z) (S : Y ⟶ Z) (a : X) (b : Y) :
    (T ⇙ S) a b ↔ ∀ c, S b c → T a c := by
  change decide (∀ c, S b c → T a c) = true ↔ _
  simp only [decide_eq_true_eq]

@[simp] theorem test_apply (p : X → Bool) (a b : X) :
    (TypedKAT.test (T := fun X : FinRelCat ↦ X → Bool) p : X ⟶ X) a b ↔ a = b ∧ p a := by
  change (decide (a = b) && p a) = true ↔ _
  simp

/-- The faithful interpretation in ordinary heterogeneous relations. -/
def toRelCat : FinRelCat.{u} ⥤ RelCat.{u} where
  obj X := X.carrier
  map R := .ofRel (FinRel.toSetRel R)
  map_id X := by ext ⟨a, b⟩; simp [RelCat.Hom.rel_id, SetRel.id]
  map_comp R S := by ext ⟨a, c⟩; simp [RelCat.Hom.rel_comp, SetRel.mem_comp]

/-- The interpretation is an order isomorphism on every hom-set. -/
noncomputable def homOrderIso : (X ⟶ Y) ≃o (toRelCat.obj X ⟶ toRelCat.obj Y) where
  toFun := toRelCat.map
  invFun R := FinRel.heteroOrderIsoSetRel.symm R.rel
  left_inv R := FinRel.heteroOrderIsoSetRel.left_inv R
  right_inv R := by
    apply RelCat.Hom.ext
    exact FinRel.heteroOrderIsoSetRel.right_inv R.rel
  map_rel_iff' := FinRel.toSetRel_le_iff

instance : toRelCat.Faithful where
  map_injective h := homOrderIso.injective h

noncomputable instance : toRelCat.Full where
  map_surjective := homOrderIso.surjective

@[simp] theorem map_inf (R S : X ⟶ Y) : toRelCat.map (R ⊓ S) = toRelCat.map R ⊓ toRelCat.map S :=
  homOrderIso.map_inf R S

@[simp] theorem map_compl (R : X ⟶ Y) : toRelCat.map Rᶜ = (toRelCat.map R)ᶜ :=
  by
    apply RelCat.Hom.ext
    ext ⟨a, b⟩
    change (!R a b) = true ↔ ¬ R a b = true
    simp

@[simp] theorem map_ldiv (R : X ⟶ Y) (T : X ⟶ Z) :
    toRelCat.map (R ⇘ T) = toRelCat.map R ⇘ toRelCat.map T := by
  apply RelCat.Hom.ext
  ext ⟨b, c⟩
  exact (ldiv_apply R T b c).trans (RelCat.Hom.mem_ldiv (toRelCat.map R) (toRelCat.map T) b c).symm

@[simp] theorem map_rdiv (T : X ⟶ Z) (S : Y ⟶ Z) :
    toRelCat.map (T ⇙ S) = toRelCat.map T ⇙ toRelCat.map S := by
  apply RelCat.Hom.ext
  ext ⟨a, b⟩
  exact (rdiv_apply T S a b).trans (RelCat.Hom.mem_rdiv (toRelCat.map T) (toRelCat.map S) a b).symm

@[simp] theorem map_kstar (R : X ⟶ X) : toRelCat.map R∗ = (toRelCat.map R)∗ := by
  ext ⟨a, b⟩
  exact kstar_apply R a b

@[simp] theorem map_converse (R : X ⟶ Y) : toRelCat.map Rᵒ = (toRelCat.map R)ᵒ := rfl

/-- The interpretation also preserves Boolean tests and Kleene star. -/
def toRelCatKAT : TypedKAT.Hom (D := RelCat.{u}) (fun X : FinRelCat.{u} ↦ X → Bool)
    Set toRelCat.obj where
  map := toRelCat.map
  testMap X :=
    { toFun := fun p ↦ {a | p a}
      map_sup' := by intros; ext a; simp
      map_inf' := by intros; ext a; simp
      map_top' := by
        ext a
        change true = true ↔ True
        simp
      map_bot' := by
        ext a
        change false = true ↔ False
        simp }
  map_id := toRelCat.map_id
  map_comp := toRelCat.map_comp
  map_bot {X Y} := by
    apply RelCat.Hom.ext
    ext ⟨a, b⟩
    change false = true ↔ False
    simp
  map_sup R S := by
    apply RelCat.Hom.ext
    ext ⟨a, b⟩
    change (R a b || S a b) = true ↔ _
    simp only [Bool.or_eq_true]
    rfl
  map_star := map_kstar
  map_test p := by
    apply RelCat.Hom.ext
    ext ⟨a, b⟩
    exact test_apply p a b

end FinRelCat
