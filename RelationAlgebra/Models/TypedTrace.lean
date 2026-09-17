import RelationAlgebra.Models.Trace
import RelationAlgebra.TypedKAT
import RelationAlgebra.TypedIteration
import RelationAlgebra.TypedResiduated

/-!
# General typed trace languages

Actions have source and target objects; states range over an arbitrary shared type.
As in Damien Pous' `theories/traces.v`, action endpoints determine typing, while states
determine whether two traces fuse. There are no finite-alphabet or atom-bound assumptions.

`TypedTrace.Language` is a set of well-typed traces, and `TraceCat` is their Kleene category
with tests. Each hom-set is a complete Boolean algebra. Top, complement, and residuals
are restricted to well-typed traces. Forgetting types preserves identity, composition,
unions, star, and tests, but does not in general preserve top or complement.

Converse is not supplied: reversing an action need not respect its declared endpoints.
This matches the supported fragment of Pous' typed trace model.

Reference: [Pous, relation-algebra, traces.v](https://github.com/damien-pous/relation-algebra/blob/2d2af3631929399bbac56f57b3e15302d8697e1c/theories/traces.v).
-/

open CategoryTheory
open scoped Computability TraceLang ResiduatedKleeneCategory

universe u v w

namespace TypedTrace

variable {σ : Type u} {α : Type v} {I : Type w} (src tgt : α → I)

/-- A list of actions respects its source, intermediate objects, and target. -/
def PathTyped : I → List α → I → Prop
  | X, [], Y => X = Y
  | X, a :: l, Y => X = src a ∧ PathTyped (tgt a) l Y

variable {src tgt} {X Y Z : I}

@[simp] theorem pathTyped_nil : PathTyped src tgt X [] Y ↔ X = Y := Iff.rfl

@[simp] theorem pathTyped_cons (a : α) (l : List α) :
    PathTyped src tgt X (a :: l) Y ↔ X = src a ∧ PathTyped src tgt (tgt a) l Y := Iff.rfl

theorem pathTyped_append (l r : List α) :
    PathTyped src tgt X (l ++ r) Z ↔
      ∃ Y, PathTyped src tgt X l Y ∧ PathTyped src tgt Y r Z := by
  induction l generalizing X with
  | nil => simp
  | cons a l ih => simp only [List.cons_append, pathTyped_cons, ih]; aesop

/-- Typing ignores states, but checks every action in the trace. -/
def WellTyped (src tgt : α → I) (X Y : I) (t : Trace σ α) : Prop :=
  PathTyped src tgt X (t.2.map Prod.fst) Y

@[simp] theorem wellTyped_nil (s : σ) : WellTyped src tgt X Y (s, []) ↔ X = Y := Iff.rfl

theorem wellTyped_append {s s' : σ} {l r : List (α × σ)}
    (hl : WellTyped src tgt X Y (s, l)) (hr : WellTyped src tgt Y Z (s', r)) :
    WellTyped src tgt X Z (s, l ++ r) := by
  exact (List.map_append .. ▸ (pathTyped_append _ _).mpr ⟨Y, hl, hr⟩ :
    PathTyped src tgt X ((l ++ r).map Prod.fst) Z)

/-- A trace language whose actions have the indicated endpoints. -/
structure Language (σ : Type u) {α : Type v} {I : Type w} (src tgt : α → I) (X Y : I) where
  traces : TraceLang σ α
  typed : ∀ t ∈ traces, WellTyped src tgt X Y t

namespace Language

variable {L M : Language σ src tgt X Y}

@[ext] theorem ext (h : L.traces = M.traces) : L = M := by
  cases L; cases M; cases h; rfl

theorem traces_injective : Function.Injective (traces : Language σ src tgt X Y → _) :=
  fun _ _ ↦ ext

instance : CompleteLattice (Language σ src tgt X Y) where
  le L M := L.traces ⊆ M.traces
  le_refl _ := Set.Subset.rfl
  le_trans _ _ _ := Set.Subset.trans
  le_antisymm _ _ h h' := ext (h.antisymm h')
  sup L M := ⟨L.traces ∪ M.traces, fun t h ↦ h.elim (L.typed t) (M.typed t)⟩
  le_sup_left _ _ := Set.subset_union_left
  le_sup_right _ _ := Set.subset_union_right
  sup_le _ _ _ := Set.union_subset
  inf L M := ⟨L.traces ∩ M.traces, fun t h ↦ L.typed t h.1⟩
  inf_le_left _ _ := Set.inter_subset_left
  inf_le_right _ _ := Set.inter_subset_right
  le_inf _ _ _ := Set.subset_inter
  top := ⟨{t | WellTyped src tgt X Y t}, fun _ h ↦ h⟩
  le_top L := L.typed
  bot := ⟨∅, fun _ h ↦ h.elim⟩
  bot_le _ := Set.empty_subset _
  sSup S := ⟨{t | ∃ L ∈ S, t ∈ L.traces}, fun t ⟨L, _, h⟩ ↦ L.typed t h⟩
  isLUB_sSup S := ⟨fun L h _ ht ↦ ⟨L, h, ht⟩, fun _ h _ ⟨L, hL, ht⟩ ↦ h hL ht⟩
  sInf S := ⟨{t | WellTyped src tgt X Y t ∧ ∀ L ∈ S, t ∈ L.traces}, fun _ h ↦ h.1⟩
  isGLB_sInf S := ⟨fun L h _ ht ↦ ht.2 L h, fun L h t ht ↦ ⟨L.typed t ht, fun _ hm ↦ h hm ht⟩⟩

instance : BooleanAlgebra (Language σ src tgt X Y) where
  __ := (inferInstance : CompleteLattice (Language σ src tgt X Y))
  compl L := ⟨{t | WellTyped src tgt X Y t ∧ t ∉ L.traces}, fun _ h ↦ h.1⟩
  le_sup_inf _ _ _ _ h := by rcases h with ⟨h | h, h' | h'⟩ <;> tauto
  inf_compl_le_bot _ _ h := h.2.2 h.1
  top_le_sup_compl L t ht := by
    by_cases h : t ∈ L.traces
    · exact Or.inl h
    · exact Or.inr ⟨ht, h⟩

@[simp] theorem traces_bot : (⊥ : Language σ src tgt X Y).traces = ∅ := rfl
@[simp] theorem traces_sup (L M : Language σ src tgt X Y) :
    (L ⊔ M).traces = L.traces ∪ M.traces := rfl
@[simp] theorem traces_inf (L M : Language σ src tgt X Y) :
    (L ⊓ M).traces = L.traces ∩ M.traces := rfl
@[simp] theorem mem_top (t : Trace σ α) :
    t ∈ (⊤ : Language σ src tgt X Y).traces ↔ WellTyped src tgt X Y t := Iff.rfl
@[simp] theorem mem_compl (L : Language σ src tgt X Y) (t : Trace σ α) :
    t ∈ Lᶜ.traces ↔ WellTyped src tgt X Y t ∧ t ∉ L.traces := Iff.rfl

/-- Restrict an arbitrary language to traces with these endpoints. -/
def restrict (X Y : I) (L : TraceLang σ α) : Language σ src tgt X Y :=
  ⟨{t | WellTyped src tgt X Y t ∧ t ∈ L}, fun _ h ↦ h.1⟩

@[simp] theorem restrict_traces (L : Language σ src tgt X Y) :
    restrict X Y L.traces = L := by
  apply ext
  ext t
  exact ⟨And.right, fun h ↦ ⟨L.typed t h, h⟩⟩

/-- Fusion of languages with compatible action types. -/
def comp (L : Language σ src tgt X Y) (M : Language σ src tgt Y Z) :
    Language σ src tgt X Z where
  traces := L.traces * M.traces
  typed := by
    rintro ⟨s, l⟩ ⟨l₁, l₂, rfl, hL, hM⟩
    exact wellTyped_append (L.typed _ hL) (M.typed _ hM)

/-- Empty traces are identities at every object. -/
def ident (X : I) : Language σ src tgt X X :=
  ⟨1, by rintro ⟨s, l⟩ (h : l = []); subst l; rfl⟩

private theorem pow_typed (L : Language σ src tgt X X) (n : ℕ) :
    ∀ t ∈ L.traces ^ n, WellTyped src tgt X X t := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact (ident (σ := σ) (src := src) (tgt := tgt) X).typed
  | succ n ih =>
    rw [pow_succ']
    rintro ⟨s, l⟩ ⟨l₁, l₂, rfl, hL, hM⟩
    exact wellTyped_append (L.typed _ hL) (ih _ hM)

/-- Kleene star is the existing fusion closure, which preserves endomorphism typing. -/
def closure (L : Language σ src tgt X X) : Language σ src tgt X X :=
  ⟨L.traces∗, fun t h ↦ by
    obtain ⟨n, hn⟩ := TraceLang.mem_kstar.mp h
    exact pow_typed L n t hn⟩

/-- Tests select single-state traces. -/
def test (X : I) (P : Set σ) : Language σ src tgt X X :=
  ⟨TraceLang.ofStates P, fun ⟨s, l⟩ h ↦ by
    obtain ⟨(rfl : l = []), _⟩ := h
    rfl⟩

/-- All one-action traces carrying a given action. -/
def action (a : α) : Language σ src tgt (src a) (tgt a) :=
  ⟨{t | ∃ s, t.2 = [(a, s)]}, fun ⟨s, l⟩ ⟨s', h⟩ ↦ by
    change l = [(a, s')] at h
    subst l
    exact ⟨rfl, rfl⟩⟩

/-- A particular one-action trace, with prescribed boundary states. -/
def step (s : σ) (a : α) (t : σ) : Language σ src tgt (src a) (tgt a) :=
  ⟨{(s, [(a, t)])}, fun _ h ↦ by subst h; exact ⟨rfl, rfl⟩⟩

end Language
end TypedTrace

/-- Objects of the trace-language category, indexed by arbitrary action endpoints. -/
structure TraceCat (σ : Type u) {α : Type v} {I : Type w} (src tgt : α → I) where
  obj : I

namespace TraceCat

variable {σ : Type u} {α : Type v} {I : Type w} {src tgt : α → I}
open TypedTrace

instance : Category (TraceCat σ src tgt) where
  Hom X Y := TypedTrace.Language σ src tgt X.obj Y.obj
  id X := TypedTrace.Language.ident X.obj
  comp := TypedTrace.Language.comp
  id_comp L := TypedTrace.Language.ext (one_mul L.traces)
  comp_id L := TypedTrace.Language.ext (mul_one L.traces)
  assoc L M N := TypedTrace.Language.ext (mul_assoc L.traces M.traces N.traces)

instance : KleeneCategory (TraceCat σ src tgt) where
  homSemilatticeSup X Y :=
    inferInstanceAs (SemilatticeSup (TypedTrace.Language σ src tgt X.obj Y.obj))
  homOrderBot X Y := inferInstanceAs (OrderBot (TypedTrace.Language σ src tgt X.obj Y.obj))
  sup_comp L M N := TypedTrace.Language.ext (add_mul L.traces M.traces N.traces)
  comp_sup L M N := TypedTrace.Language.ext (mul_add L.traces M.traces N.traces)
  bot_comp L := TypedTrace.Language.ext (zero_mul L.traces)
  comp_bot L := TypedTrace.Language.ext (mul_zero L.traces)
  kstar := TypedTrace.Language.closure
  id_le_kstar L := show (1 : TraceLang σ α) ≤ L.traces∗ from one_le_kstar
  comp_kstar_le_kstar L := show L.traces * L.traces∗ ≤ L.traces∗ from mul_kstar_le_kstar
  kstar_comp_le_kstar L := show L.traces∗ * L.traces ≤ L.traces∗ from kstar_mul_le_kstar
  comp_kstar_le_self L M h :=
    show M.traces * L.traces∗ ≤ M.traces from
      mul_kstar_le_self (show M.traces * L.traces ≤ M.traces from h)
  kstar_comp_le_self L M h :=
    show L.traces∗ * M.traces ≤ M.traces from
      kstar_mul_le_self (show L.traces * M.traces ≤ M.traces from h)

instance : BooleanKleeneCategory (TraceCat σ src tgt) where
  inf {X Y} := @Min.min (TypedTrace.Language σ src tgt X.obj Y.obj) _
  top {X Y} := (⊤ : TypedTrace.Language σ src tgt X.obj Y.obj)
  compl {X Y} := @Compl.compl (TypedTrace.Language σ src tgt X.obj Y.obj) _
  inf_le_left _ _ := Set.inter_subset_left
  inf_le_right _ _ := Set.inter_subset_right
  le_inf _ _ _ hf hg := Set.subset_inter hf hg
  le_sup_inf _ _ _ := by intro t h; rcases h with ⟨h | h, h' | h'⟩ <;> tauto
  le_top L := fun {_} h ↦ L.typed _ h
  inf_compl_le_bot _ := fun {_} h ↦ h.2.2 h.1
  top_le_sup_compl L := by
    intro t ht
    by_cases h : t ∈ L.traces
    · exact Or.inl h
    · exact Or.inr ⟨ht, h⟩

instance : TypedKAT (TraceCat σ src tgt) (fun _ ↦ Set σ) where
  test {X} := TypedTrace.Language.test X.obj
  test_bot := TypedTrace.Language.ext (KAT.test_bot (T := Set σ) (K := TraceLang σ α))
  test_top := TypedTrace.Language.ext (KAT.test_top (T := Set σ) (K := TraceLang σ α))
  test_sup P Q := TypedTrace.Language.ext (KAT.test_sup (K := TraceLang σ α) P Q)
  test_inf P Q := TypedTrace.Language.ext (KAT.test_inf (K := TraceLang σ α) P Q)

variable {X Y Z : TraceCat σ src tgt}

/-- Left residual: append this trace after every trace of `L`. -/
def ldiv (L : X ⟶ Y) (N : X ⟶ Z) : Y ⟶ Z :=
  TypedTrace.Language.restrict Y.obj Z.obj {t | ∀ u ∈ L.traces,
    u.last = t.1 → u.append t ∈ N.traces}

/-- Right residual: append every trace of `M` after this trace. -/
def rdiv (N : X ⟶ Z) (M : Y ⟶ Z) : X ⟶ Y :=
  TypedTrace.Language.restrict X.obj Y.obj {t | ∀ u ∈ M.traces,
    t.last = u.1 → t.append u ∈ N.traces}

instance : ResiduatedKleeneCategory (TraceCat σ src tgt) where
  ldiv := ldiv
  rdiv := rdiv
  ldiv_spec L M N := by
    constructor
    · intro h
      rintro ⟨s, l⟩ ⟨l₁, l₂, hl, hL, hM⟩
      change l = l₁ ++ l₂ at hl
      subst l
      exact (h hM).2 (s, l₁) hL rfl
    · intro h t ht
      exact ⟨M.typed t ht, fun u hu heq ↦ h (TraceLang.append_mem_mul hu ht heq)⟩
  rdiv_spec L M N := by
    constructor
    · intro h
      rintro ⟨s, l⟩ ⟨l₁, l₂, hl, hL, hM⟩
      change l = l₁ ++ l₂ at hl
      subst l
      exact (h hL).2 (Trace.lastOf s l₁, l₂) hM rfl
    · intro h t ht
      exact ⟨L.typed t ht, fun u hu heq ↦ h (TraceLang.append_mem_mul ht hu heq)⟩

@[simp] theorem traces_comp (L : X ⟶ Y) (M : Y ⟶ Z) :
    (L ≫ M).traces = L.traces * M.traces := rfl

@[simp] theorem traces_id : ((𝟙 X) : TypedTrace.Language σ src tgt X.obj X.obj).traces = 1 := rfl

@[simp] theorem traces_kstar (L : X ⟶ X) : (L∗).traces = L.traces∗ := rfl

@[simp] theorem traces_kplus (L : X ⟶ X) : (L⁺).traces = L.traces⁺ := rfl

@[simp] theorem traces_test (P : Set σ) :
    (TypedKAT.test (T := fun _ : TraceCat σ src tgt ↦ Set σ) P : X ⟶ X).traces =
      TraceLang.ofStates P := rfl

/-- Star membership is a finite sequence of fusible blocks of the original language. -/
theorem mem_kstar (L : X ⟶ X) (t : Trace σ α) :
    t ∈ (L∗).traces ↔ ∃ n : ℕ, t ∈ L.traces ^ n := TraceLang.mem_kstar

/-- The residual contains only traces of its own hom-set. -/
theorem mem_ldiv (L : X ⟶ Y) (N : X ⟶ Z) (t : Trace σ α) :
    t ∈ (L ⇘ N).traces ↔ WellTyped src tgt Y.obj Z.obj t ∧
      ∀ u ∈ L.traces, u.last = t.1 → u.append t ∈ N.traces := Iff.rfl

theorem mem_rdiv (N : X ⟶ Z) (M : Y ⟶ Z) (t : Trace σ α) :
    t ∈ (N ⇙ M).traces ↔ WellTyped src tgt X.obj Y.obj t ∧
      ∀ u ∈ M.traces, t.last = u.1 → t.append u ∈ N.traces := Iff.rfl

/-- An atom at an object specifies exactly one empty trace. -/
def atom (X : TraceCat σ src tgt) (s : σ) : X ⟶ X :=
  TypedTrace.Language.test X.obj {s}

/-- The action whose declared endpoints are `src a` and `tgt a`. -/
def action (a : α) : (⟨src a⟩ : TraceCat σ src tgt) ⟶ ⟨tgt a⟩ :=
  TypedTrace.Language.action a

/-- Prescribing the boundary states of an action selects a single trace. -/
theorem atom_action_atom (s t : σ) (a : α) :
    atom ⟨src a⟩ s ≫ action a ≫ atom ⟨tgt a⟩ t = TypedTrace.Language.step s a t := by
  rw [← Category.assoc]
  apply TypedTrace.Language.ext
  ext ⟨r, l⟩
  change (r, l) ∈ TraceLang.ofStates {s} *
    (TypedTrace.Language.action (src := src) (tgt := tgt) a).traces * TraceLang.ofStates {t} ↔
      (r, l) = (s, [(a, t)])
  constructor
  · rintro ⟨l₁, l₂, hl, ⟨la, lb, hl₁, ⟨hla, hrs⟩, b, hlb⟩, hl₂, hbt⟩
    change la = [] at hla
    change l₂ = [] at hl₂
    change r = s at hrs
    change lb = [(a, b)] at hlb
    subst la l₂ r lb
    simp only [List.nil_append] at hl₁
    subst l₁
    change b = t at hbt
    subst b
    simpa using hl
  · rintro ⟨⟩
    exact ⟨[(a, t)], [], rfl, ⟨[], [(a, t)], rfl, ⟨rfl, rfl⟩, t, rfl⟩, rfl, rfl⟩

end TraceCat

namespace TypedTrace.Language

variable {σ : Type u} {α : Type v} {I : Type w} {src tgt : α → I} {X Y Z : I}

@[gcongr] theorem restrict_mono {L M : TraceLang σ α} (h : L ≤ M) :
    restrict (src := src) (tgt := tgt) X Y L ≤ restrict X Y M := fun _ ht ↦ ⟨ht.1, h ht.2⟩

@[simp] theorem restrict_zero : restrict (σ := σ) (src := src) (tgt := tgt) X Y 0 = ⊥ := by
  apply ext
  ext t
  exact ⟨fun h ↦ h.2, False.elim⟩

@[simp] theorem restrict_one : restrict (σ := σ) (src := src) (tgt := tgt) X X 1 = ident X := by
  apply ext
  ext t
  exact ⟨And.right, fun h ↦ ⟨(ident X).typed t h, h⟩⟩

@[simp] theorem restrict_union (L M : TraceLang σ α) :
    restrict (src := src) (tgt := tgt) X Y (L ∪ M) = restrict X Y L ⊔ restrict X Y M := by
  apply ext
  ext t
  exact and_or_left

/-- Restriction commutes with composition when each input already has the specified type. -/
theorem restrict_comp (L M : TraceLang σ α)
    (hL : ∀ t ∈ L, WellTyped src tgt X Y t) (hM : ∀ t ∈ M, WellTyped src tgt Y Z t) :
    restrict (src := src) (tgt := tgt) X Z (L * M) = comp (restrict X Y L) (restrict Y Z M) := by
  have hrL : restrict X Y L = (⟨L, hL⟩ : Language σ src tgt X Y) := restrict_traces ⟨L, hL⟩
  have hrM : restrict Y Z M = (⟨M, hM⟩ : Language σ src tgt Y Z) := restrict_traces ⟨M, hM⟩
  rw [hrL, hrM]
  exact restrict_traces (comp ⟨L, hL⟩ ⟨M, hM⟩)

theorem restrict_kstar (L : TraceLang σ α) (h : ∀ t ∈ L, WellTyped src tgt X X t) :
    restrict (src := src) (tgt := tgt) X X L∗ = closure (restrict X X L) := by
  have hr : restrict X X L = (⟨L, h⟩ : Language σ src tgt X X) := restrict_traces ⟨L, h⟩
  rw [hr]
  exact restrict_traces (closure ⟨L, h⟩)

/-- With a single object, every trace is well typed and the old model is recovered. -/
def oneObjectOrderIso : Language σ (fun _ : α ↦ ()) (fun _ ↦ ()) () () ≃o TraceLang σ α where
  toFun := traces
  invFun L := ⟨L, fun t _ ↦ by
    unfold WellTyped
    generalize t.2.map Prod.fst = l
    induction l with
    | nil => rfl
    | cons a l ih => exact ⟨rfl, ih⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

end TypedTrace.Language
