import RelationAlgebra.Decide.GuardedString
import RelationAlgebra.Kleene.Complete

/-!
# Soundness of the guarded-string semantics

We interpret `KAT.BTerm`s in a Boolean algebra `T` and `KAT.KTerm`s in a Kleene algebra with
tests `K` over `T`, and prove that in a *complete* KAT the value of a term is the join of the
values of its guarded strings (`KAT.KTerm.eval_eq_sumGS`).  Consequently two terms with the
same guarded strings are equal (`KAT.KTerm.eval_eq_of_decideEq`), which is the soundness of the
`kat` tactic.

The key ingredients are the standard facts about *atoms* of the free Boolean algebra on `k`
generators: the atoms are pairwise disjoint (`KAT.atomAux_inf_atomAux_eq_bot`), their join is
`⊤` (`KAT.lsup_atomAux_eq_top`), and each Boolean term is the join of the atoms satisfying it
(`KAT.BTerm.eval_eq_lsup`).
-/

open scoped Computability KAT

namespace KAT

/-! ### Evaluation -/

/-- Evaluate a Boolean term in a Boolean algebra. -/
def BTerm.eval {T : Type*} [BooleanAlgebra T] (τ : ℕ → T) : BTerm → T
  | .top => ⊤
  | .bot => ⊥
  | .tvar i => τ i
  | .and a b => a.eval τ ⊓ b.eval τ
  | .or a b => a.eval τ ⊔ b.eval τ
  | .not a => (a.eval τ)ᶜ

/-- Evaluate a KAT term in a Kleene algebra with tests. -/
def KTerm.eval {T K : Type*} [BooleanAlgebra T] [KleeneAlgebra K] [KAT T K] (τ : ℕ → T)
    (ρ : ℕ → K) : KTerm → K
  | .zero => 0
  | .one => 1
  | .test b => ⌜b.eval τ⌝
  | .act p => ρ p
  | .add a b => a.eval τ ρ + b.eval τ ρ
  | .mul a b => a.eval τ ρ * b.eval τ ρ
  | .star a => (a.eval τ ρ)∗

/-- All test variables of a term are below `k`. -/
def KTerm.tvarsBelow (k : ℕ) (e : KTerm) : Bool := e.tvars.all (· < k)

/-! ### Finite joins over lists -/

section Lsup

variable {L : Type*} [SemilatticeSup L] [OrderBot L]

/-- The join of the values of a function on a list. -/
def lsup {ι : Type*} (f : ι → L) : List ι → L
  | [] => ⊥
  | x :: l => f x ⊔ lsup f l

@[simp] theorem lsup_nil {ι : Type*} (f : ι → L) : lsup f [] = ⊥ := rfl
@[simp] theorem lsup_cons {ι : Type*} (f : ι → L) (x : ι) (l : List ι) :
    lsup f (x :: l) = f x ⊔ lsup f l := rfl

theorem lsup_append {ι : Type*} (f : ι → L) (l₁ l₂ : List ι) :
    lsup f (l₁ ++ l₂) = lsup f l₁ ⊔ lsup f l₂ := by
  induction l₁ with
  | nil => simp
  | cons x l ih => simp [ih, sup_assoc]

theorem lsup_map {ι κ : Type*} (f : κ → L) (g : ι → κ) (l : List ι) :
    lsup f (l.map g) = lsup (f ∘ g) l := by
  induction l with
  | nil => rfl
  | cons _ l ih => simp [ih]

theorem lsup_congr {ι : Type*} {f g : ι → L} {l : List ι} (h : ∀ x ∈ l, f x = g x) :
    lsup f l = lsup g l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [lsup_cons, h x (List.mem_cons_self ..)]
    rw [ih fun y hy ↦ h y (List.mem_cons_of_mem _ hy)]

theorem lsup_inf_left {ι : Type*} {T : Type*} [DistribLattice T] [OrderBot T] (c : T) (f : ι → T)
    (l : List ι) : lsup (fun x ↦ c ⊓ f x) l = c ⊓ lsup f l := by
  induction l with
  | nil => simp
  | cons _ l ih => simp [ih, inf_sup_left]

theorem lsup_le_iff {ι : Type*} {f : ι → L} {l : List ι} {a : L} :
    lsup f l ≤ a ↔ ∀ x ∈ l, f x ≤ a := by
  induction l with
  | nil => simp
  | cons x l ih => simp [ih]

theorem le_lsup {ι : Type*} {f : ι → L} {l : List ι} {x : ι} (hx : x ∈ l) : f x ≤ lsup f l := by
  induction l with
  | nil => simp at hx
  | cons y l ih =>
    rcases List.mem_cons.1 hx with rfl | hx
    · exact le_sup_left
    · exact (ih hx).trans le_sup_right

end Lsup

theorem lsup_eq_iSup {K : Type*} [CompleteLattice K] {ι : Type*} (f : ι → K) (l : List ι) :
    lsup f l = ⨆ x ∈ l, f x :=
  le_antisymm (lsup_le_iff.2 fun x hx ↦ le_iSup₂_of_le x hx le_rfl)
    (iSup₂_le fun _ hx ↦ le_lsup hx)

/-! ### Atoms in a Boolean algebra -/

section Atoms

variable {T : Type*} [BooleanAlgebra T] (τ : ℕ → T)

/-- The element of `T` denoted by an atom, whose entries are assigned to the variables
`j, j + 1, …`. -/
def atomAux : ℕ → Atom → T
  | _, [] => ⊤
  | j, b :: α => (if b then τ j else (τ j)ᶜ) ⊓ atomAux (j + 1) α

/-- The element of `T` denoted by an atom. -/
def atomT (α : Atom) : T := atomAux τ 0 α

theorem atomAux_inf_tvar : ∀ (α : Atom) (j i : ℕ), i < α.length →
    atomAux τ j α ⊓ τ (j + i) = if α.getD i false then atomAux τ j α else ⊥
  | [], _, _, h => absurd h (Nat.not_lt_zero _)
  | b :: α, j, 0, _ => by
    change (if b = true then τ j else (τ j)ᶜ) ⊓ atomAux τ (j + 1) α ⊓ τ j =
      if b = true then (if b = true then τ j else (τ j)ᶜ) ⊓ atomAux τ (j + 1) α else ⊥
    cases b
    · rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, inf_right_comm,
        compl_inf_eq_bot, bot_inf_eq]
    · rw [if_pos rfl, if_pos rfl, inf_right_comm, inf_idem]
  | b :: α, j, i + 1, h => by
    rw [List.getD_cons_succ, atomAux, inf_assoc, show j + (i + 1) = (j + 1) + i by omega,
      atomAux_inf_tvar α (j + 1) i (by simpa using h)]
    by_cases hc : α.getD i false = true
    · rw [if_pos hc, if_pos hc]
    · rw [if_neg hc, if_neg hc, inf_bot_eq]

theorem atomAux_inf_eval : ∀ (b : BTerm) (α : Atom), (∀ i ∈ b.tvars, i < α.length) →
    atomAux τ 0 α ⊓ b.eval τ = if α.sat b then atomAux τ 0 α else ⊥
  | .top, α, _ => by simp [BTerm.eval, Atom.sat]
  | .bot, α, _ => by simp [BTerm.eval, Atom.sat]
  | .tvar i, α, h => by
    have := atomAux_inf_tvar τ α 0 i (h i (by simp [BTerm.tvars]))
    simpa [BTerm.eval, Atom.sat] using this
  | .and a b, α, h => by
    simp only [BTerm.tvars, List.mem_append] at h
    have ha := atomAux_inf_eval a α fun i hi ↦ h i (Or.inl hi)
    have hb := atomAux_inf_eval b α fun i hi ↦ h i (Or.inr hi)
    simp only [BTerm.eval, Atom.sat]
    rw [inf_inf_distrib_left, ha, hb]
    rcases Bool.eq_false_or_eq_true (α.sat a) with h1 | h1 <;>
      rcases Bool.eq_false_or_eq_true (α.sat b) with h2 | h2 <;> simp [h1, h2]
  | .or a b, α, h => by
    simp only [BTerm.tvars, List.mem_append] at h
    have ha := atomAux_inf_eval a α fun i hi ↦ h i (Or.inl hi)
    have hb := atomAux_inf_eval b α fun i hi ↦ h i (Or.inr hi)
    simp only [BTerm.eval, Atom.sat]
    rw [inf_sup_left, ha, hb]
    rcases Bool.eq_false_or_eq_true (α.sat a) with h1 | h1 <;>
      rcases Bool.eq_false_or_eq_true (α.sat b) with h2 | h2 <;> simp [h1, h2]
  | .not a, α, h => by
    have ha := atomAux_inf_eval a α h
    simp only [BTerm.eval, Atom.sat]
    by_cases hs : α.sat a = true
    · rw [if_pos hs] at ha
      rw [if_neg (by simp [hs]), ← ha, inf_assoc, inf_compl_eq_bot, inf_bot_eq]
    · rw [if_neg hs] at ha
      rw [if_pos (by simp [hs])]
      calc atomAux τ 0 α ⊓ (a.eval τ)ᶜ
          = atomAux τ 0 α ⊓ a.eval τ ⊔ atomAux τ 0 α ⊓ (a.eval τ)ᶜ := by rw [ha, bot_sup_eq]
        _ = atomAux τ 0 α ⊓ (a.eval τ ⊔ (a.eval τ)ᶜ) := (inf_sup_left _ _ _).symm
        _ = atomAux τ 0 α := by rw [sup_compl_eq_top, inf_top_eq]

theorem atomAux_inf_atomAux_eq_bot : ∀ (α β : Atom) (j : ℕ), α ≠ β → α.length = β.length →
    atomAux τ j α ⊓ atomAux τ j β = ⊥
  | [], [], _, h, _ => absurd rfl h
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | b :: α, b' :: β, j, h, hl => by
    simp only [atomAux]
    by_cases hb : b = b'
    · subst hb
      have hαβ : α ≠ β := fun h' ↦ h (h' ▸ rfl)
      rw [← inf_inf_distrib_left, atomAux_inf_atomAux_eq_bot α β (j + 1) hαβ (by simpa using hl),
        inf_bot_eq]
    · refine le_bot_iff.1 ((inf_le_inf inf_le_left inf_le_left).trans ?_)
      cases b <;> cases b' <;> simp_all

theorem lsup_atomAux_eq_top : ∀ (k j : ℕ), lsup (atomAux τ j) (allAtoms k) = ⊤
  | 0, _ => by simp [allAtoms, atomAux]
  | k + 1, j => by
    simp only [allAtoms, lsup_append, lsup_map]
    have h1 : lsup (atomAux τ j ∘ (true :: ·)) (allAtoms k) = τ j := by
      rw [show atomAux τ j ∘ (true :: ·) = fun α ↦ τ j ⊓ atomAux τ (j + 1) α from rfl,
        lsup_inf_left, lsup_atomAux_eq_top k (j + 1), inf_top_eq]
    have h2 : lsup (atomAux τ j ∘ (false :: ·)) (allAtoms k) = (τ j)ᶜ := by
      rw [show atomAux τ j ∘ (false :: ·) = fun α ↦ (τ j)ᶜ ⊓ atomAux τ (j + 1) α from rfl,
        lsup_inf_left, lsup_atomAux_eq_top k (j + 1), inf_top_eq]
    rw [h1, h2, sup_compl_eq_top]

theorem lsup_atomT_eq_top (k : ℕ) : lsup (atomT τ) (allAtoms k) = ⊤ := lsup_atomAux_eq_top τ k 0

/-- A Boolean term is the join of the atoms satisfying it. -/
theorem BTerm.eval_eq_lsup (k : ℕ) (b : BTerm) (h : ∀ i ∈ b.tvars, i < k) :
    b.eval τ = lsup (fun α ↦ if α.sat b then atomT τ α else ⊥) (allAtoms k) := by
  calc b.eval τ = b.eval τ ⊓ lsup (atomT τ) (allAtoms k) := by
        rw [lsup_atomT_eq_top, inf_top_eq]
    _ = lsup (fun α ↦ b.eval τ ⊓ atomT τ α) (allAtoms k) := (lsup_inf_left _ _ _).symm
    _ = lsup (fun α ↦ if α.sat b then atomT τ α else ⊥) (allAtoms k) := by
        refine lsup_congr fun α hα ↦ ?_
        rw [inf_comm]
        exact atomAux_inf_eval τ b α fun i hi ↦ (mem_allAtoms.1 hα).symm ▸ h i hi

end Atoms

/-! ### Values of guarded strings -/

section Values

variable {T K : Type*} [BooleanAlgebra T] [CompleteKleeneAlgebra K] [KAT T K]
  (τ : ℕ → T) (ρ : ℕ → K)

/-- Well-formedness of a guarded string for `k` test variables. -/
def GStr.wf (k : ℕ) (g : GStr) : Prop := g.1.length = k ∧ ∀ x ∈ g.2, x.2.length = k

theorem GStr.wf_last {k : ℕ} : ∀ (α : Atom) (l : List (ℕ × Atom)), GStr.wf k (α, l) →
    (GStr.last α l).length = k
  | _, [], h => h.1
  | _, (_, β) :: l, h => GStr.wf_last β l ⟨h.2 _ (List.mem_cons_self ..),
      fun x hx ↦ h.2 x (List.mem_cons_of_mem _ hx)⟩

theorem GStr.wf_fuse {k : ℕ} {X Y : Set GStr} (hX : ∀ g ∈ X, GStr.wf k g)
    (hY : ∀ g ∈ Y, GStr.wf k g) : ∀ g ∈ fuse X Y, GStr.wf k g := by
  rintro ⟨α, l⟩ h
  obtain ⟨l₁, l₂, rfl, h₁, h₂⟩ := mem_fuse.1 h
  refine ⟨(hX _ h₁).1, fun x hx ↦ ?_⟩
  rcases List.mem_append.1 hx with hx | hx
  · exact (hX _ h₁).2 x hx
  · exact (hY _ h₂).2 x hx

theorem GStr.wf_unitGS {k : ℕ} : ∀ g ∈ unitGS k, GStr.wf k g := by
  rintro ⟨α, l⟩ ⟨h1, h2⟩
  simp only at h1 h2
  subst h1
  exact ⟨mem_allAtoms.1 h2, by simp⟩

theorem GStr.wf_fusePow {k : ℕ} {X : Set GStr} (hX : ∀ g ∈ X, GStr.wf k g) :
    ∀ n, ∀ g ∈ fusePow k X n, GStr.wf k g
  | 0 => GStr.wf_unitGS
  | n + 1 => GStr.wf_fuse hX (GStr.wf_fusePow hX n)

theorem KTerm.wf_of_mem_gs {k : ℕ} : ∀ (e : KTerm), ∀ g ∈ e.gs k, GStr.wf k g
  | .zero, _, h => absurd h (Set.notMem_empty _)
  | .one, g, h => GStr.wf_unitGS g h
  | .test _, ⟨α, l⟩, h => by
    obtain ⟨rfl, hα, -⟩ := KTerm.mem_gs_test.1 h
    exact ⟨mem_allAtoms.1 hα, by simp⟩
  | .act _, ⟨α, l⟩, h => by
    obtain ⟨β, rfl, hα, hβ⟩ := KTerm.mem_gs_act.1 h
    exact ⟨mem_allAtoms.1 hα, by simp [mem_allAtoms.1 hβ]⟩
  | .add a b, g, h => by
    rcases h with h | h
    · exact KTerm.wf_of_mem_gs a g h
    · exact KTerm.wf_of_mem_gs b g h
  | .mul a b, g, h => GStr.wf_fuse (KTerm.wf_of_mem_gs a) (KTerm.wf_of_mem_gs b) g h
  | .star a, g, h => by
    obtain ⟨n, hn⟩ := KTerm.mem_gs_star.1 h
    exact GStr.wf_fusePow (KTerm.wf_of_mem_gs a) n g hn

/-- The value of a guarded string `α₀ p₁ α₁ ⋯` in `K`. -/
def gsVal : Atom → List (ℕ × Atom) → K
  | α, [] => ⌜atomT τ α⌝ * 1
  | α, (p, β) :: l => ⌜atomT τ α⌝ * (ρ p * gsVal β l)

/-- The value of a guarded string after its first atom. -/
def gsTail : List (ℕ × Atom) → K
  | [] => 1
  | (p, β) :: l => ρ p * gsVal τ ρ β l

theorem gsVal_eq (α : Atom) (l : List (ℕ × Atom)) :
    gsVal τ ρ α l = ⌜atomT τ α⌝ * gsTail τ ρ l := by
  cases l with
  | nil => rfl
  | cons x l => obtain ⟨p, β⟩ := x; rfl

/-- The value of a guarded string. -/
def GStr.val (g : GStr) : K := gsVal τ ρ g.1 g.2

/-- The join of the values of a set of guarded strings. -/
def sumGS (X : Set GStr) : K := ⨆ g ∈ X, GStr.val τ ρ g

theorem sumGS_mono {X Y : Set GStr} (h : X ⊆ Y) : sumGS τ ρ X ≤ sumGS τ ρ Y :=
  iSup₂_le fun g hg ↦ le_iSup₂_of_le g (h hg) le_rfl

theorem test_atomT_mul_test_atomT {k : ℕ} (α β : Atom) (hα : α.length = k) (hβ : β.length = k) :
    (⌜atomT τ α⌝ : K) * ⌜atomT τ β⌝ = if α = β then ⌜atomT τ α⌝ else 0 := by
  rw [← test_inf]
  split_ifs with h
  · subst h
    rw [inf_idem]
  · rw [atomT, atomT, atomAux_inf_atomAux_eq_bot τ α β 0 h (hα.trans hβ.symm), test_bot]

theorem gsVal_mul_gsVal {k : ℕ} : ∀ (α : Atom) (l : List (ℕ × Atom)) (β : Atom)
    (l' : List (ℕ × Atom)), (GStr.last α l).length = k → β.length = k →
    gsVal τ ρ α l * gsVal τ ρ β l' =
      if GStr.last α l = β then gsVal τ ρ α (l ++ l') else 0
  | α, [], β, l', hα, hβ => by
    simp only [GStr.last_nil, List.nil_append] at hα ⊢
    change ⌜atomT τ α⌝ * 1 * gsVal τ ρ β l' = _
    rw [mul_one, gsVal_eq τ ρ β l', ← mul_assoc, test_atomT_mul_test_atomT τ (k := k) α β hα hβ,
      gsVal_eq τ ρ α l']
    split_ifs
    · rfl
    · rw [zero_mul]
  | α, (p, γ) :: l, β, l', hα, hβ => by
    simp only [GStr.last_cons, List.cons_append] at hα ⊢
    simp only [gsVal]
    rw [mul_assoc, mul_assoc, gsVal_mul_gsVal γ l β l' hα hβ]
    split_ifs <;> simp

theorem sumGS_union (X Y : Set GStr) : sumGS τ ρ (X ∪ Y) = sumGS τ ρ X + sumGS τ ρ Y := by
  rw [add_eq_sup]
  exact iSup_union

theorem sumGS_iUnion (P : ℕ → Set GStr) : sumGS τ ρ (⋃ n, P n) = ⨆ n, sumGS τ ρ (P n) := by
  apply le_antisymm
  · refine iSup₂_le fun g hg ↦ ?_
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hg
    exact le_iSup_of_le n (le_iSup₂_of_le g hn le_rfl)
  · exact iSup_le fun n ↦ iSup₂_le fun g hg ↦ le_iSup₂_of_le g (Set.mem_iUnion.2 ⟨n, hg⟩) le_rfl

theorem sumGS_fuse {k : ℕ} {X Y : Set GStr} (hX : ∀ g ∈ X, GStr.wf k g)
    (hY : ∀ g ∈ Y, GStr.wf k g) : sumGS τ ρ (fuse X Y) = sumGS τ ρ X * sumGS τ ρ Y := by
  apply le_antisymm
  · refine iSup₂_le fun g hg ↦ ?_
    obtain ⟨α, l₁, l₂, rfl, h₁, h₂⟩ := hg
    have hl := GStr.wf_last α l₁ (hX _ h₁)
    have : GStr.val τ ρ (α, l₁ ++ l₂) =
        GStr.val τ ρ (α, l₁) * GStr.val τ ρ (GStr.last α l₁, l₂) := by
      simp only [GStr.val]
      rw [gsVal_mul_gsVal τ ρ (k := k) α l₁ _ l₂ hl hl, if_pos rfl]
    rw [this]
    exact mul_le_mul' (le_iSup₂_of_le _ h₁ le_rfl) (le_iSup₂_of_le _ h₂ le_rfl)
  · unfold sumGS
    rw [CompleteKleeneAlgebra.iSup_mul]
    refine iSup_le fun g ↦ ?_
    rw [CompleteKleeneAlgebra.iSup_mul]
    refine iSup_le fun hg ↦ ?_
    rw [CompleteKleeneAlgebra.mul_iSup]
    refine iSup_le fun g' ↦ ?_
    rw [CompleteKleeneAlgebra.mul_iSup]
    refine iSup_le fun hg' ↦ ?_
    obtain ⟨α, l⟩ := g
    obtain ⟨β, l'⟩ := g'
    simp only [GStr.val]
    rw [gsVal_mul_gsVal τ ρ (k := k) α l β l' (GStr.wf_last α l (hX _ hg)) (hY _ hg').1]
    split_ifs with h
    · refine le_iSup₂_of_le (α, l ++ l') (mem_fuse.2 ⟨l, l', rfl, hg, ?_⟩) le_rfl
      rw [h]
      exact hg'
    · exact zero_le

theorem test_lsup {ι : Type*} (f : ι → T) (l : List ι) :
    (⌜lsup f l⌝ : K) = lsup (fun x ↦ ⌜f x⌝) l := by
  induction l with
  | nil => simp [test_bot, CompleteKleeneAlgebra.bot_eq_zero]
  | cons x l ih => simp [test_sup, ih, add_eq_sup]

theorem one_eq_iSup_atoms (k : ℕ) : (1 : K) = ⨆ α ∈ allAtoms k, (⌜atomT τ α⌝ : K) := by
  rw [← lsup_eq_iSup, ← test_lsup, lsup_atomT_eq_top, test_top]

theorem sumGS_unitGS (k : ℕ) : sumGS τ ρ (unitGS k) = 1 := by
  rw [one_eq_iSup_atoms τ k]
  apply le_antisymm
  · refine iSup₂_le fun g hg ↦ ?_
    obtain ⟨α, l⟩ := g
    obtain ⟨h1, h2⟩ := hg
    simp only at h1 h2
    subst h1
    exact le_iSup₂_of_le α h2 (by simp [GStr.val, gsVal])
  · exact iSup₂_le fun α hα ↦ le_iSup₂_of_le (α, []) ⟨rfl, hα⟩ (by simp [GStr.val, gsVal])

theorem sumGS_fusePow {k : ℕ} {X : Set GStr} (hX : ∀ g ∈ X, GStr.wf k g) :
    ∀ n, sumGS τ ρ (fusePow k X n) = sumGS τ ρ X ^ n
  | 0 => by
    rw [pow_zero]
    exact sumGS_unitGS τ ρ k
  | n + 1 => by
    change sumGS τ ρ (fuse X (fusePow k X n)) = _
    rw [pow_succ', sumGS_fuse τ ρ hX (GStr.wf_fusePow hX n), sumGS_fusePow hX n]

theorem sumGS_gs_test (k : ℕ) (b : BTerm) (h : ∀ i ∈ b.tvars, i < k) :
    sumGS τ ρ ((KTerm.test b).gs k) = ⌜b.eval τ⌝ := by
  rw [BTerm.eval_eq_lsup τ k b h, test_lsup, lsup_eq_iSup]
  apply le_antisymm
  · refine iSup₂_le fun g hg ↦ ?_
    obtain ⟨α, l⟩ := g
    obtain ⟨rfl, hα, hs⟩ := KTerm.mem_gs_test.1 hg
    exact le_iSup₂_of_le α hα (by simp [GStr.val, gsVal, hs])
  · refine iSup₂_le fun α hα ↦ ?_
    split_ifs with hs
    · exact le_iSup₂_of_le (α, []) (KTerm.mem_gs_test.2 ⟨rfl, hα, hs⟩)
        (by simp [GStr.val, gsVal])
    · rw [test_bot]
      exact zero_le

theorem sumGS_gs_act (k : ℕ) (p : ℕ) : sumGS τ ρ ((KTerm.act p).gs k) = ρ p := by
  apply le_antisymm
  · refine iSup₂_le fun g hg ↦ ?_
    obtain ⟨α, l⟩ := g
    obtain ⟨β, rfl, -, -⟩ := KTerm.mem_gs_act.1 hg
    simp only [GStr.val, gsVal]
    calc ⌜atomT τ α⌝ * (ρ p * (⌜atomT τ β⌝ * 1)) ≤ 1 * (ρ p * (1 * 1)) :=
          mul_le_mul' test_le_one (mul_le_mul' le_rfl (mul_le_mul' test_le_one le_rfl))
      _ = ρ p := by simp
  · calc ρ p = (⨆ α ∈ allAtoms k, (⌜atomT τ α⌝ : K)) *
          (ρ p * ⨆ β ∈ allAtoms k, (⌜atomT τ β⌝ : K)) := by
          rw [← one_eq_iSup_atoms, one_mul, mul_one]
      _ ≤ sumGS τ ρ ((KTerm.act p).gs k) := by
          rw [CompleteKleeneAlgebra.iSup_mul]
          refine iSup_le fun α ↦ ?_
          rw [CompleteKleeneAlgebra.iSup_mul]
          refine iSup_le fun hα ↦ ?_
          rw [CompleteKleeneAlgebra.mul_iSup, CompleteKleeneAlgebra.mul_iSup]
          refine iSup_le fun β ↦ ?_
          rw [CompleteKleeneAlgebra.mul_iSup, CompleteKleeneAlgebra.mul_iSup]
          refine iSup_le fun hβ ↦ ?_
          exact le_iSup₂_of_le (α, [(p, β)]) (KTerm.mem_gs_act.2 ⟨β, rfl, hα, hβ⟩)
            (by simp [GStr.val, gsVal])

/-- **The value of a term is the join of the values of its guarded strings.** -/
theorem KTerm.eval_eq_sumGS (k : ℕ) : ∀ e : KTerm, (∀ i ∈ e.tvars, i < k) →
    e.eval τ ρ = sumGS τ ρ (e.gs k)
  | .zero, _ => by simp [KTerm.eval, KTerm.gs, sumGS, CompleteKleeneAlgebra.bot_eq_zero, iSup_const]
  | .one, _ => (sumGS_unitGS τ ρ k).symm
  | .test b, h => (sumGS_gs_test τ ρ k b h).symm
  | .act p, _ => (sumGS_gs_act τ ρ k p).symm
  | .add a b, h => by
    simp only [KTerm.tvars, List.mem_append] at h
    simp only [KTerm.eval, KTerm.gs]
    rw [KTerm.eval_eq_sumGS k a (fun i hi ↦ h i (Or.inl hi)),
      KTerm.eval_eq_sumGS k b (fun i hi ↦ h i (Or.inr hi)), sumGS_union]
  | .mul a b, h => by
    simp only [KTerm.tvars, List.mem_append] at h
    simp only [KTerm.eval, KTerm.gs]
    rw [KTerm.eval_eq_sumGS k a (fun i hi ↦ h i (Or.inl hi)),
      KTerm.eval_eq_sumGS k b (fun i hi ↦ h i (Or.inr hi)),
      sumGS_fuse τ ρ (KTerm.wf_of_mem_gs a) (KTerm.wf_of_mem_gs b)]
  | .star a, h => by
    simp only [KTerm.eval, KTerm.gs]
    rw [KTerm.eval_eq_sumGS k a h, sumGS_iUnion, CompleteKleeneAlgebra.kstar_eq_iSup_pow]
    exact iSup_congr fun n ↦ (sumGS_fusePow τ ρ (KTerm.wf_of_mem_gs a) n).symm

theorem KTerm.tvars_lt_of_tvarsBelow {k : ℕ} {e : KTerm} (h : e.tvarsBelow k = true) :
    ∀ i ∈ e.tvars, i < k := by
  simpa [KTerm.tvarsBelow, List.all_eq_true] using h

/-- **Soundness of the `kat` decision procedure.** -/
theorem KTerm.eval_eq_of_decideEq {k : ℕ} {e f : KTerm} {fuel : ℕ} (he : e.tvarsBelow k = true)
    (hf : f.tvarsBelow k = true) (h : KTerm.decideEq k e f fuel = true) :
    e.eval τ ρ = f.eval τ ρ := by
  rw [KTerm.eval_eq_sumGS τ ρ k e (KTerm.tvars_lt_of_tvarsBelow he),
    KTerm.eval_eq_sumGS τ ρ k f (KTerm.tvars_lt_of_tvarsBelow hf), KTerm.gs_eq_of_decideEq h]

theorem KTerm.eval_le_of_decideLe {k : ℕ} {e f : KTerm} {fuel : ℕ} (he : e.tvarsBelow k = true)
    (hf : f.tvarsBelow k = true) (h : KTerm.decideLe k e f fuel = true) :
    e.eval τ ρ ≤ f.eval τ ρ := by
  rw [KTerm.eval_eq_sumGS τ ρ k e (KTerm.tvars_lt_of_tvarsBelow he),
    KTerm.eval_eq_sumGS τ ρ k f (KTerm.tvars_lt_of_tvarsBelow hf)]
  exact sumGS_mono τ ρ (KTerm.gs_le_of_decideLe h)

end Values

end KAT
