import RelationAlgebra.Decide.Term

/-!
# Deciding language equivalence with Antimirov derivatives

This file implements a decision procedure for the equivalence of regular expressions
(`KleeneAlgebra.Term`), following Antimirov's *partial derivatives* and the bisimulation-based
algorithm used by Pous' `relation-algebra` library and by Krauss–Nipkow.

* `Term.nullable e` decides whether `[] ∈ lang e`;
* `Term.deriv x e` is the list of partial derivatives of `e` by the letter `x`, so that
  `x :: w ∈ lang e ↔ ∃ t ∈ deriv x e, w ∈ lang t` (`Term.cons_mem_lang_iff`);
* a state of the algorithm is a *set* of terms, represented as a list, with language the union
  of the languages of its elements (`Term.langs`);
* a pair of states `(S, T)` has equal languages as soon as it belongs to a *bisimulation*
  (`Term.isBisim`): a finite set of pairs closed under derivatives (up to set-equality of the
  lists) and agreeing on nullability (`Term.langs_eq_of_isBisim`);
* `Term.explore` searches for such a bisimulation by a worklist exploration with fuel, and
  `Term.decideEq` checks the result with `isBisim`.  Only the checker needs to be verified
  (`Term.lang_eq_of_decideEq`); termination is guaranteed in practice because the set of
  partial derivatives of a term is finite.
-/

open scoped Computability

namespace KleeneAlgebra.Term

/-! ### Nullability and partial derivatives -/

/-- Does the language of the term contain the empty word? -/
def nullable : Term → Bool
  | zero => false
  | one => true
  | var _ => false
  | add a b => nullable a || nullable b
  | mul a b => nullable a && nullable b
  | star _ => true

/-- Antimirov's partial derivatives of a term by a letter. -/
def deriv (x : ℕ) : Term → List Term
  | zero => []
  | one => []
  | var i => if i = x then [one] else []
  | add a b => deriv x a ++ deriv x b
  | mul a b => (deriv x a).map (fun t ↦ mul t b) ++ (if nullable a then deriv x b else [])
  | star a => (deriv x a).map (fun t ↦ mul t (star a))

/-- The variables occurring in a term. -/
def vars : Term → List ℕ
  | zero => []
  | one => []
  | var i => [i]
  | add a b => vars a ++ vars b
  | mul a b => vars a ++ vars b
  | star a => vars a

theorem nil_mem_lang_iff : ∀ e : Term, [] ∈ lang e ↔ nullable e = true
  | zero => by simp [nullable]
  | one => by simp [Language.mem_one, nullable]
  | var i => by simp [mem_singleton_lang, nullable]
  | add a b => by
    simp only [lang_add, Language.mem_add, nullable, Bool.or_eq_true]
    rw [nil_mem_lang_iff a, nil_mem_lang_iff b]
  | mul a b => by
    simp only [lang_mul, Language.mem_mul, nullable, Bool.and_eq_true]
    rw [← nil_mem_lang_iff a, ← nil_mem_lang_iff b]
    constructor
    · rintro ⟨u, hu, v, hv, huv⟩
      obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 huv
      exact ⟨hu, hv⟩
    · rintro ⟨ha, hb⟩
      exact ⟨[], ha, [], hb, rfl⟩
  | star a => by simp [Language.nil_mem_kstar, nullable]

theorem cons_mem_lang_iff (x : ℕ) : ∀ (e : Term) (w : List ℕ),
    x :: w ∈ lang e ↔ ∃ t ∈ deriv x e, w ∈ lang t
  | zero, w => by simp [deriv]
  | one, w => by simp [Language.mem_one, deriv]
  | var i, w => by
    rw [lang_var, mem_singleton_lang]
    simp only [deriv]
    constructor
    · intro h
      obtain ⟨rfl, rfl⟩ := List.cons_eq_cons.1 h
      exact ⟨one, by simp, rfl⟩
    · rintro ⟨t, ht, hw⟩
      split_ifs at ht with h
      · subst h
        simp only [List.mem_singleton] at ht
        subst ht
        rw [lang_one, Language.mem_one] at hw
        subst hw
        rfl
      · simp at ht
  | add a b, w => by
    simp only [lang_add, Language.mem_add, deriv, List.mem_append, cons_mem_lang_iff x a w,
      cons_mem_lang_iff x b w]
    constructor
    · rintro (⟨t, ht, hw⟩ | ⟨t, ht, hw⟩)
      · exact ⟨t, Or.inl ht, hw⟩
      · exact ⟨t, Or.inr ht, hw⟩
    · rintro ⟨t, ht | ht, hw⟩
      · exact Or.inl ⟨t, ht, hw⟩
      · exact Or.inr ⟨t, ht, hw⟩
  | mul a b, w => by
    simp only [lang_mul, deriv, List.mem_append, List.mem_map]
    constructor
    · intro h
      obtain ⟨u, hu, v, hv, huv⟩ := Language.mem_mul.1 h
      cases u with
      | nil =>
        have ha : nullable a = true := (nil_mem_lang_iff a).1 hu
        obtain ⟨t, ht, hw⟩ := (cons_mem_lang_iff x b w).1 (by simpa using huv ▸ hv)
        exact ⟨t, Or.inr (by simpa [ha] using ht), hw⟩
      | cons y u' =>
        simp only [List.cons_append] at huv
        obtain ⟨rfl, rfl⟩ := List.cons_eq_cons.1 huv.symm
        obtain ⟨t, ht, hu'⟩ := (cons_mem_lang_iff x a u').1 hu
        exact ⟨mul t b, Or.inl ⟨t, ht, rfl⟩, Language.mem_mul.2 ⟨u', hu', v, hv, rfl⟩⟩
    · rintro ⟨t, ht | ht, hw⟩
      · obtain ⟨t', ht', rfl⟩ := ht
        obtain ⟨u', hu', v, hv, rfl⟩ := Language.mem_mul.1 hw
        exact Language.mem_mul.2
          ⟨x :: u', (cons_mem_lang_iff x a u').2 ⟨t', ht', hu'⟩, v, hv, rfl⟩
      · by_cases ha : nullable a = true
        · simp only [ha, if_true] at ht
          exact Language.mem_mul.2
            ⟨[], (nil_mem_lang_iff a).2 ha, x :: w, (cons_mem_lang_iff x b w).2 ⟨t, ht, hw⟩, rfl⟩
        · simp [ha] at ht
  | star a, w => by
    simp only [lang_star, deriv, List.mem_map]
    constructor
    · intro h
      obtain ⟨S, hS, hmem⟩ := Language.mem_kstar_iff_exists_nonempty.1 h
      cases S with
      | nil => simp at hS
      | cons y S' =>
        obtain ⟨hy, hyne⟩ := hmem y (List.mem_cons_self ..)
        cases y with
        | nil => exact absurd rfl hyne
        | cons z u' =>
          simp only [List.flatten_cons, List.cons_append] at hS
          obtain ⟨rfl, rfl⟩ := List.cons_eq_cons.1 hS
          obtain ⟨t, ht, hu'⟩ := (cons_mem_lang_iff x a u').1 hy
          refine ⟨mul t (star a), ⟨t, ht, rfl⟩, ?_⟩
          exact Language.mem_mul.2 ⟨u', hu', S'.flatten,
            Language.join_mem_kstar fun y hy ↦ (hmem y (List.mem_cons_of_mem _ hy)).1, rfl⟩
    · rintro ⟨t, ⟨t', ht', rfl⟩, hw⟩
      obtain ⟨u', hu', v, hv, rfl⟩ := Language.mem_mul.1 hw
      have h1 : (x :: u') ++ v ∈ lang a * (lang a)∗ :=
        Language.mem_mul.2 ⟨x :: u', (cons_mem_lang_iff x a u').2 ⟨t', ht', hu'⟩, v, hv, rfl⟩
      have h2 : lang a * (lang a)∗ ≤ (lang a)∗ := mul_kstar_le_kstar
      exact h2 h1

theorem deriv_eq_nil_of_not_mem_vars (x : ℕ) : ∀ e : Term, x ∉ vars e → deriv x e = []
  | zero, _ => rfl
  | one, _ => rfl
  | var i, h => by
    simp only [vars, List.mem_singleton] at h
    simp [deriv, Ne.symm h]
  | add a b, h => by
    simp only [vars, List.mem_append, not_or] at h
    simp [deriv, deriv_eq_nil_of_not_mem_vars x a h.1, deriv_eq_nil_of_not_mem_vars x b h.2]
  | mul a b, h => by
    simp only [vars, List.mem_append, not_or] at h
    simp [deriv, deriv_eq_nil_of_not_mem_vars x a h.1, deriv_eq_nil_of_not_mem_vars x b h.2]
  | star a, h => by
    simp [deriv, deriv_eq_nil_of_not_mem_vars x a h]

/-! ### Sets of terms -/

/-- The language of a set (list) of terms: the union of their languages. -/
def langs (S : List Term) : Language ℕ := {w | ∃ t ∈ S, w ∈ lang t}

theorem mem_langs {S : List Term} {w : List ℕ} : w ∈ langs S ↔ ∃ t ∈ S, w ∈ lang t := Iff.rfl

@[simp] theorem langs_singleton (t : Term) : langs [t] = lang t := by
  ext w; simp [mem_langs]

/-- Nullability of a set of terms. -/
def nullableS (S : List Term) : Bool := S.any nullable

/-- Partial derivative of a set of terms. -/
def derivS (x : ℕ) (S : List Term) : List Term := S.flatMap (deriv x)

/-- The variables occurring in a set of terms. -/
def varsS (S : List Term) : List ℕ := S.flatMap vars

theorem nil_mem_langs_iff (S : List Term) : [] ∈ langs S ↔ nullableS S = true := by
  simp [mem_langs, nullableS, List.any_eq_true, nil_mem_lang_iff]

theorem cons_mem_langs_iff (x : ℕ) (S : List Term) (w : List ℕ) :
    x :: w ∈ langs S ↔ w ∈ langs (derivS x S) := by
  simp only [mem_langs, derivS, List.mem_flatMap, cons_mem_lang_iff]
  constructor
  · rintro ⟨t, ht, t', ht', hw⟩
    exact ⟨t', ⟨t, ht, ht'⟩, hw⟩
  · rintro ⟨t', ⟨t, ht, ht'⟩, hw⟩
    exact ⟨t, ht, t', ht', hw⟩

theorem derivS_eq_nil_of_not_mem_varsS (x : ℕ) (S : List Term) (h : x ∉ varsS S) :
    derivS x S = [] := by
  simp only [varsS, List.mem_flatMap, not_exists, not_and] at h
  simp only [derivS, List.flatMap_eq_nil_iff]
  exact fun t ht ↦ deriv_eq_nil_of_not_mem_vars x t (h t ht)

/-- Set-equality of two lists. -/
def setEq (S T : List Term) : Bool := S.all (· ∈ T) && T.all (· ∈ S)

theorem langs_eq_of_setEq {S T : List Term} (h : setEq S T = true) : langs S = langs T := by
  simp only [setEq, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  ext w
  simp only [mem_langs]
  exact ⟨fun ⟨t, ht, hw⟩ ↦ ⟨t, h.1 t ht, hw⟩, fun ⟨t, ht, hw⟩ ↦ ⟨t, h.2 t ht, hw⟩⟩

/-! ### Bisimulations -/

/-- A pair of states of the algorithm. -/
abbrev Pair := List Term × List Term

/-- Membership of a pair in a relation, up to set-equality of the components. -/
def memUpTo (p : Pair) (R : List Pair) : Bool :=
  R.any fun q ↦ setEq p.1 q.1 && setEq p.2 q.2

/-- Check that a list of pairs is a bisimulation up to set-equality: related states agree on
nullability, and their derivatives by every letter are again related. -/
def isBisim (R : List Pair) : Bool :=
  R.all fun p ↦ (nullableS p.1 == nullableS p.2) &&
    (varsS p.1 ++ varsS p.2).all fun x ↦ memUpTo (derivS x p.1, derivS x p.2) R

theorem langs_eq_of_memUpTo_aux {R : List Pair} (hR : isBisim R = true) :
    ∀ (w : List ℕ) (p : Pair), p ∈ R → (w ∈ langs p.1 ↔ w ∈ langs p.2) := by
  intro w
  induction w with
  | nil =>
    intro p hp
    simp only [isBisim, List.all_eq_true, Bool.and_eq_true, beq_iff_eq] at hR
    rw [nil_mem_langs_iff, nil_mem_langs_iff, (hR p hp).1]
  | cons x w ih =>
    intro p hp
    rw [cons_mem_langs_iff, cons_mem_langs_iff]
    by_cases hx : x ∈ varsS p.1 ++ varsS p.2
    · have hR' := hR
      simp only [isBisim, List.all_eq_true, Bool.and_eq_true, beq_iff_eq] at hR'
      have hmem := (hR' p hp).2 x hx
      simp only [memUpTo, List.any_eq_true, Bool.and_eq_true] at hmem
      obtain ⟨q, hq, h₁, h₂⟩ := hmem
      rw [langs_eq_of_setEq h₁, langs_eq_of_setEq h₂]
      exact ih q hq
    · simp only [List.mem_append, not_or] at hx
      rw [derivS_eq_nil_of_not_mem_varsS x _ hx.1, derivS_eq_nil_of_not_mem_varsS x _ hx.2]

/-- States related by a bisimulation have the same language. -/
theorem langs_eq_of_isBisim {R : List Pair} (hR : isBisim R = true) {S T : List Term}
    (h : memUpTo (S, T) R = true) : langs S = langs T := by
  simp only [memUpTo, List.any_eq_true, Bool.and_eq_true] at h
  obtain ⟨q, hq, h₁, h₂⟩ := h
  rw [langs_eq_of_setEq h₁, langs_eq_of_setEq h₂]
  ext w
  exact langs_eq_of_memUpTo_aux hR w q hq

/-! ### The decision procedure -/

/-- Worklist exploration of the pairs reachable from the initial ones by derivatives.  Returns
the visited pairs when the worklist is exhausted, or `none` when running out of fuel. -/
def explore : ℕ → List Pair → List Pair → Option (List Pair)
  | 0, _, _ => none
  | _ + 1, visited, [] => some visited
  | fuel + 1, visited, p :: todo =>
    if memUpTo p visited then explore fuel visited todo
    else
      let next := (varsS p.1 ++ varsS p.2).map fun x ↦ (derivS x p.1, derivS x p.2)
      explore fuel (p :: visited) (next ++ todo)

/-- Decide whether two terms have the same language: explore, then check the certificate. -/
def decideEq (e f : Term) (fuel : ℕ := 1000) : Bool :=
  match explore fuel [] [([e], [f])] with
  | some R => isBisim R && memUpTo ([e], [f]) R
  | none => false

/-- Decide whether the language of `e` is included in that of `f`. -/
def decideLe (e f : Term) (fuel : ℕ := 1000) : Bool := decideEq (add e f) f fuel

/-- **Soundness of the decision procedure.** -/
theorem lang_eq_of_decideEq {e f : Term} {fuel : ℕ} (h : decideEq e f fuel = true) :
    lang e = lang f := by
  unfold decideEq at h
  split at h
  · rw [Bool.and_eq_true] at h
    simpa using langs_eq_of_isBisim h.1 h.2
  · exact absurd h Bool.false_ne_true

theorem lang_le_of_decideLe {e f : Term} {fuel : ℕ} (h : decideLe e f fuel = true) :
    lang e ≤ lang f := by
  have := lang_eq_of_decideEq h
  rw [lang_add] at this
  exact add_eq_right_iff_le.1 this

/-- **Soundness for complete Kleene algebras.** -/
theorem eval_eq_of_decideEq {K : Type*} [CompleteKleeneAlgebra K] {e f : Term} {fuel : ℕ}
    (h : decideEq e f fuel = true) (ρ : ℕ → K) : eval ρ e = eval ρ f :=
  eval_eq_of_lang_eq ρ (lang_eq_of_decideEq h)

theorem eval_le_of_decideLe {K : Type*} [CompleteKleeneAlgebra K] {e f : Term} {fuel : ℕ}
    (h : decideLe e f fuel = true) (ρ : ℕ → K) : eval ρ e ≤ eval ρ f :=
  eval_le_of_lang_le ρ (lang_le_of_decideLe h)

/-- Sliding, checked by the decision procedure. -/
example :
    decideEq (mul (var 0) (star (mul (var 1) (var 0))))
      (mul (star (mul (var 0) (var 1))) (var 0)) = true := by
  decide +kernel

end KleeneAlgebra.Term
