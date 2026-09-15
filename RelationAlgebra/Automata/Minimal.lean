import RelationAlgebra.Automata.Lang

/-!
# Deterministic automata with the same language have the same value

This file completes the automata-theoretic half of Kozen's completeness proof.

* `value_eq_of_hom` : a homomorphism of deterministic automata preserves the value, in every
  Kleene algebra.  It is the rectangular bisimulation rule of `RelationAlgebra.Automata.Defs`
  applied to the zero-one graph of the homomorphism.
* `value_eq_of_langOf_eq` : **two deterministic automata accepting the same language denote the
  same element of every Kleene algebra.**  Both are mapped homomorphically onto a common
  automaton obtained by choosing, in the disjoint union of the two state sets, a canonical
  representative of each language-equivalence class; the two initial states are sent to the same
  representative exactly because the accepted languages agree.

No completeness or star-continuity assumption is made on the Kleene algebra anywhere.

## References

* [D. Kozen, *A completeness theorem for Kleene algebras and the algebra of regular events*,
  Information and Computation 110(2):366-390, 1994][kozen1994]
* Damien Pous, `relation-algebra`, `theories/ka_completeness.v`.
-/

open scoped Computability

namespace RelationAlgebra.Automata

/-! ### Homomorphisms of deterministic automata -/

section Hom

variable {K : Type*} [KleeneAlgebra K] {n q : Type*} [Fintype n] [DecidableEq n]
  [Fintype q] [DecidableEq q]

/-- A homomorphism of deterministic automata preserves the denoted element of every Kleene
algebra. -/
theorem value_eq_of_hom {A : EpsNFA n} {B : EpsNFA q} {init : n} {nxt : ℕ → n → n}
    {initB : q} {nxtB : ℕ → q → q} (Γ : Finset ℕ) (ρ : ℕ → K)
    (hA : A.IsDet init nxt) (hB : B.IsDet initB nxtB) (h : n → q)
    (hinit : h init = initB)
    (hstep : ∀ a ∈ Γ, ∀ i, h (nxt a i) = nxtB a (h i))
    (hacc : ∀ i, B.accept (h i) ↔ A.accept i) :
    B.value Γ ρ = A.value Γ ρ := by
  classical
  set X : Matrix n q K := Matrix.ofRel K fun i c => h i = c with hX
  refine value_eq_of_sim (A := B) (B := A) X ?_ ?_ ?_
  · -- `A.startVec * X = B.startVec`
    rw [EpsNFA.startVec, EpsNFA.startVec, hX, Matrix.ofRel_comp]
    refine Matrix.ofRel_congr fun _ c ↦ ?_
    constructor
    · rintro ⟨i, hi, rfl⟩
      rw [hB.start_iff, ← hinit, (hA.start_iff i).1 hi]
    · intro hc
      exact ⟨init, (hA.start_iff init).2 rfl, by rw [hinit, ← (hB.start_iff c).1 hc]⟩
  · -- `X * B.transMat = A.transMat * X`
    rw [EpsNFA.transMat_of_epsFree hA.epsFree, EpsNFA.transMat_of_epsFree hB.epsFree,
      EpsNFA.letterMat, EpsNFA.letterMat, Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun a ha ↦ ?_
    rw [hX, Matrix.ofRel_mul_ofRelLab, Matrix.ofRelLab_mul_ofRel]
    refine Matrix.ofRelLab_congr fun i d ↦ ?_
    constructor
    · rintro ⟨c, rfl, hstepB⟩
      exact ⟨nxt a i, (hA.step_iff a i _).2 rfl, by
        rw [hstep a ha i, ← (hB.step_iff a (h i) d).1 hstepB]⟩
    · rintro ⟨j, hstepA, rfl⟩
      refine ⟨h i, rfl, ?_⟩
      rw [hB.step_iff, ← hstep a ha i, (hA.step_iff a i j).1 hstepA]
  · -- `X * B.acceptVec = A.acceptVec`
    rw [EpsNFA.acceptVec, EpsNFA.acceptVec, hX, Matrix.ofRel_comp]
    refine Matrix.ofRel_congr fun i _ ↦ ?_
    constructor
    · rintro ⟨c, rfl, hc⟩
      exact (hacc i).1 hc
    · intro hi
      exact ⟨h i, rfl, (hacc i).2 hi⟩

end Hom

/-! ### Canonical representatives of language classes -/

section Rep

variable {m : Type*} [Fintype m] [DecidableEq m] (L : m → Language ℕ)

open Classical in
/-- The language-equivalence class of a state, as a `Finset`. -/
noncomputable def cls (x : m) : Finset m := Finset.univ.filter fun y => L y = L x

omit [DecidableEq m] in
theorem self_mem_cls (x : m) : x ∈ cls L x := by
  classical
  simp [cls]

omit [DecidableEq m] in
theorem cls_eq_of_eq {x y : m} (hxy : L x = L y) : cls L x = cls L y := by
  classical
  simp only [cls]
  exact Finset.filter_congr fun z _ ↦ by rw [hxy]

open Classical in
/-- A canonical representative of the language-equivalence class of a state: the element of the
class that is least under an arbitrary enumeration of the (finite) state type. -/
noncomputable def rep (x : m) : m :=
  (Fintype.equivFin m).symm
    (((cls L x).image (Fintype.equivFin m)).min' ⟨_, Finset.mem_image_of_mem _ (self_mem_cls L x)⟩)

omit [DecidableEq m] in
theorem rep_mem_cls (x : m) : rep L x ∈ cls L x := by
  classical
  obtain ⟨y, hy, hey⟩ := Finset.mem_image.1
    (Finset.min'_mem ((cls L x).image (Fintype.equivFin m))
      ⟨_, Finset.mem_image_of_mem _ (self_mem_cls L x)⟩)
  rw [rep, ← hey, Equiv.symm_apply_apply]
  exact hy

omit [DecidableEq m] in
/-- The canonical representative has the same language. -/
theorem lang_rep (x : m) : L (rep L x) = L x := by
  classical
  have := rep_mem_cls L x
  simpa [cls] using this

omit [DecidableEq m] in
/-- States with the same language have the same canonical representative. -/
theorem rep_eq_of_eq {x y : m} (hxy : L x = L y) : rep L x = rep L y := by
  classical
  have hc : (cls L x).image (Fintype.equivFin m) = (cls L y).image (Fintype.equivFin m) := by
    rw [cls_eq_of_eq L hxy]
  have key : ∀ (s t : Finset (Fin (Fintype.card m))) (hs : s.Nonempty) (ht : t.Nonempty),
      s = t → s.min' hs = t.min' ht := by
    rintro s t hs ht rfl
    rfl
  rw [rep, rep]
  exact congrArg _ (key _ _ _ _ hc)

end Rep

/-! ### The main comparison theorem -/

section Compare

variable {K : Type*} [KleeneAlgebra K] {n n' : Type*} [Fintype n] [DecidableEq n]
  [Fintype n'] [DecidableEq n']

/-- **Two deterministic automata accepting the same language denote the same element of every
Kleene algebra.** -/
theorem value_eq_of_langOf_eq (Γ : Finset ℕ) (ρ : ℕ → K)
    {A : EpsNFA n} {init : n} {nxt : ℕ → n → n} (hA : A.IsDet init nxt)
    {A' : EpsNFA n'} {init' : n'} {nxt' : ℕ → n' → n'} (hA' : A'.IsDet init' nxt')
    (hlang : langOf A nxt Γ init = langOf A' nxt' Γ init') :
    A.value Γ ρ = A'.value Γ ρ := by
  classical
  set L : n ⊕ n' → Language ℕ := Sum.elim (langOf A nxt Γ) (langOf A' nxt' Γ) with hL
  set nxtSum : ℕ → (n ⊕ n') → (n ⊕ n') := fun a => Sum.map (nxt a) (nxt' a) with hnxtSum
  set accSum : (n ⊕ n') → Prop := Sum.elim A.accept A'.accept with haccSum
  -- the language of a state determines acceptance and the derivative
  have hnil : ∀ x, accSum x ↔ [] ∈ L x := by
    rintro (i | i') <;> exact nil_mem_langOf_iff.symm
  have hderiv : ∀ a ∈ Γ, ∀ x, L (nxtSum a x) = {w | a :: w ∈ L x} := by
    rintro a ha (i | i')
    · exact langOf_deriv ha
    · exact langOf_deriv ha
  -- the common automaton, on canonical representatives
  set r : (n ⊕ n') → (n ⊕ n') := rep L with hr
  set nxtQ : ℕ → (n ⊕ n') → (n ⊕ n') := fun a c => if a ∈ Γ then r (nxtSum a c) else c with hnxtQ
  set B : EpsNFA (n ⊕ n') :=
    { start := fun c => c = r (Sum.inl init)
      accept := accSum
      eps := fun _ _ => False
      step := fun a c d => d = nxtQ a c } with hB
  have hBdet : B.IsDet (r (Sum.inl init)) nxtQ :=
    { start_iff := fun _ ↦ Iff.rfl
      epsFree := fun _ _ h ↦ h
      step_iff := fun _ _ _ ↦ Iff.rfl }
  -- the homomorphism condition, for either component
  have hhom : ∀ (x : n ⊕ n') (a : ℕ), a ∈ Γ → r (nxtSum a x) = nxtQ a (r x) := by
    intro x a ha
    rw [hnxtQ]
    simp only [if_pos ha]
    refine (rep_eq_of_eq L ?_).symm
    rw [hderiv a ha (r x), hderiv a ha x, lang_rep L x]
  have hraccept : ∀ x : n ⊕ n', accSum (r x) ↔ accSum x := by
    intro x
    rw [hnil, hnil, lang_rep L x]
  -- both automata map onto `B`
  have h1 : B.value Γ ρ = A.value Γ ρ := by
    refine value_eq_of_hom Γ ρ hA hBdet (fun i ↦ r (Sum.inl i)) rfl ?_ ?_
    · intro a ha i
      exact hhom (Sum.inl i) a ha
    · intro i
      exact (hraccept (Sum.inl i)).trans Iff.rfl
  have h2 : B.value Γ ρ = A'.value Γ ρ := by
    refine value_eq_of_hom Γ ρ hA' hBdet (fun i ↦ r (Sum.inr i)) ?_ ?_ ?_
    · exact (rep_eq_of_eq L hlang.symm)
    · intro a ha i
      exact hhom (Sum.inr i) a ha
    · intro i
      exact (hraccept (Sum.inr i)).trans Iff.rfl
  rw [← h1, h2]

end Compare

end RelationAlgebra.Automata
