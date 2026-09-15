import RelationAlgebra.KATCompleteness.Recovery
import RelationAlgebra.KATCompleteness.LangCorrect

/-!
# Completeness of the guarded-string semantics for Kleene algebra with tests

This file assembles the main result: two KAT terms with the same guarded-string semantics have
the same value in *every* Kleene algebra with tests.  No completeness, star-continuity,
commutativity or finiteness assumption is placed on the carrier `K` or on the test algebra `T`.

The argument is the standard one of Kozen and Smith, organised so that it reuses the Kleene
algebra completeness theorem already proved in `RelationAlgebra.Decide.KACompleteness`:

* a term `e` is interpreted as a matrix indexed by the atoms of the free Boolean algebra on the
  `k` test variables, each action `p` becoming `⌜α⌝ * ρ p * ⌜β⌝` at the entry `(α, β)`
  (`KAT.Completeness.valMat`);
* the same construction over the *free* Kleene algebra sends `p` to the single letter
  `⟨α, p, β⟩`, giving a matrix of regular languages (`KAT.Completeness.regMat`), and the entries
  of that matrix are determined by the guarded-string semantics
  (`KAT.Completeness.regMat_eq_of_gs_eq`);
* `RelationAlgebra.RegLang.interp` interprets a regular language in an arbitrary Kleene algebra,
  and is well defined precisely because of Kleene algebra completeness; it commutes with the
  matrix star (`Matrix.map_kstar`), so it carries `regMat` to `valMat`;
* finally `KAT.Completeness.sandwich_valMat` recovers the value of the term from its matrix.

## References

* Damien Pous, `relation-algebra`, `theories/kat_completeness.v`, revision
  `2d2af3631929399bbac56f57b3e15302d8697e1c`.
* D. Kozen and F. Smith, *Kleene algebra with tests: completeness and decidability*, CSL'96.
-/

open scoped Computability KAT

namespace KAT.Completeness

variable {T K : Type*} [BooleanAlgebra T] [KleeneAlgebra K] [KAT T K] (τ : ℕ → T) (ρ : ℕ → K)
  (k : ℕ)

/-- The interpretation of a letter `⟨α, p, β⟩` of the free Kleene algebra, read off from its
code.  Codes outside the range of `KAT.Completeness.code` are sent to `0`; they never occur. -/
noncomputable def actOfCode (n : ℕ) : K :=
  if h : n.unpair.1 < (allAtoms k).length ∧ n.unpair.2.unpair.2 < (allAtoms k).length then
    atomVal τ k ⟨n.unpair.1, h.1⟩ * ρ n.unpair.2.unpair.1 * atomVal τ k ⟨n.unpair.2.unpair.2, h.2⟩
  else 0

@[simp] theorem actOfCode_code (i : Idx k) (p : ℕ) (j : Idx k) :
    actOfCode τ ρ k (code i p j) = actMat τ ρ k p i j := by
  have h1 : (code i p j).unpair.1 = i.val := by simp [code]
  have h2 : (code i p j).unpair.2.unpair.1 = p := by simp [code]
  have h3 : (code i p j).unpair.2.unpair.2 = j.val := by simp [code]
  rw [actOfCode, dif_pos (by rw [h1, h3]; exact ⟨i.isLt, j.isLt⟩)]
  simp only [actMat]
  congr 1
  · congr 1
    · congr 1
      exact Fin.eq_of_val_eq h1
    · rw [h2]
  · congr 1
    exact Fin.eq_of_val_eq h3

/-- Interpreting a regular language in `K` is a Kleene algebra homomorphism.  Well-definedness of
`RelationAlgebra.RegLang.interp` is exactly Kleene algebra completeness. -/
theorem isKAHom_interp :
    Matrix.IsKAHom (RelationAlgebra.RegLang.interp (actOfCode τ ρ k)) where
  map_zero := RelationAlgebra.RegLang.interp_zero _
  map_one := RelationAlgebra.RegLang.interp_one _
  map_add := RelationAlgebra.RegLang.interp_add _
  map_mul := RelationAlgebra.RegLang.interp_mul _
  map_kstar := RelationAlgebra.RegLang.interp_kstar _

/-- The free matrix interpretation is carried to the matrix interpretation in `K`. -/
theorem map_regMat (e : KTerm) :
    (regMat k e).map (RelationAlgebra.RegLang.interp (actOfCode τ ρ k)) = valMat τ ρ k e := by
  rw [regMat, evalMat_map (isKAHom_interp τ ρ k), valMat]
  refine congrArg (fun P ↦ evalMat P e) (funext fun p ↦ ?_)
  funext i j
  simp only [Matrix.map_apply, RelationAlgebra.RegLang.interp_ofTerm, KleeneAlgebra.Term.eval]
  exact actOfCode_code τ ρ k i p j

/-- **Completeness of the guarded-string semantics for KAT.**  Two terms with the same guarded
strings have the same value in every Kleene algebra with tests. -/
theorem KTerm.eval_eq_of_gs_eq {e f : KTerm} (he : ∀ i ∈ e.tvars, i < k)
    (hf : ∀ i ∈ f.tvars, i < k) (h : e.gs k = f.gs k) : e.eval τ ρ = f.eval τ ρ := by
  have hval : valMat τ ρ k e = valMat τ ρ k f := by
    rw [← map_regMat τ ρ k e, ← map_regMat τ ρ k f, regMat_eq_of_gs_eq h]
  rw [eval_eq_sandwich τ ρ k e he, eval_eq_sandwich τ ρ k f hf, hval]

/-- The inequational form. -/
theorem KTerm.eval_le_of_gs_subset {e f : KTerm} (he : ∀ i ∈ e.tvars, i < k)
    (hf : ∀ i ∈ f.tvars, i < k) (h : e.gs k ⊆ f.gs k) : e.eval τ ρ ≤ f.eval τ ρ := by
  have hadd : (KTerm.add e f).gs k = f.gs k := Set.union_eq_self_of_subset_left h
  have hmem : ∀ i ∈ (KTerm.add e f).tvars, i < k := by
    intro i hi
    rcases List.mem_append.1 hi with hi | hi
    · exact he i hi
    · exact hf i hi
  have := KTerm.eval_eq_of_gs_eq τ ρ k hmem hf hadd
  simpa [KTerm.eval] using le_of_eq this

end KAT.Completeness

namespace KAT.Completeness

variable {T K : Type*} [BooleanAlgebra T] [KleeneAlgebra K] [KAT T K]

/-- The reflection lemma used by the `kat` tactic for equalities: a successful bisimulation
check gives the equation in *every* Kleene algebra with tests. -/
theorem eval_eq_of_decideEq (τ : ℕ → T) (ρ : ℕ → K) {k : ℕ} {e f : KTerm} {fuel : ℕ}
    (he : e.tvarsBelow k = true) (hf : f.tvarsBelow k = true)
    (h : KTerm.decideEq k e f fuel = true) : e.eval τ ρ = f.eval τ ρ :=
  KTerm.eval_eq_of_gs_eq τ ρ k (KTerm.tvars_lt_of_tvarsBelow he)
    (KTerm.tvars_lt_of_tvarsBelow hf) (KTerm.gs_eq_of_decideEq h)

/-- The reflection lemma used by the `kat` tactic for inequalities. -/
theorem eval_le_of_decideLe (τ : ℕ → T) (ρ : ℕ → K) {k : ℕ} {e f : KTerm} {fuel : ℕ}
    (he : e.tvarsBelow k = true) (hf : f.tvarsBelow k = true)
    (h : KTerm.decideLe k e f fuel = true) : e.eval τ ρ ≤ f.eval τ ρ :=
  KTerm.eval_le_of_gs_subset τ ρ k (KTerm.tvars_lt_of_tvarsBelow he)
    (KTerm.tvars_lt_of_tvarsBelow hf) (KTerm.gs_le_of_decideLe h)

end KAT.Completeness
