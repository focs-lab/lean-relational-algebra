import RelationAlgebra.Examples.Paterson.Programs

/-! # The concrete assignment facts used in Paterson's equivalence

Every side condition used by the algebraic proof is proved here from the store semantics.
-/
open scoped Computability SetRel KAT
namespace Paterson.Facts
open Programs
variable (M : Interpretation)

theorem a1_p22 : (⌜a1.denote M⌝ : SetRel State State) * p22.denote M =
    p22.denote M * ⌜a1.denote M⌝ := by
  exact test_assign_comm M _ _ _ (by decide)

theorem a1_q214 : (⌜a1.denote M⌝ : SetRel State State) * q214.denote M =
    q214.denote M * ⌜a1.denote M⌝ := by
  exact test_assign_comm M _ _ _ (by decide)

theorem a1_q211 : (⌜a1.denote M⌝ : SetRel State State) * q211.denote M =
    q211.denote M * ⌜a1.denote M⌝ := by
  exact test_assign_comm M _ _ _ (by decide)

theorem a1_q311 : (⌜a1.denote M⌝ : SetRel State State) * q311.denote M =
    q311.denote M * ⌜a1.denote M⌝ := by
  exact test_assign_comm M _ _ _ (by decide)

theorem a2_p13 : (⌜a2.denote M⌝ : SetRel State State) * p13.denote M =
    p13.denote M * ⌜a2.denote M⌝ := by
  exact test_assign_comm M _ _ _ (by decide)

theorem a2_r12 : (⌜a2.denote M⌝ : SetRel State State) * r12.denote M =
    r12.denote M * ⌜a2.denote M⌝ := by
  exact test_assign_comm M _ _ _ (by decide)

theorem a2_r13 : (⌜a2.denote M⌝ : SetRel State State) * r13.denote M =
    r13.denote M * ⌜a2.denote M⌝ := by
  exact test_assign_comm M _ _ _ (by decide)

theorem a3_p13 : (⌜a3.denote M⌝ : SetRel State State) * p13.denote M =
    p13.denote M * ⌜a3.denote M⌝ := by
  exact test_assign_comm M _ _ _ (by decide)

theorem a3_p22 : (⌜a3.denote M⌝ : SetRel State State) * p22.denote M =
    p22.denote M * ⌜a3.denote M⌝ := by
  exact test_assign_comm M _ _ _ (by decide)

theorem a3_r12 : (⌜a3.denote M⌝ : SetRel State State) * r12.denote M =
    r12.denote M * ⌜a3.denote M⌝ := by
  exact test_assign_comm M _ _ _ (by decide)

theorem a3_r13 : (⌜a3.denote M⌝ : SetRel State State) * r13.denote M =
    r13.denote M * ⌜a3.denote M⌝ := by
  exact test_assign_comm M _ _ _ (by decide)

theorem a4_p13 : (⌜a4.denote M⌝ : SetRel State State) * p13.denote M =
    p13.denote M * ⌜a4.denote M⌝ := by
  exact test_assign_comm M _ _ _ (by decide)

theorem a4_p11 : (⌜a4.denote M⌝ : SetRel State State) * p11.denote M =
    p11.denote M * ⌜a4.denote M⌝ := by
  exact test_assign_comm M _ _ _ (by decide)

theorem a4_p22 : (⌜a4.denote M⌝ : SetRel State State) * p22.denote M =
    p22.denote M * ⌜a4.denote M⌝ := by
  exact test_assign_comm M _ _ _ (by decide)

theorem a4_q214 : (⌜a4.denote M⌝ : SetRel State State) * q214.denote M =
    q214.denote M * ⌜a4.denote M⌝ := by
  exact test_assign_comm M _ _ _ (by decide)

theorem a4_q211 : (⌜a4.denote M⌝ : SetRel State State) * q211.denote M =
    q211.denote M * ⌜a4.denote M⌝ := by
  exact test_assign_comm M _ _ _ (by decide)

theorem a4_q311 : (⌜a4.denote M⌝ : SetRel State State) * q311.denote M =
    q311.denote M * ⌜a4.denote M⌝ := by
  exact test_assign_comm M _ _ _ (by decide)

theorem p41_p11 : p41.denote M * p11.denote M *
    ⌜a1.denote M ⊓ (a4.denote M)ᶜ ⊔ (a1.denote M)ᶜ ⊓ a4.denote M⌝ ≤ 0 := by
  simp only [Prog.denote, assign, graph_mul]
  apply same_value
  intro s
  simp [BExpr.denote, BExpr.eval, AExpr.eval, update]

theorem q211_q311 : q211.denote M * q311.denote M *
    ⌜a2.denote M ⊓ (a3.denote M)ᶜ ⊔ (a2.denote M)ᶜ ⊓ a3.denote M⌝ ≤ 0 := by
  simp only [Prog.denote, assign, graph_mul]
  apply same_value
  intro s
  simp [BExpr.denote, BExpr.eval, AExpr.eval, update]

theorem r12_p22 : r12.denote M * p22.denote M * p22.denote M *
    ⌜a1.denote M ⊓ (a2.denote M)ᶜ ⊔ (a1.denote M)ᶜ ⊓ a2.denote M⌝ ≤ 0 := by
  simp only [Prog.denote, assign, graph_mul]
  apply same_value
  intro s
  simp [BExpr.denote, BExpr.eval, AExpr.eval, update, Function.comp_def]

theorem p13_p22 : p13.denote M * p22.denote M = p22.denote M * p13.denote M := by
  exact assign_comm M _ _ _ _ (by decide) (by decide) (by decide)

theorem r13_p22 : r13.denote M * p22.denote M = p22.denote M * r13.denote M := by
  exact assign_comm M _ _ _ _ (by decide) (by decide) (by decide)

theorem p41_p11_q214 : p41.denote M * p11.denote M * q214.denote M =
    p41.denote M * p11.denote M * q211.denote M := by
  simp only [Prog.denote, assign, graph_mul]
  congr 1

theorem q211_q311_r13 : q211.denote M * q311.denote M * r13.denote M =
    q211.denote M * q311.denote M * r12.denote M := by
  simp only [Prog.denote, assign, graph_mul]
  congr 1

theorem p13_z2 : p13.denote M * z2.denote M = z2.denote M := by
  simp only [Prog.denote, assign, graph_mul]
  congr 1
  funext s x
  cases x <;> simp [update, AExpr.eval, Function.comp_def]

theorem x1_p11 : x1.denote M * p11.denote M = s1.denote M := by
  exact assign_assign M _ _ _

theorem p13_p11 : p13.denote M * p11.denote M = r13.denote M := by
  exact assign_assign M _ _ _

theorem p22_q211 : p22.denote M * q211.denote M = q211.denote M := by
  exact assign_assign M _ _ _

/-- Clearing a temporary before the final cleanup has no additional effect. -/
theorem del_clr (y : Loc) (h : y ≠ .io) :
    (del y).denote M * clr.denote M = clr.denote M := by
  simp only [Prog.denote, assign, graph_mul]
  congr 1
  funext s x
  cases y <;> cases x <;> simp_all [update, AExpr.eval, Function.comp_def]

/-- Dead-store elimination with the common final cleanup of both schemes. -/
theorem gc_clr (y : Loc) (p : Prog) (hy : y ≠ .io) (hp : p.dontRead y = true) :
    (p.gc y).denote M * clr.denote M = p.denote M * clr.denote M := by
  calc
    _ = ((p.gc y).denote M * (del y).denote M) * clr.denote M := by rw [mul_assoc, del_clr M y hy]
    _ = (p.denote M * (del y).denote M) * clr.denote M := by
      exact congrArg (fun r : SetRel State State => r * clr.denote M) (Prog.gc_correct M y p hp)
    _ = _ := by rw [mul_assoc, del_clr M y hy]


/-- Substitute the assignment into its following test and update. -/
theorem left_init : s1.denote M * ⌜a1.denote M⌝ * q211.denote M =
    ⌜bInit.denote M⌝ * s1.denote M * qInit.denote M := by
  have ht := test_assign M .y1 (.f (.var .io)) a1
  change (⌜bInit.denote M⌝ : SetRel State State) * s1.denote M =
    s1.denote M * ⌜a1.denote M⌝ at ht
  rw [← ht, mul_assoc]
  have hq := assign_subst M .y1 .y2 (.f (.var .io)) (.g (.var .y1) (.var .y1)) (by decide)
  change s1.denote M * q211.denote M = s1.denote M * qInit.denote M at hq
  rw [hq, mul_assoc]

/-- Substitute the assignment into its following test and update. -/
theorem left_loop : r12.denote M * ⌜a1.denote M⌝ * q211.denote M =
    ⌜bNext.denote M⌝ * r12.denote M * qNext.denote M := by
  have ht := test_assign M .y1 (.f (.f (.var .y2))) a1
  change (⌜bNext.denote M⌝ : SetRel State State) * r12.denote M =
    r12.denote M * ⌜a1.denote M⌝ at ht
  rw [← ht, mul_assoc]
  have hq := assign_subst M .y1 .y2 (.f (.f (.var .y2))) (.g (.var .y1) (.var .y1)) (by decide)
  change r12.denote M * q211.denote M = r12.denote M * qNext.denote M at hq
  rw [hq, mul_assoc]

/-- Substitute the assignment into its following test and update. -/
theorem right_init : s2.denote M * ⌜a2.denote M⌝ * q222.denote M =
    ⌜bInit.denote M⌝ * qInit.denote M := by
  have ht := test_assign M .y2 (.f (.var .io)) a2
  change (⌜bInit.denote M⌝ : SetRel State State) * s2.denote M =
    s2.denote M * ⌜a2.denote M⌝ at ht
  rw [← ht, mul_assoc]
  have hq := assign_assign M .y2 (.f (.var .io)) (.g (.var .y2) (.var .y2))
  change s2.denote M * q222.denote M = qInit.denote M at hq
  rw [hq]

/-- Substitute the assignment into its following test and update. -/
theorem right_loop : r22.denote M * ⌜a2.denote M⌝ * q222.denote M =
    ⌜bNext.denote M⌝ * qNext.denote M := by
  have ht := test_assign M .y2 (.f (.f (.var .y2))) a2
  change (⌜bNext.denote M⌝ : SetRel State State) * r22.denote M =
    r22.denote M * ⌜a2.denote M⌝ at ht
  rw [← ht, mul_assoc]
  have hq := assign_assign M .y2 (.f (.f (.var .y2))) (.g (.var .y2) (.var .y2))
  change r22.denote M * q222.denote M = qNext.denote M at hq
  rw [hq]

end Paterson.Facts
