import Mathlib.Order.GaloisConnection.Basic
import RelationAlgebra.Converse
import RelationAlgebra.Kleene.Quantale

/-!
# Residuated idempotent semirings: left and right factors

This file introduces *residuals* (also called *factors*, or *divisions*) for the
Kleene-algebra hierarchy, porting `theories/factors.v` and the residual fragment of
`theories/monoid.v` from Damien Pous' Rocq library `relation-algebra`.

## Design

* **No completeness assumption.**  Mathlib's `Mathlib.Algebra.Order.Quantale` already provides
  residuals `x ⇨ₗ y` and `x ⇨ᵣ y` for a *complete* lattice, defined as suprema.  Following
  Pous, we axiomatise the residuals instead, so that they are available in models which are
  not complete: `ResiduatedIdemSemiring` is an `IdemSemiring` together with two binary
  operations `ldiv` and `rdiv` characterised by the adjunctions
  ```
  y ≤ ldiv x z ↔ x * y ≤ z        x ≤ rdiv z y ↔ x * y ≤ z
  ```
  Every unital quantale gives such a structure (`ResiduatedIdemSemiring.ofQuantale`), and so
  does every relation algebra, via `x ⇘ z = (xᵒ * zᶜ)ᶜ` (`ResiduatedIdemSemiring.ofRelationAlgebra`,
  Pous' `ldv_unfold`).

* **Notation.**  In the scope `RelationAlgebra` we write `x ⇘ z` for `ldiv x z` (Pous'
  `x -o z`, the largest `y` with `x * y ≤ z`) and `z ⇙ y` for `rdiv z y` (Pous' `z o- y`, the
  largest `x` with `x * y ≤ z`).  The arrow points at the "divided" argument.  Both bind
  looser than `*`, and `⇙` binds tighter than `⇘`, so that `x ⇘ y ⇙ z` parses as
  `x ⇘ (y ⇙ z)`, as in `ldiv_rdiv`.  Activate them with `open scoped RelationAlgebra`.

* **Galois connections.**  The two specifications say exactly that `x * ·` and `· * y` have
  right adjoints, which we record as `gc_mul_ldiv` and `gc_mul_rdiv`; most lemmas below are
  then instances of the general `GaloisConnection` API.

* **Residuated Kleene algebras.**  `ResiduatedKleeneAlgebra` combines the two structures, and
  is used for `kstar_ldiv_self : (x ⇘ x)∗ = x ⇘ x` (Pous' `str_ldv`).

* **The relational model.**  `SetRel α α` is residuated, with
  `R ⇘ S = {(b, c) | ∀ a, a ~[R] b → a ~[S] c}`.  As everywhere in this library, the instance
  is scoped: use `open scoped SetRel`.

## References

* [D. Pous, *Relation Algebra and KAT in Coq*, <https://github.com/damien-pous/relation-algebra>],
  files `theories/factors.v`, `theories/monoid.v` and `theories/lattice.v`
* [A. Tarski, *On the calculus of relations*, J. Symb. Logic 6 (1941)]
* [B. Jónsson and A. Tarski, *Boolean algebras with operators II*, Amer. J. Math. 74 (1952)]
* [D. Kozen, *A completeness theorem for Kleene algebras and the algebra of regular events*]
-/

open scoped Computability

/-- A **residuated idempotent semiring**: an idempotent semiring in which multiplication has a
right adjoint in each argument.  `ldiv x z` (notation `x ⇘ z`) is the largest `y` such that
`x * y ≤ z`, and `rdiv z y` (notation `z ⇙ y`) is the largest `x` such that `x * y ≤ z`.

These are Pous' left and right *factors* `x -o z` and `z o- y`.  Unlike the residuals of a
quantale, they are axiomatised rather than defined by a supremum, so the definition makes
sense in models whose order is not complete. -/
class ResiduatedIdemSemiring (K : Type*) extends IdemSemiring K where
  /-- `ldiv x z` is the largest `y` with `x * y ≤ z`. -/
  ldiv : K → K → K
  /-- `rdiv z y` is the largest `x` with `x * y ≤ z`. -/
  rdiv : K → K → K
  /-- `ldiv x z` is right adjoint to left multiplication by `x`. -/
  ldiv_spec (x y z : K) : y ≤ ldiv x z ↔ x * y ≤ z
  /-- `rdiv z y` is right adjoint to right multiplication by `y`. -/
  rdiv_spec (x y z : K) : x ≤ rdiv z y ↔ x * y ≤ z

/-- A **residuated Kleene algebra**: a Kleene algebra whose multiplication has residuals. -/
class ResiduatedKleeneAlgebra (K : Type*) extends KleeneAlgebra K, ResiduatedIdemSemiring K

namespace RelationAlgebra

/-- `x ⇘ z` is the largest `y` such that `x * y ≤ z` (Pous' left factor `x -o z`). -/
scoped infixr:65 " ⇘ " => ResiduatedIdemSemiring.ldiv

/-- `z ⇙ y` is the largest `x` such that `x * y ≤ z` (Pous' right factor `z o- y`). -/
scoped infixl:66 " ⇙ " => ResiduatedIdemSemiring.rdiv

end RelationAlgebra

open scoped RelationAlgebra

namespace ResiduatedIdemSemiring

variable {K : Type*} [ResiduatedIdemSemiring K] (x y z w : K)

/-! ### The two Galois connections -/

/-- Left multiplication by `x` is left adjoint to `x ⇘ ·`. -/
theorem gc_mul_ldiv : GaloisConnection (x * ·) (x ⇘ ·) := fun _ _ ↦ (ldiv_spec _ _ _).symm

/-- Right multiplication by `y` is left adjoint to `· ⇙ y`. -/
theorem gc_mul_rdiv : GaloisConnection (· * y) (· ⇙ y) := fun _ _ ↦ (rdiv_spec _ _ _).symm

/-! ### Cancellation and the unit of the adjunction -/

/-- `x * (x ⇘ z) ≤ z`: the counit of the adjunction (Pous' `ldv_cancel`). -/
theorem mul_ldiv_le : x * (x ⇘ z) ≤ z := (ldiv_spec x (x ⇘ z) z).1 le_rfl

/-- `(z ⇙ y) * y ≤ z`: the counit of the adjunction (Pous' `rdv_cancel`). -/
theorem rdiv_mul_le : (z ⇙ y) * y ≤ z := (rdiv_spec (z ⇙ y) y z).1 le_rfl

/-- `y ≤ x ⇘ (x * y)`: the unit of the adjunction (Pous' `ldv_xdot`). -/
theorem le_ldiv_mul : y ≤ x ⇘ (x * y) := (ldiv_spec x y (x * y)).2 le_rfl

/-- `x ≤ (x * y) ⇙ y`: the unit of the adjunction (Pous' `rdv_xdot`). -/
theorem le_mul_rdiv : x ≤ (x * y) ⇙ y := (rdiv_spec x y (x * y)).2 le_rfl

/-! ### Monotonicity -/

theorem ldiv_le_ldiv {x x' z z' : K} (hx : x' ≤ x) (hz : z ≤ z') : x ⇘ z ≤ x' ⇘ z' :=
  (ldiv_spec _ _ _).2 <| ((mul_le_mul_left hx _).trans (mul_ldiv_le x z)).trans hz

theorem rdiv_le_rdiv {y y' z z' : K} (hy : y' ≤ y) (hz : z ≤ z') : z ⇙ y ≤ z' ⇙ y' :=
  (rdiv_spec _ _ _).2 <| ((mul_le_mul_right hy _).trans (rdiv_mul_le y z)).trans hz

/-- `x ⇘ ·` is monotone. -/
theorem ldiv_mono_right : Monotone (x ⇘ ·) := (gc_mul_ldiv x).monotone_u

/-- `· ⇘ z` is antitone. -/
theorem ldiv_anti_left : Antitone (· ⇘ z) := fun _ _ h ↦ ldiv_le_ldiv h le_rfl

/-- `· ⇙ y` is monotone. -/
theorem rdiv_mono_left : Monotone (· ⇙ y) := (gc_mul_rdiv y).monotone_u

/-- `z ⇙ ·` is antitone. -/
theorem rdiv_anti_right : Antitone (z ⇙ ·) := fun _ _ h ↦ rdiv_le_rdiv h le_rfl

/-! ### Composition and the unit `1` -/

/-- Pous' `ldv_dotx`: `(x * y) ⇘ z = y ⇘ (x ⇘ z)`. -/
theorem mul_ldiv : (x * y) ⇘ z = y ⇘ (x ⇘ z) :=
  eq_of_forall_le_iff fun t ↦ by rw [ldiv_spec, ldiv_spec, ldiv_spec, mul_assoc]

/-- Pous' `rdv_dotx`: `z ⇙ (y * x) = (z ⇙ x) ⇙ y`. -/
theorem rdiv_mul : z ⇙ (y * x) = z ⇙ x ⇙ y :=
  eq_of_forall_le_iff fun t ↦ by rw [rdiv_spec, rdiv_spec, rdiv_spec, mul_assoc]

/-- Pous' `ldv_rdv`: `x ⇘ (y ⇙ z) = (x ⇘ y) ⇙ z`. -/
theorem ldiv_rdiv : x ⇘ (y ⇙ z) = (x ⇘ y) ⇙ z :=
  eq_of_forall_le_iff fun t ↦ by rw [ldiv_spec, rdiv_spec, rdiv_spec, ldiv_spec, mul_assoc]

/-- Pous' `ldv_1x`: `1 ⇘ x = x`. -/
theorem one_ldiv : (1 : K) ⇘ x = x :=
  eq_of_forall_le_iff fun t ↦ by rw [ldiv_spec, one_mul]

/-- Pous' `rdv_1x`: `x ⇙ 1 = x`. -/
theorem rdiv_one : x ⇙ (1 : K) = x :=
  eq_of_forall_le_iff fun t ↦ by rw [rdiv_spec, mul_one]

/-- Pous' `leq_ldv`: `x ≤ y ↔ 1 ≤ x ⇘ y`. -/
theorem le_iff_one_le_ldiv : x ≤ y ↔ 1 ≤ x ⇘ y := by rw [ldiv_spec, mul_one]

/-- Pous' `leq_rdv`: `x ≤ y ↔ 1 ≤ y ⇙ x`. -/
theorem le_iff_one_le_rdiv : x ≤ y ↔ 1 ≤ y ⇙ x := by rw [rdiv_spec, one_mul]

/-- Pous' `ldv_xx`: `1 ≤ x ⇘ x`. -/
theorem one_le_ldiv_self : 1 ≤ x ⇘ x := (le_iff_one_le_ldiv x x).1 le_rfl

/-- Pous' `rdv_xx`: `1 ≤ x ⇙ x`. -/
theorem one_le_rdiv_self : 1 ≤ x ⇙ x := (le_iff_one_le_rdiv x x).1 le_rfl

/-- Pous' `ldv_trans`: left factors compose. -/
theorem ldiv_mul_ldiv_le : (x ⇘ y) * (y ⇘ z) ≤ x ⇘ z :=
  (ldiv_spec _ _ _).2 <| by
    rw [← mul_assoc]
    exact (mul_le_mul_left (mul_ldiv_le x y) _).trans (mul_ldiv_le y z)

/-- Pous' `rdv_trans`: right factors compose. -/
theorem rdiv_mul_rdiv_le : (z ⇙ y) * (y ⇙ x) ≤ z ⇙ x :=
  (rdiv_spec _ _ _).2 <| by
    rw [mul_assoc]
    exact (mul_le_mul_right (rdiv_mul_le x y) _).trans (rdiv_mul_le y z)

/-! ### Idempotency of the adjunction -/

/-- `x ⇘ (x * (x ⇘ z)) = x ⇘ z`. -/
theorem ldiv_mul_ldiv_self : x ⇘ (x * (x ⇘ z)) = x ⇘ z := (gc_mul_ldiv x).u_l_u_eq_u z

/-- `((z ⇙ y) * y) ⇙ y = z ⇙ y`. -/
theorem rdiv_mul_rdiv_self : ((z ⇙ y) * y) ⇙ y = z ⇙ y := (gc_mul_rdiv y).u_l_u_eq_u z

/-- `x * (x ⇘ (x * y)) = x * y`. -/
theorem mul_ldiv_mul_self : x * (x ⇘ (x * y)) = x * y := (gc_mul_ldiv x).l_u_l_eq_l y

/-- `((x * y) ⇙ y) * y = x * y`. -/
theorem mul_rdiv_mul_self : ((x * y) ⇙ y) * y = x * y := (gc_mul_rdiv y).l_u_l_eq_l x

/-! ### Interaction with `0` and `⊔`

An `IdemSemiring` has a least element `0 = ⊥` but no greatest element in general.  Pous'
`ldv_0x` (`0 -o x` is the top element) therefore becomes the statement that *every* element is
below `0 ⇘ z`; similarly, `(x ⊔ y) ⇘ z` is the greatest lower bound of `x ⇘ z` and `y ⇘ z`
even when binary meets do not exist. -/

/-- `0 ⇘ z` is the greatest element: this is Pous' `ldv_0x`. -/
theorem le_zero_ldiv : y ≤ (0 : K) ⇘ z :=
  (ldiv_spec _ _ _).2 (by rw [zero_mul, ← bot_eq_zero]; exact bot_le)

/-- `z ⇙ 0` is the greatest element: this is Pous' `rdv_0x`. -/
theorem le_rdiv_zero : x ≤ z ⇙ (0 : K) :=
  (rdiv_spec _ _ _).2 (by rw [mul_zero, ← bot_eq_zero]; exact bot_le)

theorem add_ldiv_le_iff : w ≤ (x + y) ⇘ z ↔ w ≤ x ⇘ z ∧ w ≤ y ⇘ z := by
  rw [ldiv_spec, ldiv_spec, ldiv_spec, add_mul, add_le_iff]

theorem rdiv_add_le_iff : w ≤ z ⇙ (x + y) ↔ w ≤ z ⇙ x ∧ w ≤ z ⇙ y := by
  rw [rdiv_spec, rdiv_spec, rdiv_spec, mul_add, add_le_iff]

/-- `(x ⊔ y) ⇘ z` is the greatest lower bound of `x ⇘ z` and `y ⇘ z`. -/
theorem isGLB_add_ldiv : IsGLB {x ⇘ z, y ⇘ z} ((x + y) ⇘ z) := by
  constructor
  · rintro t (rfl | rfl)
    · exact ldiv_anti_left z le_self_add
    · exact ldiv_anti_left z le_add_self
  · intro t ht
    exact (add_ldiv_le_iff x y z t).2 ⟨ht (by simp), ht (by simp)⟩

/-- `z ⇙ (x ⊔ y)` is the greatest lower bound of `z ⇙ x` and `z ⇙ y`. -/
theorem isGLB_rdiv_add : IsGLB {z ⇙ x, z ⇙ y} (z ⇙ (x + y)) := by
  constructor
  · rintro t (rfl | rfl)
    · exact rdiv_anti_right z le_self_add
    · exact rdiv_anti_right z le_add_self
  · intro t ht
    exact (rdiv_add_le_iff x y z t).2 ⟨ht (by simp), ht (by simp)⟩

theorem add_ldiv_le_left : (x + y) ⇘ z ≤ x ⇘ z := ldiv_anti_left z le_self_add

theorem add_ldiv_le_right : (x + y) ⇘ z ≤ y ⇘ z := ldiv_anti_left z le_add_self

theorem ldiv_add_le : (x ⇘ y) + (x ⇘ z) ≤ x ⇘ (y + z) :=
  add_le (ldiv_mono_right x le_self_add) (ldiv_mono_right x le_add_self)

theorem rdiv_add_le_left : z ⇙ (x + y) ≤ z ⇙ x := rdiv_anti_right z le_self_add

theorem rdiv_add_le_right : z ⇙ (x + y) ≤ z ⇙ y := rdiv_anti_right z le_add_self

theorem add_rdiv_le : (y ⇙ x) + (z ⇙ x) ≤ (y + z) ⇙ x :=
  add_le (rdiv_mono_left x le_self_add) (rdiv_mono_left x le_add_self)

end ResiduatedIdemSemiring

/-! ### Residuals and the Kleene star -/

namespace ResiduatedKleeneAlgebra

open ResiduatedIdemSemiring

variable {K : Type*} [ResiduatedKleeneAlgebra K] (x : K)

/-- Pous' `str_ldv`: `(x ⇘ x)∗ = x ⇘ x`, since `x ⇘ x` is a reflexive transitive element. -/
theorem kstar_ldiv_self : (x ⇘ x)∗ = x ⇘ x :=
  le_antisymm
    (kstar_le_of_mul_le_left (one_le_ldiv_self x) (ldiv_mul_ldiv_le x x x)) le_kstar

/-- Pous' `str_rdv`: `(x ⇙ x)∗ = x ⇙ x`. -/
theorem kstar_rdiv_self : (x ⇙ x)∗ = x ⇙ x :=
  le_antisymm
    (kstar_le_of_mul_le_left (one_le_rdiv_self x) (rdiv_mul_rdiv_le x x x)) le_kstar

end ResiduatedKleeneAlgebra

/-! ### Residuals from quantales and from relation algebras -/

section OfQuantale

variable (K : Type*) [Monoid K] [CompleteLattice K] [IsQuantale K]

open scoped Quantale

-- See note [reducible non-instances]
/-- A unital quantale is residuated: `x ⇘ z = x ⇨ᵣ z` and `z ⇙ y = y ⇨ₗ z`, the residuals of
`Mathlib.Algebra.Order.Quantale`. -/
abbrev ResiduatedIdemSemiring.ofQuantale : ResiduatedIdemSemiring K where
  __ := IdemSemiring.ofQuantale K
  ldiv x z := x ⇨ᵣ z
  rdiv z y := y ⇨ₗ z
  ldiv_spec _ _ _ := Quantale.rightMulResiduation_le_iff_mul_le
  rdiv_spec _ _ _ := Quantale.leftMulResiduation_le_iff_mul_le

end OfQuantale

section OfRelationAlgebra

variable (K : Type*) [RelationAlgebra K]

-- See note [reducible non-instances]
/-- A relation algebra is residuated, with `x ⇘ z = (xᵒ * zᶜ)ᶜ` and `z ⇙ y = (zᶜ * yᵒ)ᶜ`.
This is Pous' `ldv_unfold`/`rdv_unfold`; the proof is the pair of Schröder rules. -/
abbrev ResiduatedIdemSemiring.ofRelationAlgebra : ResiduatedIdemSemiring K where
  __ := (inferInstance : IdemSemiring K)
  ldiv x z := (star x * zᶜ)ᶜ
  rdiv z y := (zᶜ * star y)ᶜ
  ldiv_spec _ _ _ := by rw [le_compl_comm, ← RelationAlgebra.schroeder_left]
  rdiv_spec _ _ _ := by rw [le_compl_comm, ← RelationAlgebra.schroeder_right]

/-- The left factor of a relation algebra, unfolded (Pous' `ldv_unfold`). -/
theorem ResiduatedIdemSemiring.ofRelationAlgebra_ldiv (x z : K) :
    (ResiduatedIdemSemiring.ofRelationAlgebra K).ldiv x z = (star x * zᶜ)ᶜ := rfl

/-- The right factor of a relation algebra, unfolded (Pous' `rdv_unfold`). -/
theorem ResiduatedIdemSemiring.ofRelationAlgebra_rdiv (y z : K) :
    (ResiduatedIdemSemiring.ofRelationAlgebra K).rdiv z y = (zᶜ * star y)ᶜ := rfl

end OfRelationAlgebra

/-! ### The relational model -/

namespace SetRel

variable {α : Type*} {R S : SetRel α α} {a b c : α}

/-- Binary relations are residuated: `R ⇘ S` relates `b` to `c` when every `R`-predecessor of
`b` is an `S`-predecessor of `c`. -/
scoped instance instResiduatedIdemSemiring : ResiduatedIdemSemiring (SetRel α α) where
  __ := instIdemSemiring
  ldiv R S := {p | ∀ a, a ~[R] p.1 → a ~[S] p.2}
  rdiv S T := {p | ∀ c, p.2 ~[T] c → p.1 ~[S] c}
  ldiv_spec R T S := by
    constructor
    · rintro h ⟨a, c⟩ ⟨b, hab, hbc⟩
      exact h hbc a hab
    · rintro h ⟨b, c⟩ hbc a hab
      exact h ⟨b, hab, hbc⟩
  rdiv_spec T R S := by
    constructor
    · rintro h ⟨a, c⟩ ⟨b, hab, hbc⟩
      exact h hab c hbc
    · rintro h ⟨a, b⟩ hab c hbc
      exact h ⟨b, hab, hbc⟩

/-- Binary relations form a residuated Kleene algebra. -/
scoped instance instResiduatedKleeneAlgebra : ResiduatedKleeneAlgebra (SetRel α α) where
  __ := instKleeneAlgebra
  __ := instResiduatedIdemSemiring

@[simp] theorem mem_ldiv : b ~[R ⇘ S] c ↔ ∀ a, a ~[R] b → a ~[S] c := Iff.rfl

@[simp] theorem mem_rdiv : a ~[S ⇙ R] b ↔ ∀ c, b ~[R] c → a ~[S] c := Iff.rfl

end SetRel

/-! ### Residuation with finite meets -/

/-- A residuated Kleene algebra with finite meets (including the empty meet).
The inherited structures share one order. No distributivity of the lattice, Boolean
complement, converse, or completeness assumption is needed for matrix residuals. -/
class ResiduatedKleeneLattice (K : Type*) extends ResiduatedKleeneAlgebra K, Lattice K,
    Top K where
  le_top : ∀ x : K, x ≤ ⊤

instance (priority := 100) ResiduatedKleeneLattice.toOrderTop {K : Type*}
    [h : ResiduatedKleeneLattice K] : OrderTop K where
  le_top := h.le_top

/-- Boolean relation algebras provide the finite meets needed for matrix residuals. -/
noncomputable instance (priority := 100) RelationAlgebra.toResiduatedKleeneLattice
    {K : Type*} [RelationAlgebra K] : ResiduatedKleeneLattice K where
  __ := (inferInstance : KleeneAlgebra K)
  __ := ResiduatedIdemSemiring.ofRelationAlgebra K
  __ := (inferInstance : Lattice K)
  __ := (inferInstance : Top K)
  le_top _ := _root_.le_top

namespace ResiduatedKleeneLattice

open ResiduatedIdemSemiring
variable {K : Type*} [ResiduatedKleeneLattice K] (a b c : K)

@[simp] theorem kstar_top : (⊤ : K)∗ = ⊤ := le_antisymm _root_.le_top le_kstar

@[simp] theorem zero_ldiv : (0 : K) ⇘ c = ⊤ := top_unique (le_zero_ldiv ⊤ c)
@[simp] theorem rdiv_zero : c ⇙ (0 : K) = ⊤ := top_unique (le_rdiv_zero ⊤ c)
@[simp] theorem ldiv_top : a ⇘ (⊤ : K) = ⊤ := top_unique ((ldiv_spec _ _ _).mpr _root_.le_top)
@[simp] theorem top_rdiv : (⊤ : K) ⇙ a = ⊤ := top_unique ((rdiv_spec _ _ _).mpr _root_.le_top)

theorem sup_ldiv : (a ⊔ b) ⇘ c = (a ⇘ c) ⊓ (b ⇘ c) := by
  apply eq_of_forall_le_iff
  intro d
  rw [← add_eq_sup, add_ldiv_le_iff, le_inf_iff]

theorem ldiv_inf : a ⇘ (b ⊓ c) = (a ⇘ b) ⊓ (a ⇘ c) := by
  apply eq_of_forall_le_iff
  intro d
  rw [le_inf_iff, ldiv_spec, ldiv_spec, ldiv_spec, le_inf_iff]

theorem rdiv_sup : a ⇙ (b ⊔ c) = (a ⇙ b) ⊓ (a ⇙ c) := by
  apply eq_of_forall_le_iff
  intro d
  rw [← add_eq_sup, rdiv_add_le_iff, le_inf_iff]

theorem inf_rdiv : (a ⊓ b) ⇙ c = (a ⇙ c) ⊓ (b ⇙ c) := by
  apply eq_of_forall_le_iff
  intro d
  rw [le_inf_iff, rdiv_spec, rdiv_spec, rdiv_spec, le_inf_iff]

end ResiduatedKleeneLattice

namespace ResiduatedKleeneAlgebra

variable {K : Type*} [ResiduatedKleeneAlgebra K] [StarRing K] (a b : K)

@[simp] theorem star_ldiv : star (a ⇘ b) = star b ⇙ star a := by
  apply eq_of_forall_le_iff
  intro c
  rw [← KleeneAlgebra.star_le_star_iff, star_star,
    ResiduatedIdemSemiring.ldiv_spec, ResiduatedIdemSemiring.rdiv_spec,
    ← KleeneAlgebra.star_le_star_iff, star_mul, star_star]

@[simp] theorem star_rdiv : star (a ⇙ b) = star b ⇘ star a := by
  apply eq_of_forall_le_iff
  intro c
  rw [← KleeneAlgebra.star_le_star_iff, star_star,
    ResiduatedIdemSemiring.rdiv_spec, ResiduatedIdemSemiring.ldiv_spec,
    ← KleeneAlgebra.star_le_star_iff, star_mul, star_star]

end ResiduatedKleeneAlgebra
