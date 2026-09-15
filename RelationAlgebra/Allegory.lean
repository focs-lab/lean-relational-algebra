import RelationAlgebra.Converse

/-!
# Allegories, and the standard relational predicates

An **allegory** (Freyd–Scedrov) is the fragment of relation algebra that survives when one
drops joins, complements and the Kleene star, keeping only composition, converse and binary
intersection, tied together by the *modular law*.  It is the "one-object" (untyped) version of
Freyd and Scedrov's notion; the corresponding structure with all sups is a Dedekind category.

This file ports the allegory fragment of `theories/monoid.v` and the standard facts about
functional, total, injective and surjective elements from `theories/relalg.v` of Damien Pous'
Rocq library `relation-algebra`.

## Design

* **Converse is Mathlib's `star`**, exactly as in `RelationAlgebra.Converse`.

* `Allegory K` extends `SemilatticeInf K`, `Monoid K` and `Star K` with: `star` involutive,
  anti-multiplicative and meet-preserving, composition monotone in both arguments, and the
  **modular law** `(a * b) ⊓ c ≤ (a ⊓ c * star b) * b`.  Monotonicity of composition is
  exported as Mathlib's `MulLeftMono`/`MulRightMono`, so the usual `mul_le_mul_right`,
  `mul_le_mul_left` and `mul_le_mul'` lemmas apply.

* From the modular law we derive its mirror image (`mul_inf_le_mul_inf`), the Dedekind law
  (`dedekind`), `a ≤ a * star a * a` (`le_mul_star_mul`) and `star 1 = 1` (`star_one`).

* **Relational predicates.**  `Functional f` (Pous' `is_univalent`, `star f * f ≤ 1`),
  `Total f` (`1 ≤ f * star f`), `Injective f` (`f * star f ≤ 1`), `Surjective f`
  (`1 ≤ star f * f`) and `IsMap f` (functional and total).  Converse exchanges functional with
  injective and total with surjective, each class is closed under composition, and functional
  elements distribute over meets on the left (`Functional.mul_inf`).

* **Models.**  Every `RelationAlgebra` (from `RelationAlgebra.Converse`) is an allegory, hence
  so is `SetRel α α`; `SetRel.functional_iff`, `SetRel.total_iff`, `SetRel.injective_iff` and
  `SetRel.surjective_iff` identify the abstract predicates with the expected pointwise
  statements about binary relations.

## A word of warning on `Functional` versus `Injective`

The exchange `(f * a) ⊓ b = f * (a ⊓ star f * b)` requires `f` to be **injective**, not
functional: in `SetRel`, with `f = {(1, y), (2, y)}` (which is functional), `a = {(y, z)}` and
`b = {(2, z)}`, the left-hand side is `{(2, z)}` while the right-hand side is `{(1, z), (2, z)}`.
The statement for a *functional* `f` is the mirror one, `(a * f) ⊓ b = (a ⊓ b * star f) * f`.
Both are proved below (`Injective.mul_inf_eq`, `Functional.inf_mul_eq`).

## References

* [P. Freyd and A. Scedrov, *Categories, Allegories*, North-Holland (1990)]
* [A. Tarski, *On the calculus of relations*, J. Symb. Logic 6 (1941)]
* [B. Jónsson and A. Tarski, *Boolean algebras with operators II*, Amer. J. Math. 74 (1952)]
* [D. Pous, *Relation Algebra and KAT in Coq*, <https://github.com/damien-pous/relation-algebra>],
  files `theories/monoid.v` and `theories/relalg.v`
-/

/-- An **allegory** (Freyd–Scedrov): a monoid on a meet-semilattice, equipped with an
involutive, anti-multiplicative and meet-preserving converse `star`, whose composition is
monotone and satisfies the *modular law* `(a * b) ⊓ c ≤ (a ⊓ c * star b) * b`.

This is the fragment of relation algebra that remains after forgetting joins, complements and
the Kleene star. -/
class Allegory (K : Type*) extends SemilatticeInf K, Monoid K, Star K where
  /-- Converse is an involution. -/
  star_involutive : Function.Involutive (star : K → K)
  /-- Converse reverses composition. -/
  star_mul (a b : K) : star (a * b) = star b * star a
  /-- Converse preserves intersections. -/
  star_inf (a b : K) : star (a ⊓ b) = star a ⊓ star b
  /-- Composition is monotone in its left argument. -/
  protected mul_mono_left {a b : K} (h : a ≤ b) (c : K) : a * c ≤ b * c
  /-- Composition is monotone in its right argument. -/
  protected mul_mono_right {a b : K} (h : a ≤ b) (c : K) : c * a ≤ c * b
  /-- The modular law. -/
  modular (a b c : K) : (a * b) ⊓ c ≤ (a ⊓ c * star b) * b

namespace Allegory

variable {K : Type*} [Allegory K] {a b c f g : K}

/-- Composition is monotone in its right argument. -/
instance (priority := 100) toMulLeftMono : MulLeftMono K :=
  ⟨fun a _ _ h ↦ Allegory.mul_mono_right h a⟩

/-- Composition is monotone in its left argument. -/
instance (priority := 100) toMulRightMono : MulRightMono K :=
  ⟨fun a _ _ h ↦ Allegory.mul_mono_left h a⟩

/-! ### Converse -/

@[simp] theorem star_star (a : K) : star (star a) = a := star_involutive a

/-- Converse is monotone: it preserves intersections, hence the order. -/
theorem star_mono : Monotone (star : K → K) := fun _ _ h ↦ by
  rw [← inf_eq_left, ← star_inf, inf_eq_left.2 h]

@[simp] theorem star_le_star_iff : star a ≤ star b ↔ a ≤ b :=
  ⟨fun h ↦ by simpa using star_mono h, fun h ↦ star_mono h⟩

theorem star_le_iff : star a ≤ b ↔ a ≤ star b := by rw [← star_le_star_iff, star_star]

theorem le_star_iff : a ≤ star b ↔ star a ≤ b := star_le_iff.symm

/-- Converse is an order isomorphism, so it is injective. -/
theorem star_injective : Function.Injective (star : K → K) := star_involutive.injective

@[simp] theorem star_inj : star a = star b ↔ a = b := star_injective.eq_iff

/-! ### The modular laws -/

/-- The mirror image of the modular law: `(a * b) ⊓ c ≤ a * (b ⊓ star a * c)`.  It is obtained
by applying converse to the modular law for the converses. -/
theorem mul_inf_le_mul_inf (a b c : K) : (a * b) ⊓ c ≤ a * (b ⊓ star a * c) := by
  have h := star_mono (modular (star b) (star a) (star c))
  have hl : star ((star b * star a) ⊓ star c) = (a * b) ⊓ c := by
    simp only [star_inf, star_mul, star_star]
  have hr : star ((star b ⊓ star c * star (star a)) * star a) = a * (b ⊓ star a * c) := by
    simp only [star_inf, star_mul, star_star]
  rwa [hl, hr] at h

/-- The modular law, restated with the name used in `RelationAlgebra.Converse`. -/
theorem mul_inf_le_inf_mul (a b c : K) : (a * b) ⊓ c ≤ (a ⊓ c * star b) * b := modular a b c

/-- The **Dedekind law** `(a * b) ⊓ c ≤ (a ⊓ c * star b) * (b ⊓ star a * c)`, derived from the
two modular laws. -/
theorem dedekind (a b c : K) : (a * b) ⊓ c ≤ (a ⊓ c * star b) * (b ⊓ star a * c) :=
  calc (a * b) ⊓ c ≤ ((a ⊓ c * star b) * b) ⊓ c := le_inf (modular a b c) inf_le_right
    _ ≤ (a ⊓ c * star b) * (b ⊓ star (a ⊓ c * star b) * c) := mul_inf_le_mul_inf _ _ _
    _ ≤ (a ⊓ c * star b) * (b ⊓ star a * c) :=
        mul_le_mul_right (inf_le_inf_left _ (mul_le_mul_left (star_mono inf_le_left) _)) _

/-- Every element is "partially reflexive": `a ≤ a * star a * a`. -/
theorem le_mul_star_mul (a : K) : a ≤ a * star a * a :=
  calc a = (a * 1) ⊓ a := by rw [mul_one, inf_idem]
    _ ≤ a * (1 ⊓ star a * a) := mul_inf_le_mul_inf a 1 a
    _ ≤ a * (star a * a) := mul_le_mul_right inf_le_right _
    _ = a * star a * a := (mul_assoc _ _ _).symm

/-- The converse of the unit is the unit. -/
@[simp] theorem star_one : star (1 : K) = 1 := by
  refine le_antisymm ?_ ?_
  · have h : (1 : K) ≤ star 1 := by simpa using le_mul_star_mul (1 : K)
    simpa using star_mono h
  · simpa using le_mul_star_mul (1 : K)

/-! ### Functional, total, injective and surjective elements

These are Pous' `is_univalent`, `is_total`, `is_injective` and `is_surjective`. -/

/-- `f` is **functional** (Pous' *univalent*): `star f * f ≤ 1`.  In the relational model this
says that `f` is a partial function. -/
def Functional (f : K) : Prop := star f * f ≤ 1

/-- `f` is **total**: `1 ≤ f * star f`.  In the relational model this says that every point has
at least one image. -/
def Total (f : K) : Prop := 1 ≤ f * star f

/-- `f` is **injective**: `f * star f ≤ 1`.  In the relational model this says that every point
has at most one preimage. -/
def Injective (f : K) : Prop := f * star f ≤ 1

/-- `f` is **surjective**: `1 ≤ star f * f`.  In the relational model this says that every
point has at least one preimage. -/
def Surjective (f : K) : Prop := 1 ≤ star f * f

/-- `f` is a **map** (Pous' `is_mapping`) when it is functional and total, i.e. a total
function in the relational model. -/
structure IsMap (f : K) : Prop where
  /-- A map is functional. -/
  functional : Functional f
  /-- A map is total. -/
  total : Total f

/-! #### Converse exchanges the four predicates -/

@[simp] theorem functional_star_iff : Functional (star f) ↔ Injective f := by
  simp only [Functional, Injective, star_star]

@[simp] theorem injective_star_iff : Injective (star f) ↔ Functional f := by
  simp only [Functional, Injective, star_star]

@[simp] theorem total_star_iff : Total (star f) ↔ Surjective f := by
  simp only [Total, Surjective, star_star]

@[simp] theorem surjective_star_iff : Surjective (star f) ↔ Total f := by
  simp only [Total, Surjective, star_star]

theorem Functional.injective_star (h : Functional f) : Injective (star f) :=
  injective_star_iff.2 h

theorem Injective.functional_star (h : Injective f) : Functional (star f) :=
  functional_star_iff.2 h

theorem Total.surjective_star (h : Total f) : Surjective (star f) := surjective_star_iff.2 h

theorem Surjective.total_star (h : Surjective f) : Total (star f) := total_star_iff.2 h

/-! #### The unit, and closure under composition -/

theorem functional_one : Functional (1 : K) := by simp [Functional]

theorem total_one : Total (1 : K) := by simp [Total]

theorem injective_one : Injective (1 : K) := by simp [Injective]

theorem surjective_one : Surjective (1 : K) := by simp [Surjective]

theorem isMap_one : IsMap (1 : K) := ⟨functional_one, total_one⟩

theorem Functional.mul (hf : Functional f) (hg : Functional g) : Functional (f * g) :=
  calc star (f * g) * (f * g) = star g * (star f * f) * g := by
        rw [star_mul]; simp only [mul_assoc]
    _ ≤ star g * 1 * g := mul_le_mul_left (mul_le_mul_right hf _) _
    _ = star g * g := by rw [mul_one]
    _ ≤ 1 := hg

theorem Injective.mul (hf : Injective f) (hg : Injective g) : Injective (f * g) :=
  calc (f * g) * star (f * g) = f * (g * star g) * star f := by
        rw [star_mul]; simp only [mul_assoc]
    _ ≤ f * 1 * star f := mul_le_mul_left (mul_le_mul_right hg _) _
    _ = f * star f := by rw [mul_one]
    _ ≤ 1 := hf

theorem Total.mul (hf : Total f) (hg : Total g) : Total (f * g) :=
  calc (1 : K) ≤ f * star f := hf
    _ = f * 1 * star f := by rw [mul_one]
    _ ≤ f * (g * star g) * star f := mul_le_mul_left (mul_le_mul_right hg _) _
    _ = (f * g) * star (f * g) := by rw [star_mul]; simp only [mul_assoc]

theorem Surjective.mul (hf : Surjective f) (hg : Surjective g) : Surjective (f * g) :=
  calc (1 : K) ≤ star g * g := hg
    _ = star g * 1 * g := by rw [mul_one]
    _ ≤ star g * (star f * f) * g := mul_le_mul_left (mul_le_mul_right hf _) _
    _ = star (f * g) * (f * g) := by rw [star_mul]; simp only [mul_assoc]

theorem IsMap.mul (hf : IsMap f) (hg : IsMap g) : IsMap (f * g) :=
  ⟨hf.functional.mul hg.functional, hf.total.mul hg.total⟩

/-! #### Distribution over intersections -/

/-- A functional element distributes over intersections on the left (Pous'
`dot_univalent_cap`). -/
theorem Functional.mul_inf (hf : Functional f) (a b : K) : f * (a ⊓ b) = f * a ⊓ f * b := by
  refine le_antisymm (le_inf (mul_le_mul_right inf_le_left _) (mul_le_mul_right inf_le_right _)) ?_
  calc f * a ⊓ f * b ≤ f * (a ⊓ star f * (f * b)) := mul_inf_le_mul_inf f a (f * b)
    _ = f * (a ⊓ star f * f * b) := by rw [mul_assoc]
    _ ≤ f * (a ⊓ 1 * b) := mul_le_mul_right (inf_le_inf_left _ (mul_le_mul_left hf _)) _
    _ = f * (a ⊓ b) := by rw [one_mul]

/-- An injective element distributes over intersections on the right. -/
theorem Injective.inf_mul (hf : Injective f) (a b : K) : (a ⊓ b) * f = a * f ⊓ b * f := by
  refine le_antisymm (le_inf (mul_le_mul_left inf_le_left _) (mul_le_mul_left inf_le_right _)) ?_
  calc a * f ⊓ b * f ≤ (a ⊓ b * f * star f) * f := mul_inf_le_inf_mul a f (b * f)
    _ = (a ⊓ b * (f * star f)) * f := by rw [mul_assoc]
    _ ≤ (a ⊓ b * 1) * f := mul_le_mul_left (inf_le_inf_left _ (mul_le_mul_right hf _)) _
    _ = (a ⊓ b) * f := by rw [mul_one]

/-- Exchange law for an **injective** `f`: `(f * a) ⊓ b = f * (a ⊓ star f * b)`.  The inequality
`≤` is the modular law and holds in any allegory; injectivity is what makes `≥` true (see the
counterexample in the module docstring). -/
theorem Injective.mul_inf_eq (hf : Injective f) (a b : K) :
    (f * a) ⊓ b = f * (a ⊓ star f * b) := by
  refine le_antisymm (mul_inf_le_mul_inf f a b) (le_inf (mul_le_mul_right inf_le_left _) ?_)
  calc f * (a ⊓ star f * b) ≤ f * (star f * b) := mul_le_mul_right inf_le_right _
    _ = f * star f * b := (mul_assoc _ _ _).symm
    _ ≤ 1 * b := mul_le_mul_left hf _
    _ = b := one_mul b

/-- Exchange law for a **functional** `f`: `(a * f) ⊓ b = (a ⊓ b * star f) * f`. -/
theorem Functional.inf_mul_eq (hf : Functional f) (a b : K) :
    (a * f) ⊓ b = (a ⊓ b * star f) * f := by
  refine le_antisymm (mul_inf_le_inf_mul a f b) (le_inf (mul_le_mul_left inf_le_left _) ?_)
  calc (a ⊓ b * star f) * f ≤ (b * star f) * f := mul_le_mul_left inf_le_right _
    _ = b * (star f * f) := mul_assoc _ _ _
    _ ≤ b * 1 := mul_le_mul_right hf _
    _ = b := mul_one b

end Allegory

/-! ### Relation algebras are allegories -/

/-- Every relation algebra is an allegory: forget joins, complements and the Kleene star, and
keep the left modular law derived from the Dedekind law. -/
instance (priority := 100) RelationAlgebra.toAllegory {K : Type*} [RelationAlgebra K] :
    Allegory K where
  __ := (inferInstance : SemilatticeInf K)
  __ := (inferInstance : Monoid K)
  __ := (inferInstance : Star K)
  star_involutive := RelationAlgebra.star_involutive
  star_mul := RelationAlgebra.star_mul
  star_inf := RelationAlgebra.star_inf
  mul_mono_left h c := mul_le_mul_left h c
  mul_mono_right h c := mul_le_mul_right h c
  modular := RelationAlgebra.mul_inf_le_inf_mul

/-! ### The relational model -/

namespace SetRel

variable {α : Type*} {R : SetRel α α}

/-- Binary relations form an allegory; the instance comes from `SetRel.instRelationAlgebra`. -/
example : Allegory (SetRel α α) := inferInstance

/-- `R` is functional exactly when it is a partial function. -/
theorem functional_iff : Allegory.Functional R ↔ ∀ a b c, a ~[R] b → a ~[R] c → b = c := by
  constructor
  · rintro h a b c hab hac
    exact h (a := (b, c)) ⟨a, hab, hac⟩
  · rintro h ⟨b, c⟩ ⟨a, hab, hac⟩
    exact h a b c hab hac

/-- `R` is total exactly when every point has an image. -/
theorem total_iff : Allegory.Total R ↔ ∀ a, ∃ b, a ~[R] b := by
  constructor
  · rintro h a
    obtain ⟨b, hab, -⟩ := h (a := (a, a)) rfl
    exact ⟨b, hab⟩
  · rintro h ⟨a, a'⟩ (haa : a = a')
    obtain ⟨b, hab⟩ := h a
    exact ⟨b, hab, haa ▸ hab⟩

/-- `R` is injective exactly when every point has at most one preimage. -/
theorem injective_iff : Allegory.Injective R ↔ ∀ a b c, a ~[R] c → b ~[R] c → a = b := by
  constructor
  · rintro h a b c hac hbc
    exact h (a := (a, b)) ⟨c, hac, hbc⟩
  · rintro h ⟨a, b⟩ ⟨c, hac, hbc⟩
    exact h a b c hac hbc

/-- `R` is surjective exactly when every point has a preimage. -/
theorem surjective_iff : Allegory.Surjective R ↔ ∀ b, ∃ a, a ~[R] b := by
  constructor
  · rintro h b
    obtain ⟨a, hab, -⟩ := h (a := (b, b)) rfl
    exact ⟨a, hab⟩
  · rintro h ⟨b, b'⟩ (hbb : b = b')
    obtain ⟨a, hab⟩ := h b
    exact ⟨a, hab, hbb ▸ hab⟩

/-- `R` is a map exactly when it is the graph of a function. -/
theorem isMap_iff : Allegory.IsMap R ↔ ∀ a, ∃! b, a ~[R] b := by
  constructor
  · rintro ⟨hf, ht⟩ a
    obtain ⟨b, hab⟩ := total_iff.1 ht a
    exact ⟨b, hab, fun c hac ↦ functional_iff.1 hf a c b hac hab⟩
  · intro h
    refine ⟨functional_iff.2 fun a b c hab hac ↦ ?_, total_iff.2 fun a ↦ ?_⟩
    · obtain ⟨d, -, hd⟩ := h a
      rw [hd b hab, hd c hac]
    · exact ⟨(h a).choose, (h a).choose_spec.1⟩

end SetRel
