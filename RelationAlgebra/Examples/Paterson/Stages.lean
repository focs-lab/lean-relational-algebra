import RelationAlgebra.Examples.Paterson.Programs

/-! # Intermediate flowcharts in the Paterson proof

The numbering follows the equations in Angus and Kozen (2001), §5, as used in
Pous's proof. These are syntax, without any semantic assumptions.
-/
open scoped Computability
namespace Paterson.Stages
open Programs
local notation "⟪" b "⟫" => Prog.test b
local infixl:70 " & " => BExpr.and
local prefix:max "~" => BExpr.not

/-- The expression at equation 19. -/
def s19 : Prog :=
  x1 * p41 * p11 * q214 * q311 *
   (⟪~a1 & ~a4⟫ * p11 * q214 * q311 + ⟪~a1 & a4⟫ * p11 * q214 * q311 +
    ⟪a1 & ~a4⟫ * p13 * ⟪~a4⟫ * q214 * q311 +
    ⟪a1 & a4⟫ * p13 * (⟪~a2⟫ * p22)∗ * ⟪a2 & ~a3⟫ * p41 * p11 * q214 * q311)∗ *
   ⟪a1⟫ * p13 * (⟪~a2⟫ * p22)∗ * ⟪a2 & a3 & a4⟫ * z2

/-- The expression at equation 23. -/
def s23 : Prog :=
  x1 * p41 * p11 * q214 * q311 *
   (⟪~a1 & ~a4⟫ * p11 * q214 * q311 + ⟪~a1 & a4⟫ * p11 * q214 * q311 +
    ⟪a1 & ~a4⟫ * p13 * ⟪~a4⟫ * q214 * q311 +
    ⟪a1 & a4⟫ * p13 * (⟪~a2⟫ * p22)∗ * ⟪a2 & ~a3⟫ * p41 * p11 * q214 * q311)∗ *
   (⟪~a2⟫ * p22)∗ * ⟪a1 & a2 & a3 & a4⟫ * z2

/-- The expression at equation 24. -/
def s24 : Prog :=
  x1 * p41 * p11 * q214 * q311 *
   (⟪a1 & a4⟫ * p13 * (⟪~a2⟫ * p22)∗ * ⟪a2 & ~a3⟫ * p41 * p11 * q214 * q311)∗ *
   (⟪~a2⟫ * p22)∗ * ⟪a1 & a2 & a3 & a4⟫ * z2

/-- The expression at equation 27. -/
def s27 : Prog :=
  x1 * p41 * p11 * q211 * q311 *
   (⟪a1 & a4⟫ * p13 * (⟪~a2⟫ * p22)∗ * ⟪a2 & ~a3⟫ * p41 * p11 * q211 * q311)∗ *
   (⟪~a2⟫ * p22)∗ * ⟪a1 & a2 & a3 & a4⟫ * z2

/-- The expression at equation 29. -/
def s29 : Prog :=
  x1 * (p41 * (p11 * q211 * q311 * ⟪a1⟫ * p13 * (⟪~a2⟫ * p22)∗ * ⟪a2 & ~a3⟫))∗ *
   p41 * p11 * q211 * q311 * (⟪~a2⟫ * p22)∗ * ⟪a1 & a2 & a3⟫ * z2

/-- The expression at equation 31. -/
def s31 : Prog :=
  x1 * (p11 * q211 * q311 * ⟪a1⟫ * p13 * (⟪~a2⟫ * p22)∗ * ⟪a2 & ~a3⟫)∗ *
   p11 * q211 * q311 * (⟪~a2⟫ * p22)∗ * ⟪a1 & a2 & a3⟫ * z2

/-- The expression at equation 32. -/
def s32 : Prog :=
  (x1 * p11) * (q211 * q311 * (⟪~a2⟫ * p22)∗ * ⟪a1 & a2 & ~a3⟫ * (p13 * p11))∗ *
   q211 * q311 * (⟪~a2⟫ * p22)∗ * ⟪a1 & a2 & a3⟫ * z2

/-- The expression at equation 33. -/
def s33 : Prog :=
  s1 * (q211 * q311 * (⟪~a2⟫ * p22)∗ * ⟪a1 & a2 & ~a3⟫ * r13)∗ *
   q211 * q311 * (⟪~a2⟫ * p22)∗ * ⟪a1 & a2 & a3⟫ * z2

/-- The expression at equation 34. -/
def s34 : Prog :=
  s1 * (⟪a1⟫ * (q211 * q311 * r13) * (⟪~a2⟫ * p22)∗ * ⟪a2 & ~a3⟫)∗ *
   q211 * q311 * (⟪~a2⟫ * p22)∗ * ⟪a1 & a2 & a3⟫ * z2

/-- The expression at equation 35. -/
def s35 : Prog :=
  s1 * (⟪a1⟫ * (q211 * q311 * r12) * (⟪~a2⟫ * p22)∗ * ⟪a2 & ~a3⟫)∗ *
   q211 * q311 * (⟪~a2⟫ * p22)∗ * ⟪a1 & a2 & a3⟫ * z2

/-- The expression at equation 36. -/
def s36 : Prog :=
  s1 * (⟪a1⟫ * (q211 * q311) * ⟪~a2⟫ * r12 * (⟪~a2⟫ * p22)∗ * ⟪a2⟫)∗ *
   (q211 * q311) * ⟪a2⟫ * (⟪~a2⟫ * p22)∗ * ⟪a1 & a2⟫ * z2

/-- The expression at equation 37. -/
def s37 : Prog :=
  s1 * (⟪a1⟫ * q211 * ⟪~a2⟫ * r12 * (⟪~a2⟫ * p22)∗ * ⟪a2⟫)∗ *
   q211 * ⟪a2⟫ * (⟪~a2⟫ * p22)∗ * ⟪a1 & a2⟫ * z2

/-- The expression at equation 38. -/
def s38 : Prog :=
  s1 * ⟪a1⟫ * q211 * (⟪~a2⟫ * r12 * ⟪a1⟫ * p22 * ⟪a2⟫ * q211 +
   ⟪~a2⟫ * r12 * ⟪a1⟫ * p22 * ⟪~a2⟫ * (p22 * q211))∗ * ⟪a2⟫ * z2

/-- The expression at equation 43. -/
def s43 : Prog :=
  s1 * ⟪a1⟫ * q211 * (⟪~a2⟫ * r12 * ⟪a1⟫ * q211)∗ * ⟪a2⟫ * z2


/-- The equation 29 expression before clearing its temporary cells. -/
abbrev body29 : Prog :=
  x1 * (p41 * (p11 * q211 * q311 * ⟪a1⟫ * p13 * (⟪~a2⟫ * p22)∗ * ⟪a2 & ~a3⟫))∗ *
   p41 * p11 * q211 * q311 * (⟪~a2⟫ * p22)∗ * ⟪a1 & a2 & a3⟫ * (.assign Loc.io (.var Loc.y2))

/-- The equation 36 expression before clearing its temporary cells. -/
abbrev body36 : Prog :=
  s1 * (⟪a1⟫ * (q211 * q311) * ⟪~a2⟫ * r12 * (⟪~a2⟫ * p22)∗ * ⟪a2⟫)∗ *
   (q211 * q311) * ⟪a2⟫ * (⟪~a2⟫ * p22)∗ * ⟪a1 & a2⟫ * (.assign Loc.io (.var Loc.y2))

/-- The final substituted expression, before clearing the temporary cells. -/
abbrev body44 : Prog :=
  ⟪bInit⟫ * s1 * qInit * (⟪~a2⟫ * ⟪bNext⟫ * r12 * qNext)∗ * ⟪a2⟫ * (.assign Loc.io (.var Loc.y2))

/-- Equation 44 after substituting away all reads of `y1`. -/
def s44 : Prog := body44 * clr

/-- The common expression after eliminating `y1`, still with the common cleanup. -/
def common : Prog := ⟪bInit⟫ * qInit * (⟪~a2⟫ * ⟪bNext⟫ * qNext)∗ * ⟪a2⟫ * z2

end Paterson.Stages
