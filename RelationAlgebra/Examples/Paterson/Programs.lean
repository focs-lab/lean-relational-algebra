import RelationAlgebra.Examples.Paterson.Model

/-! # The two Paterson flowchart schemes

These are the expressions in the statement of Damien Pous's `Paterson` theorem.
The names follow Angus and Kozen's equations (19)–(47). `io` is the shared input/output
cell; `y1`–`y4` are cleared on successful termination.
-/
open scoped Computability SetRel KAT
namespace Paterson

namespace Prog
instance : Mul Prog := ⟨seq⟩
instance : Add Prog := ⟨choice⟩
instance : KStar Prog := ⟨star⟩
end Prog

namespace Programs
open Loc
local notation "⟪" b "⟫" => Prog.test b
local infixl:70 " & " => BExpr.and
local prefix:max "~" => BExpr.not

abbrev a1 : BExpr := .pred (.var y1)
abbrev a2 : BExpr := .pred (.var y2)
abbrev a3 : BExpr := .pred (.var y3)
abbrev a4 : BExpr := .pred (.var y4)
abbrev del (y : Loc) : Prog := .assign y .zero
abbrev clr : Prog := del y1 * del y2 * del y3 * del y4
abbrev x1 : Prog := .assign y1 (.var io)
abbrev s1 : Prog := .assign y1 (.f (.var io))
abbrev s2 : Prog := .assign y2 (.f (.var io))
abbrev z1 : Prog := .assign io (.var y1) * clr
abbrev z2 : Prog := .assign io (.var y2) * clr
abbrev p11 : Prog := .assign y1 (.f (.var y1))
abbrev p13 : Prog := .assign y1 (.f (.var y3))
abbrev p22 : Prog := .assign y2 (.f (.var y2))
abbrev p41 : Prog := .assign y4 (.f (.var y1))
abbrev q222 : Prog := .assign y2 (.g (.var y2) (.var y2))
abbrev q214 : Prog := .assign y2 (.g (.var y1) (.var y4))
abbrev q211 : Prog := .assign y2 (.g (.var y1) (.var y1))
abbrev q311 : Prog := .assign y3 (.g (.var y1) (.var y1))
abbrev r11 : Prog := .assign y1 (.f (.f (.var y1)))
abbrev r12 : Prog := .assign y1 (.f (.f (.var y2)))
abbrev r13 : Prog := .assign y1 (.f (.f (.var y3)))
abbrev r22 : Prog := .assign y2 (.f (.f (.var y2)))

/-- Initial test after substituting the input assignment. -/
abbrev bInit : BExpr := .pred (.f (.var io))
/-- Loop test after substituting the two applications of `f`. -/
abbrev bNext : BExpr := .pred (.f (.f (.var y2)))
/-- Initial assignment after propagating the value of `f(io)`. -/
abbrev qInit : Prog := .assign y2 (.g (.f (.var io)) (.f (.var io)))
/-- Loop assignment after propagating the value of `f(f(y2))`. -/
abbrev qNext : Prog := .assign y2 (.g (.f (.f (.var y2))) (.f (.f (.var y2))))

/-- Paterson's larger flowchart, S6A. -/
def s6a : Prog :=
  x1 * p41 * p11 * q214 * q311 * (⟪~a1⟫ * p11 * q214 * q311)∗ * ⟪a1⟫ * p13 *
    ((⟪~a4⟫ + ⟪a4⟫ * (⟪~a2⟫ * p22)∗ * ⟪a2 & ~a3⟫ * p41 * p11) * q214 * q311 *
      (⟪~a1⟫ * p11 * q214 * q311)∗ * ⟪a1⟫ * p13)∗ *
    ⟪a4⟫ * (⟪~a2⟫ * p22)∗ * ⟪a2 & a3⟫ * z2

/-- The equivalent one-work-variable scheme, S6E. -/
def s6e : Prog := s2 * ⟪a2⟫ * q222 * (⟪~a2⟫ * r22 * ⟪a2⟫ * q222)∗ * ⟪a2⟫ * z2

end Programs
end Paterson
