module Text.Molfile.Parser.V3000

import Syntax.T1
import Text.Molfile.Parser.Stack
import Text.Molfile.Parser.Util

%default total

--------------------------------------------------------------------------------
-- Expressions
--------------------------------------------------------------------------------

||| Recognizes a V3000 version line.
export
v3000 : RExp True
v3000 = star sdigit >> oneof ['V','v'] >> "3000" >> newline

spaces : RExp False
spaces = star ' '

-- the "M  V30" line prefix
mv30 : RExp True
mv30 = "M  V30" >> spaces

||| Recognizes a V3000 `BEGIN` statement
export
beginV3 : RExp True -> RExp True
beginV3 x = mv30 >> "BEGIN" >> spaces >> x >> dots >> newline

||| Recognizes a V3000 `END` statement
export
endV3 : RExp True -> RExp True
endV3 x = mv30 >> "END" >> spaces >> x >> spaces >> newline

export
countsExpr : RExp True
countsExpr = mv30 >> "COUNTS" >> spaces

export
skipLines : Nat -> RExp True -> CST -> (RExp True, Step q CSz CSTCK)

spaced : CST -> Steps q CSz CSTCK -> DFA q CSz CSTCK
spaced x ss = dfa $ conv' (plus ' ') x :: ss
