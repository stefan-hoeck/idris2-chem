module Text.Molfile.Writer

import Data.String
import Data.Vect
import Text.Molfile.Float
import Text.Molfile.Types

%default total

%inline
Interpolation Nat where interpolate = show

export
fill : Interpolation a => Nat -> a -> String
fill n = padLeft n ' ' . interpolate

export
counts : Counts -> String
counts (MkCounts na nb c v) =
  fastConcat [fill 3 na, fill 3 nb, fill 6 c, fill 27 v]

coords : Vect 3 Coordinate -> String
coords [x,y,z] = fastConcat [fill 10 x, fill 10 y, fill 10 z]

||| General format:
|||   xxxxx.xxxxyyyyy.yyyyzzzzz.zzzz aaaddcccssshhhbbbvvvHHHrrriiimmmnnneee
export
atom : Atom -> String
atom (MkAtom cs a d c s h b v h0 m n e) =
  fastConcat
    [ coords cs, fill 4 a, fill 2 d, fill 3 c, fill 3 s, fill 3 h
    , fill 3 b, fill 3 v, fill 3 h0, fill 9 m, fill 3 n, fill 3 e]

||| General format:
|||   111222tttsssxxxrrrccc
export
bond : Bond -> String
bond (MkBond a1 a2 t s r c) =
  fastConcat [ fill 3 a1, fill 3 a2, fill 3 t, fill 3 s, fill 6 r, fill 3 c]
