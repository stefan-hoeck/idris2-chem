module Text.Molfile.Writer

import Chem
import Data.String
import Data.Vect
import Text.Molfile.Types

%default total

%inline
Interpolation Nat where interpolate = show

%inline
Interpolation (Fin n) where interpolate = show . S . finToNat

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
atom (MkAtom cs a _ c s h b v h0) =
  fastConcat
    [ coords cs, fill 4 a, fill 5 c, fill 3 s, fill 3 h
    , fill 3 b, fill 3 v, fill 3 h0]

||| General format:
|||   111222tttsssxxxrrrccc
export
bond : Edge k Bond -> String
bond (E x y $ MkBond True t s r) =
 fastConcat [ fill 3 x, fill 3 y, fill 3 t, fill 3 s, fill 6 r]
bond (E x y $ MkBond False t s r) =
 fastConcat [ fill 3 y, fill 3 x, fill 3 t, fill 3 s, fill 6 r]
