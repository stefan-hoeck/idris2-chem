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

[IP_ISO] Interpolation Isotope where
  interpolate (MkI H $ Just 2) = "D"
  interpolate (MkI H $ Just 3) = "T"
  interpolate (MkI e _)        = symbol e

||| General format:
|||   xxxxx.xxxxyyyyy.yyyyzzzzz.zzzz aaaddcccssshhhbbbvvvHHHrrriiimmmnnneee
export
atom : MolAtom -> String
atom (MkAtom a c pos _ () () () ()) =
  fastConcat [ coords pos, fill @{IP_ISO} 4 a, fill 5 c]

||| General format:
|||   111222tttsssxxxrrrccc
export
bond : Edge k MolBond -> String
bond (E x y $ MkBond True t s) =
 fastConcat [ fill 3 x, fill 3 y, fill 3 t, fill 3 s]
bond (E x y $ MkBond False t s) =
 fastConcat [ fill 3 y, fill 3 x, fill 3 t, fill 3 s]

export
writeMol : Molfile -> String
writeMol (MkMolfile n i c $ G o g) =
  let es := map bond (edges g)
      as := foldr (\a,ls => atom a.label :: ls) es g.graph
      cs := MkCounts o (length es) NonChiral V2000
   in fastUnlines $
      n.value :: i.value :: c.value :: counts cs :: as ++ ["M  END"]
