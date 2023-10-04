module Text.Molfile.Writer

import Chem
import Data.String
import Data.Vect
import Text.Molfile.Types

%default total

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

%inline
Interpolation Nat where interpolate = show

%inline
Interpolation (Fin n) where interpolate = show . S . finToNat

Interpolation Radical where
  interpolate NoRadical = "0"
  interpolate Singlet   = "1"
  interpolate Doublet   = "2"
  interpolate Triplet   = "3"

[IP_ISO] Interpolation Isotope where
  interpolate (MkI H $ Just 2) = "D"
  interpolate (MkI H $ Just 3) = "T"
  interpolate (MkI e _)        = symbol e

export
fill : Interpolation a => Nat -> a -> String
fill n = padLeft n ' ' . interpolate

--------------------------------------------------------------------------------
--          Properties
--------------------------------------------------------------------------------

record Props (k : Nat) where
  constructor P
  isos     : List String
  charges  : List String
  radicals : List String


grouped : (n : Nat) -> (0 p : IsSucc n) => List a -> List (List a)
grouped _     []      = []
grouped (S m) (x::xs) = go [<] [<x] m xs
  where
    go : SnocList (List a) -> SnocList a -> Nat -> List a -> List (List a)
    go sxs sx c     []        = sxs <>> [sx <>> []]
    go sxs sx 0     (x :: xs) = go (sxs :< (sx <>> [])) [<x] m xs
    go sxs sx (S k) (x :: xs) = go sxs (sx :< x) k xs

dispGroup : String -> List String -> String
dispGroup pre vs = fastConcat $ pre :: fill 3 (length vs) :: vs

props : Props k -> List String
props (P is cs rs) =
  map (dispGroup "M  ISO") (grouped 8 is) ++
  map (dispGroup "M  CHG") (grouped 8 cs) ++
  map (dispGroup "M  RAD") (grouped 8 rs)


--------------------------------------------------------------------------------
--          Writer
--------------------------------------------------------------------------------

export
counts : Counts -> String
counts (MkCounts na nb c v) =
  fastConcat [fill 3 na, fill 3 nb, fill 6 c, fill 27 v]

coords : Vect 3 Coordinate -> String
coords [x,y,z] = fastConcat [fill 10 x, fill 10 y, fill 10 z]

%inline
prependNonEmpty : String -> List String -> List String
prependNonEmpty "" = id
prependNonEmpty s  = (s::)

adjProps :
     Fin k
  -> Adj k b (Atom Isotope Charge Coordinates Radical h t c l)
  -> Props k
  -> Props k
adjProps n (A a _) p =
  let ns := fill 4 n
      i  := maybe "" (\m => ns ++ fill 4 m) a.elem.mass
      c  := if a.charge == 0 then "" else ns ++ fill 4 a.charge
      r  := if a.radical == NoRadical then "" else ns ++ fill 4 a.radical

   in { isos     $= prependNonEmpty i
      , charges  $= prependNonEmpty c
      , radicals $= prependNonEmpty r
      } p

||| General format:
|||   xxxxx.xxxxyyyyy.yyyyzzzzz.zzzz aaaddcccssshhhbbbvvvHHHrrriiimmmnnneee
export
atom : Atom Isotope Charge Coordinates Radical h t c l -> String
atom (MkAtom a c pos _ _ _ _ _) = fastConcat [ coords pos, fill @{IP_ISO} 4 a]

||| General format:
|||   111222tttsssxxxrrrccc
export
bond : Edge k MolBond -> String
bond (E x y $ MkBond True t s) =
 fastConcat [ fill 3 x, fill 3 y, fill 3 t, fill 3 s]
bond (E x y $ MkBond False t s) =
 fastConcat [ fill 3 y, fill 3 x, fill 3 t, fill 3 s]

export
writeMol :
     (name, info, comment : MolLine)
  -> Graph MolBond (Atom Isotope Charge Coordinates Radical h t c l)
  -> String
writeMol n i c (G o g) =
  let ps := props $ foldrKV adjProps (P [] [] []) g.graph
      es := map bond (edges g)
      as := foldr (\a,ls => atom a.label :: ls) (es ++ ps) g.graph
      cs := MkCounts o (length es) NonChiral V2000
   in fastUnlines $
      n.value :: i.value :: c.value :: counts cs :: as ++ ["M  END"]

export %inline
writeMolfile : Molfile -> String
writeMolfile (MkMolfile n i c g) = writeMol n i c g
