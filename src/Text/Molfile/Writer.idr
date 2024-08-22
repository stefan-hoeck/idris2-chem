module Text.Molfile.Writer

import Chem
import Data.SortedMap
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

0 GroupMap : Nat -> Type
GroupMap k = SortedMap Nat (String, SnocList $ Fin k)


record Props (k : Nat) where
  constructor P
  isos     : List String
  charges  : List String
  radicals : List String
  abbr     : GroupMap k

dispGroup : String -> List String -> String
dispGroup pre vs = fastConcat $ pre :: fill 3 (length vs) :: vs

abbreviations : List (String,String,List String) -> List String
abbreviations ls =
  map (dispGroup "M  STY" . map (\(x,_) => x ++ " SUP")) (grouped 8 ls) ++
  map (\(x,y,_) => "M  SMT\{x} \{y}") ls ++
  (ls >>= \(x,_,vs) => map (dispGroup "M  SAL\{x}") (grouped 15 vs))

dispGrp : (Nat,String,SnocList $ Fin k) -> (String,String,List String)
dispGrp (x,y,z) = (fill 4 x, y, map (fill 4) z <>> [])

props : Props k -> List String
props (P is cs rs abbr) =
  map (dispGroup "M  ISO") (grouped 8 is) ++
  map (dispGroup "M  CHG") (grouped 8 cs) ++
  map (dispGroup "M  RAD") (grouped 8 rs) ++
  abbreviations (dispGrp <$> SortedMap.toList abbr)

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

appendLbl : Maybe AtomGroup -> Fin k -> GroupMap k -> GroupMap k
appendLbl Nothing  _       m = m
appendLbl (Just $ G n l) x m =
  case lookup n m of
    Just (l,sx) => insert n (l, sx :< x) m
    Nothing     => insert n (l, [<x]) m

adjProps :
     Fin k
  -> Adj k b (Atom Isotope Charge Coordinates Radical h t c (Maybe AtomGroup))
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
      , abbr     $= appendLbl a.label n
      } p

%inline atomRem : String
atomRem = " 0  0  0  0  0  0  0  0  0  0  0  0"

%inline bondRem : String
bondRem = "  0  0  0"


||| General format:
|||   xxxxx.xxxxyyyyy.yyyyzzzzz.zzzz aaaddcccssshhhbbbvvvHHHrrriiimmmnnneee
export
atom : Atom Isotope Charge Coordinates Radical h t c l -> String
atom (MkAtom a c pos _ _ _ _ _) =
  fastConcat [ coords pos, fill @{IP_ISO} 4 a, atomRem]

||| General format:
|||   111222tttsssxxxrrrccc
export
bond : Edge k MolBond -> String
bond (E x y $ MkBond True t s) =
 fastConcat [ fill 3 x, fill 3 y, fill 3 t, fill 3 s, bondRem]
bond (E x y $ MkBond False t s) =
 fastConcat [ fill 3 y, fill 3 x, fill 3 t, fill 3 s, bondRem]

groupMap : (0 k : Nat) -> List AtomGroup -> GroupMap k
groupMap _ = SortedMap.fromList . map (\g => (g.nr, (g.lbl, [<])))

export
molLines : (name, info, comment : MolLine) -> MolGraph' h t c -> List String
molLines n i c (G 0 _) = []
molLines n i c (G o g) =
  let ps := props $ foldrKV adjProps (P [] [] [] empty) g.graph
      es := map bond (edges g)
      as := foldr (\a,ls => atom a.label :: ls) (es ++ ps) g.graph
      cs := MkCounts o (length es) NonChiral V2000
   in n.value :: i.value :: c.value :: counts cs :: as ++ ["M  END"]

export %inline
writeMolfile : Molfile' h t c -> String
writeMolfile (MkMolfile n i c g) = unlines $ molLines n i c g
