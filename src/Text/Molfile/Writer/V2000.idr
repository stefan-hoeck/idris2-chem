module Text.Molfile.Writer.V2000

import Data.Linear.Traverse1
import Data.SortedMap
import Data.String
import Data.String.Builder
import Syntax.T1
import Text.Molfile.Types
import Text.Molfile.Writer.Util

%hide Prelude.(>>)

%default total

%inline
Interpolation Nat where interpolate = show

%inline
Interpolation (Fin n) where interpolate = show . S . finToNat

%inline
Interpolation Radical where interpolate = dispRadical

[IP_ISO] Interpolation Isotope where interpolate = dispIso

fill : Interpolation a => Builder q => Nat -> a -> F1' q
fill n = putLeftPadded n ' ' . interpolate

pl : Interpolation a => Nat -> a -> String
pl n = padLeft n ' ' . interpolate

groupMap : List AtomGroup -> GroupMap
groupMap = SortedMap.fromList . map (\g => (g.nr, (g.lbl, [<])))

dispGrp : (Nat,String,SnocList Nat) -> (String,String,List String)
dispGrp (x,y,z) = (pl 4 x, y, map (pl 4) z <>> [])

--------------------------------------------------------------------------------
--          Properties
--------------------------------------------------------------------------------

record Props where
  constructor P
  isos     : List String
  charges  : List String
  radicals : List String
  abbr     : GroupMap

%inline
prependNonEmpty : String -> List String -> List String
prependNonEmpty "" = id
prependNonEmpty s  = (s::)

adjProps : Fin k -> Adj k b (MolAtom' h t c) -> Props -> Props
adjProps n adj@(A a _) p =
  let ns := pl 4 n
      i  := maybe "" (\m => ns ++ pl 4 m) a.elem.mass
      c  := if a.charge == 0 then "" else ns ++ pl 4 a.charge
      r  := if a.radical == NoRadical then "" else ns ++ pl 4 a.radical

   in { isos     $= prependNonEmpty i
      , charges  $= prependNonEmpty c
      , radicals $= prependNonEmpty r
      , abbr     $= appendLbl n adj
      } p

parameters {auto b : Builder q}
  dispGroup : String -> List String -> F1' q
  dispGroup p vs = putText p >> fill 3 (length vs) >> putAll vs >> linebreak

  abbreviations : List (String,String,List String) -> F1' q
  abbreviations ls = T1.do
    traverse1_ (dispGroup "M  STY" . map (\(x,_) => x ++ " SUP")) (grouped 8 ls)
    traverse1_ (\(x,y,_) => putTextLn "M  SMT\{x} \{y}") ls
    for1_ ls $ \(x,_,vs) => traverse1_ (dispGroup "M  SAL\{x}") (grouped 15 vs)

  props : Props -> F1' q
  props (P is cs rs abbr) =
    traverse1_ (dispGroup "M  ISO") (grouped 8 is) >>
    traverse1_ (dispGroup "M  CHG") (grouped 8 cs) >>
    traverse1_ (dispGroup "M  RAD") (grouped 8 rs) >>
    abbreviations (dispGrp <$> kvList abbr)

--------------------------------------------------------------------------------
--          Writer
--------------------------------------------------------------------------------

  counts : (na,nb : Nat) -> F1' q
  counts na nb =
    fill 3 na >> fill 3 nb >> fill 6 NonChiral >> fill 27 V2000 >> linebreak

  coords : Vect 3 Coordinate -> F1' q
  coords [x,y,z] = fill 10 x >> fill 10 y >> fill 10 z

  %inline atomRem : F1' q
  atomRem = putTextLn " 0  0  0  0  0  0  0  0  0  0  0  0"

  %inline bondRem : F1' q
  bondRem = putTextLn "  0  0  0"

  -- xxxxx.xxxxyyyyy.yyyyzzzzz.zzzz aaaddcccssshhhbbbvvvHHHrrriiimmmnnneee
  atom : Atom Isotope Charge Coordinates Radical h t c l -> F1' q
  atom (MkAtom a c p _ _ _ _ _) = coords p >> fill @{IP_ISO} 4 a >> atomRem

  -- 111222tttsssxxxrrrccc
  bond : Edge k MolBond -> F1' q
  bond (E x y $ MkBond True t s) =
   fill 3 x >> fill 3 y >> fill 3 t >> fill 3 s >> bondRem
  bond (E x y $ MkBond False t s) =
   fill 3 y >> fill 3 x >> fill 3 t >> fill 3 s >> bondRem

  export
  putMol2000 : List (Edge k MolBond) -> MolGraph' h t c -> F1' q
  putMol2000 es (G o g) = T1.do
    counts o (length es)
    traverse1_ (atom . label) g.graph
    traverse1_ bond es
    props $ foldrKV adjProps (P [] [] [] empty) g.graph
