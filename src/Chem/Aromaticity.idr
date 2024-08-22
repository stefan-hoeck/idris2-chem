module Chem.Aromaticity

import Chem.Atom
import Chem.AtomType
import Chem.Elem
import Chem.Rings.Relevant
import Chem.Types
import Data.Graph.Indexed
import Data.SortedMap
import Data.SortedSet
import Derive.Prelude

%default total
%language ElabReflection

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

public export
record AromBond (a : Type) where
  constructor AB
  type : a
  arom : Bool

%runElab derive "AromBond" [Show,Eq,Ord]

||| True, if the given node is connected to at least one aromatic edge.
export %inline
isAromatic : IGraph k (AromBond e) n -> Fin k -> Bool
isAromatic g = any arom . neighboursAsAL g

export %inline
Cast a BondOrder => Cast (AromBond a) BondOrder where
  cast = cast . type

--------------------------------------------------------------------------------
-- AromBonds
--------------------------------------------------------------------------------

||| Bonds count similar to `AtomType.Bonds` but including a counter for
||| aromatic bonds.
public export
record AromBonds where
  constructor ABS
  single : Nat
  arom   : Nat
  double : Nat
  triple : Nat

||| Total number of bonds
export
numBonds : AromBonds -> Nat
numBonds (ABS s a d t) = s + a + d + t

||| Total bond order
|||
||| Note: This assumes that there is a reasonable configuration of aromatic
|||       bonds (2 or 3). Otherwise, aromatic bonds are just ignored.
export
totalBondOrder : AromBonds -> Nat
totalBondOrder (ABS s a d t) =
  let rem = s + 2 * d + 3 * t
   in case a of
        2 => rem + 3
        3 => rem + 4
        _ => rem

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

0 Edges : Nat -> Type
Edges k = SortedSet (Fin k, Fin k)

toPair : Fin k -> Fin k -> (Fin k, Fin k)
toPair x y = if x > y then (y,x) else (x,y)

%inline hasEdge : Fin k -> Fin k -> Edges k -> Bool
hasEdge x y = contains (toPair x y)

hueckel : Nat -> Bool
hueckel n = (cast {to = Integer} n `mod` 4) == 2

--------------------------------------------------------------------------------
-- Aromaticity Perception
--------------------------------------------------------------------------------

parameters {0 e,n   : Type}
           (contrib : n -> Maybe Nat)

  ||| Perceives aromaticity for a mol graph using the given contribution
  ||| function.
  export
  aromatizeI : {k : _} -> IGraph k e n -> IGraph k (AromBond e) n
  aromatizeI {k} g =
    let bs := foldl (pairs [] 0) empty (computeCI' g)
     in IG $ mapWithIndex (toArom bs) g.graph

    where
      toArom : Edges k -> Fin k -> Adj k e n -> Adj k (AromBond e) n
      toArom ps m = {neighbours $= mapKV (\n,v => AB v $ hasEdge m n ps)}

      pairs : List (Fin k, Fin k) -> Nat -> Edges k -> Cycle k -> Edges k
      pairs xs k es (x::t@(y::_)) =
        case contrib (lab g x) of
          Nothing => es
          Just v  => pairs (toPair x y :: xs) (k+v) es t
      pairs xs k es _ =
        if hueckel k then foldl (flip insert) es xs else es

  ||| Perceives aromaticity for a mol graph using the given contribution
  ||| function.
  export %inline
  aromatize : Graph e n -> Graph (AromBond e) n
  aromatize (G o g) = G o $ aromatizeI g

--------------------------------------------------------------------------------
-- Models
--------------------------------------------------------------------------------

atMap : SortedMap (Elem,Charge,Hybridization) Nat
atMap =
  SortedMap.fromList
    [ ((C,0,SP2), 1)
    , ((C,0,SP), 1)
    , ((C,1,Planar), 0)
    , ((C,(-1),SP), 1)
    , ((C,(-1),SP2), 1)
    , ((C,(-1),SP3), 2)
    , ((B,0,SP2), 0)
    , ((O,0,SP3), 2)
    , ((S,0,SP3), 2)
    , ((N,0,SP3), 2)
    , ((N,0,SP2), 1)
    , ((N,(-1),SP3), 2)
    , ((N,(-1),SP2), 1)
    , ((N,1,SP2), 1)
    , ((P,0,SP3), 2)
    , ((P,0,SP2), 1)
    , ((P,(-1),SP3), 2)
    , ((P,(-1),SP2), 1)
    , ((P,1,SP2), 1)
    , ((As,0,SP3), 2)
    , ((Se,0,SP3), 2)
    ]

export
atomType : Cast e Elem => Atom e Charge p r h AtomType c l -> Maybe Nat
atomType a = lookup (cast a.elem, a.charge, a.type.hybridization) atMap
