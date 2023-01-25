module Chem.AtomType

{-
  Stefan Höck: This project is should be based on the source code
  from your bachelor's thesis.

  The goal of this coding project is to clean up that code and get rid of
  all repeating patterns. In order to do so, there are several things you
  should keep in mind:

    * Don't use `String` for atom types: Define an enum type deriving
      `Show`, `Eq` and `Ord` for it, and keep adding new atom types when
      they show up.

    * Most atom types are percieved by comparing the following things:
      element, aromaticity, charge, number and types of bonds (including
      bonds to implicit hydrogen atoms). Group these in a record type and
      derive `Show`, `Eq, and `Ord` for it.

      Now, have a look at function `Data.List.lookup`. Can you see, how
      you can make use of this function plus a list of pairs to come
      up with a general purpose perception function? The list of pairs
      must not be generated anew every time we percieve atom types, so
      use a top-level constant for it.

    * A few atom types require special treatment. Implement those checks
      separately and decide for each of them, whether it should be checked
      before or after running the general perception algorithm.

    * In the end, write a function for converting a graph of type `Graph Bond (Atom ())`
      to a `Maybe (Graph Bond (Atom AtomType))`.

    * Only implement atom types already present in your Bachelor's thesis.

  Marking criteria:

    * Correctness of implementation (write a couple of tests/proofs)
    * DRY-ness of code ("DRY" = "Don't Repeat Yourself")
    * Making use of existing functions from the Idris standard libs.
      (example: `Data.List`, and stuff from the Prelude)
    * Separation of concerns: Split error handling from the rest of
      the functionality. Same goes for grouping / sorting of bonds.
    * Use docstrings / comments to document your code (especially special cases)

  Deadline: 31.01.2023

  A good example for things to watch out for is the following code excerpt:

    ```
    hasODbl : List (Elem,Bond) -> Nat
    hasODbl [] = 0
    hasODbl ((O,Dbl) :: xs) = 1 + hasODbl xs
    hasODbl ((x, y) :: xs) = 0 + hasODbl xs

    hasSDbl : List (Elem,Bond) -> Nat
    hasSDbl [] = 0
    hasSDbl ((S,Dbl) :: xs) = 1 + hasSDbl xs
    hasSDbl ((x, y) :: xs) = 0 + hasSDbl xs

    hasNDbl : List (Elem,Bond) -> Nat
    hasNDbl [] = 0
    hasNDbl ((N,Dbl) :: xs) = 1 + hasNDbl xs
    hasNDbl ((x, y) :: xs) = 0 + hasNDbl xs
    ```

  This is neither DRY (repeats the same code several times), nor does it make
  use of existing functionality (look at `Prelude.count`).
-}


import Chem
import Derive.Prelude
import Data.Graph
import Text.Smiles
import Data.BitMap

%language ElabReflection
%default total

-------------------------------------------------------------------------------
-- Bond Types
-------------------------------------------------------------------------------

record Bonds where
  constructor BS
  single : Nat
  double : Nat
  triple : Nat

||| Calculates total number of bonds
||| (triple bond => 1 bond)
bondsTotal : Bonds -> Nat
bondsTotal b = b.single + b.double + b.triple


Semigroup Bonds where
  (<+>) (BS s1 d1 t1) (BS s2 d2 t2) = BS (s1 + s2) (d1 + d2) (t1 + t2)

Monoid Bonds where
  neutral = BS 0 0 0

Eq Bonds where
  (==) b1 b2 =
       b1.single == b2.single
    && b1.double == b2.double
    && b1.triple == b2.triple

Ord Bonds where
  compare b1 b2 = compare (bondsTotal b1) (bondsTotal b2)


Show Bonds where
  showPrec p (BS s d t) =
    showCon p "BS" $ showArg s ++ showArg d ++ showArg t

toBonds : List Bond -> Bonds
toBonds []           = BS 0 0 0
toBonds (Sngl :: xs) = BS 1 0 0 <+> toBonds xs
toBonds (Dbl :: xs)  = BS 0 1 0 <+> toBonds xs
toBonds (Trpl :: xs) = BS 0 0 1 <+> toBonds xs
toBonds (Arom :: xs) = BS 1 0 0 <+> toBonds xs
toBonds (x :: xs)    = BS 0 0 0 <+> toBonds xs

-------------------------------------------------------------------------------
-- AtomType
-------------------------------------------------------------------------------

data AtomType =
    C_Sp3         | C_Sp2           | C_Sp            | C_Sp2_radical | C_planar_radical |
    C_Sp2_arom    | C_Sp2_diradical | C_Sp3_diradical | O_Sp3         | O_Sp2            |
    O_Sp3_radical | O_Sp2_arom
              

%runElab derive "AtomType" [Show,Eq,Ord]

data BType = Sngl | Dbl | Trb

record ATArgs where
  constructor MkATArgs
  element : Elem
  arom : Bool
  charge : Charge
  bondCount : Nat  -- Maybe not needed, because 'Bonds' has all the information (arom = BS 1 0 0)
  bondType : Bonds

%runElab derive "ATArgs" [Show,Eq,Ord]

hCountToBonds : HCount -> Bonds
hCountToBonds h = BS (cast (h.value)) 0 0

-------------------------------------------------------------------------------
-- AtomType / Argument List
-------------------------------------------------------------------------------

atomTypes : List (ATArgs, AtomType)
atomTypes = [
  (MkATArgs C False 0 4 (BS 4 0 0), C_Sp3),
  (MkATArgs C False 0 3 (BS 2 1 0), C_Sp2),
  (MkATArgs C False 0 2 (BS 1 0 1), C_Sp ),
  (MkATArgs C False 0 2 (BS 0 2 0), C_Sp ), -- + special case C-allene
  (MkATArgs C False 0 2 (BS 1 1 0), C_Sp2_radical),
  (MkATArgs C False 0 3 (BS 3 0 0), C_planar_radical),
  (MkATArgs C False 0 1 (BS 0 1 0), C_Sp2_diradical),
  (MkATArgs C False 0 2 (BS 2 0 0), C_Sp3_diradical),
  (MkATArgs C True  0 2 (BS 2 0 0), C_Sp2_arom),
  (MkATArgs C True  0 3 (BS 3 0 0), C_Sp2_arom),

  -- Charged Carbons

  (MkATArgs O False 0 2 (BS 2 0 0), O_Sp3),
  (MkATArgs O False 0 1 (BS 0 1 0), O_Sp2),
  (MkATArgs O False 0 1 (BS 1 0 0), O_Sp3_radical),
  (MkATArgs O True  0 2 (BS 2 0 0), O_Sp2_arom)

  -- Charged Oxygens

  ]


-------------------------------------------------------------------------------
-- Determination AtomType
-------------------------------------------------------------------------------

neighboursToListNode : Graph Bond (Atom (Maybe a))
                    -> Node
                    -> List (Node,Bond)
neighboursToListNode x y = lneighbours x y


toPairElemBond : Graph Bond (Atom (Maybe a))
              -> Node
              -> List(Elem,Bond)
toPairElemBond x y = List.mapMaybe (go x) (neighboursToListNode x y)
  where go : Graph Bond (Atom (Maybe a)) -> (Node,Bond) -> Maybe (Elem,Bond)
        go x (n,b) = case lab x n of
                          Nothing => Nothing
                          Just w => Just (w.elem,b)


getBondsFromNode : Graph Bond (Atom (Maybe a)) -> Node -> HCount -> Bonds
getBondsFromNode x y h =
    let bnds = (toBonds (go' (lneighbours x y)))
        hbnds = hCountToBonds h
    in bnds <+> hbnds
  where go' : List (Node,Bond) -> List Bond
        go' [] = []
        go' ((z, b) :: zs) = b :: go' zs


toAtomType : ATArgs -> List (ATArgs, AtomType) -> Maybe AtomType
toAtomType = Data.List.lookup


adjToAtomTypes : Graph Bond (Atom (Maybe a))
              -> (BitMap.Key, Adj Bond (Atom (Maybe a)))
              -> Maybe AtomType
adjToAtomTypes x (y, (MkAdj a n)) =
  let bnd       = getBondsFromNode x y a.hydrogen
      bndCount  = bondsTotal bnd
      args      = MkATArgs a.elem a.arom a.charge bndCount bnd
  in toAtomType args atomTypes


toAtomTypes : Graph Bond (Atom (Maybe a)) -> Maybe String -- Maybe (List AtomType)
toAtomTypes (MkGraph g) = map show (traverse (adjToAtomTypes (MkGraph g)) (pairs g))


-------------------------------------------------------------------------------
-- Test section
-------------------------------------------------------------------------------

testArgs : ATArgs
testArgs = MkATArgs C False 0 3 (BS 2 1 0)
