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
  
%runElab derive "Bonds" [Show,Eq,Ord]

||| Calculates total number of bonds
||| (triple bond => 1 bond)
bondsTotal : Bonds -> Nat
bondsTotal b = b.single + b.double + b.triple


Semigroup Bonds where
  (<+>) (BS s1 d1 t1) (BS s2 d2 t2) = BS (s1 + s2) (d1 + d2) (t1 + t2)

Monoid Bonds where
  neutral = BS 0 0 0

-----
toBonds : List Bond -> Bonds
toBonds []           = BS 0 0 0
toBonds (Sngl :: xs) = BS 1 0 0 <+> toBonds xs
toBonds (Dbl :: xs)  = BS 0 1 0 <+> toBonds xs
toBonds (Trpl :: xs) = BS 0 0 1 <+> toBonds xs
toBonds (Arom :: xs) = BS 1 0 0 <+> toBonds xs
toBonds (x :: xs)    = BS 0 0 0 <+> toBonds xs

hCountToBonds : HCount -> Bonds
hCountToBonds h = BS (cast (h.value)) 0 0

-------------------------------------------------------------------------------
-- AtomType
-------------------------------------------------------------------------------

data AtomType =
  C_Sp3            | C_Sp2         | C_Sp2_allene    | C_Sp            | C_Sp2_radical |
  C_planar_radical | C_Sp2_arom    | C_Sp2_diradical | C_Sp3_diradical | O_Sp3         |
  O_Sp2            | O_Sp3_radical | O_Sp2_arom
              
%runElab derive "AtomType" [Show,Eq,Ord]


record ATArgs where
  constructor MkATArgs
  element : Elem
  arom : Bool
  charge : Charge
  bondType : Bonds

%runElab derive "ATArgs" [Show,Eq,Ord]


-------------------------------------------------------------------------------
-- AtomType / Argument List
-------------------------------------------------------------------------------

atomTypes : List (ATArgs, AtomType)
atomTypes = [
  (MkATArgs C False 0 (BS 4 0 0), C_Sp3),
  (MkATArgs C False 0 (BS 2 1 0), C_Sp2),
  (MkATArgs C False 0 (BS 1 0 1), C_Sp ),
  (MkATArgs C False 0 (BS 0 2 0), C_Sp ), -- + special case C-allene
  (MkATArgs C False 0 (BS 1 1 0), C_Sp2_radical),
  (MkATArgs C False 0 (BS 3 0 0), C_planar_radical),
  (MkATArgs C False 0 (BS 0 1 0), C_Sp2_diradical),
  (MkATArgs C False 0 (BS 2 0 0), C_Sp3_diradical),
  (MkATArgs C True  0 (BS 2 0 0), C_Sp2_arom),
  (MkATArgs C True  0 (BS 3 0 0), C_Sp2_arom),

  -- Charged Carbons

  (MkATArgs O False 0 (BS 2 0 0), O_Sp3),
  (MkATArgs O False 0 (BS 0 1 0), O_Sp2),
  (MkATArgs O False 0 (BS 1 0 0), O_Sp3_radical),
  (MkATArgs O True  0 (BS 2 0 0), O_Sp2_arom)

  -- Charged Oxygens

  ]


-------------------------------------------------------------------------------
-- Determination AtomType
-------------------------------------------------------------------------------

||| Extracts a list of linked elements with their connecting bonds
toPairElemBond : Graph Bond (Atom l)
              -> Node
              -> List(Elem,Bond)
toPairElemBond g n = List.mapMaybe (\(node,bond) => map (,bond) (map Atom.elem (lab g node))) (lneighbours g n)


||| Extracts all bonds from an atom
getBondsFromNode : Graph Bond (Atom l) -> Node -> HCount -> Bonds
getBondsFromNode x y h =
  (<+>) (toBonds (map snd (lneighbours x y))) (hCountToBonds h)


||| Help function to determine special AtomTypes
checkNeighbours : AtomType -> List (Elem,Bond) -> Maybe AtomType
checkNeighbours C_Sp2 [(C,Dbl),(C,Dbl)] = Just C_Sp2_allene
checkNeighbours at _ = Just at


||| Help funtion to determine all needed arguments to lookup the AtomType
adjToAtomTypes : Graph Bond (Atom l)
              -> BitMap.Key
              -> Adj Bond (Atom l)
              -> Maybe (Adj Bond (Atom (l,AtomType)))
adjToAtomTypes x y g@(MkAdj a n) =
  let bnd       = getBondsFromNode x y a.hydrogen
      args      = MkATArgs a.elem a.arom a.charge bnd
      neigh     = toPairElemBond x y
      at        = case Data.List.lookup args atomTypes of
                       Nothing => Nothing
                       Just z  => case z of
                          C_Sp2 => checkNeighbours z neigh
                          _ => Just z
  in traverse (\x => case at of
              Nothing => Nothing
              Just z  => Just $ map (\l => (l,z)) x) g


||| Determines the AtomType if possible
toAtomTypes : Graph Bond (Atom l) -> Maybe (Graph Bond (Atom (l,AtomType)))
toAtomTypes g@(MkGraph bm) = MkGraph <$> traverseWithKey (adjToAtomTypes g) bm


-------------------------------------------------------------------------------
-- Test section
-------------------------------------------------------------------------------

-- Read in a SMILES-string and convert the resulting graph into a graph with
-- AtomTypes
fromSmilesToAtomType : IO ()
fromSmilesToAtomType = do
  str <- map trim getLine
  case parse str of
       Stuck x cs => putStrLn (show x ++ pack cs)
       End g => case (maybe Nothing toAtomTypes (graphWithH g)) of
                     Nothing => putStrLn ("Conversion into Atom or Atom with AtomType failed")
                     Just x  => putStrLn (pretty show show x)
