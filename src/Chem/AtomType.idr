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


||| Folds a list of Bond's to Bonds
||| Caution: Quad-Bond's counts as 0!
toBonds : List Bond -> Bonds
toBonds = foldMap (\case 
                  Sngl => BS 1 0 0
                  Arom => BS 1 0 0
                  Dbl  => BS 0 1 0
                  Trpl => BS 0 0 1
                  Quad => BS 0 0 0)


hCountToBonds : HCount -> Bonds
hCountToBonds h = BS (cast (h.value)) 0 0


-------------------------------------------------------------------------------
-- AtomType
-------------------------------------------------------------------------------

||| Syntax: element_(std.valence)_hybridisation_aromaticity_charge_radical_specials
data AtomType =
  C_sp3            | C_sp2              | C_sp_allene        | C_sp                 |
  C_sp2_radical    | C_sp_radical       | C_planar_radical   | C_sp2_arom           |
  C_sp2_diradical  | C_sp3_diradical    | C_planar_plus      | C_sp2_plus           |
  C_sp_plus        | C_sp2_arom_plus    | C_planar_minus     | C_sp2_minus          |
  C_sp_minus       | C_sp2_arom_minus   | H_sgl              | H_rad                |
  H_plus           | H_minus            | O_sp3              | O_sp2                |
  O_sp3_radical    | O_sp2_arom         | O_sp3_plus         | O_sp2_plus           |
  O_sp_plus        | O_sp3_plus_radical | O_sp2_plus_radical | O_sp3_minus          |
  O_sp3_minus2     | S_2_sp3            | S_2_sp2            | S_6_sp3d2_anyl       |
  S_4_sp2_inyl     | S_4_sp2            | S_4_planar3_oxide  | S_6_sp3d2_octahedral |
  S_6_sp3d1        | S_6_sp3            | S_6_sp3_thionyl    | S_6_sp3_onyl         |
  S_6_sp2_trioxide | S_2_planar3        | S_4_sp2_arom_inyl2 | S_6_sp2_plus         |
  S_4_sp2_plus     | S_4_sp3_plus2      | S_2_sp3_minus      | S_2_minus2
              
%runElab derive "AtomType" [Show,Eq,Ord]


||| ATArgs represents the arguments needed to evaluate the associated AtomType
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

||| Includes a list with matching ATArgs and AtomType Pairs
atomTypes : List (ATArgs, AtomType)
atomTypes = [
  -- Carbon
  (MkATArgs C False 0    (BS 4 0 0), C_sp3),
  (MkATArgs C False 0    (BS 2 1 0), C_sp2),
  (MkATArgs C False 0    (BS 1 0 1), C_sp),
  (MkATArgs C False 0    (BS 0 2 0), C_sp),
  (MkATArgs C False 0    (BS 1 1 0), C_sp2_radical),
  (MkATArgs C False 0    (BS 1 0 0), C_sp_radical),
  (MkATArgs C False 0    (BS 3 0 0), C_planar_radical),
  (MkATArgs C False 0    (BS 0 1 0), C_sp2_diradical),
  (MkATArgs C False 0    (BS 2 0 0), C_sp3_diradical),
  (MkATArgs C True  0    (BS 2 0 0), C_sp2_arom),
  (MkATArgs C True  0    (BS 3 0 0), C_sp2_arom),
  (MkATArgs C False 1    (BS 3 0 0), C_planar_plus),
  (MkATArgs C False 1    (BS 1 1 0), C_sp2_plus),
  (MkATArgs C False 1    (BS 0 0 1), C_sp_plus),
  (MkATArgs C True  1    (BS 2 0 0), C_sp2_arom_plus),
  (MkATArgs C True  1    (BS 3 0 0), C_sp2_arom_plus),
  (MkATArgs C False (-1) (BS 3 0 0), C_planar_minus),
  (MkATArgs C False (-1) (BS 1 1 0), C_sp2_minus),
  (MkATArgs C False (-1) (BS 0 0 1), C_sp_minus),
  (MkATArgs C True  (-1) (BS 2 0 0), C_sp2_arom_minus),
  (MkATArgs C True  (-1) (BS 3 0 0), C_sp2_arom_minus),

  -- Hydrogen
  (MkATArgs H False 0    (BS 1 0 0), H_sgl),
  (MkATArgs H False 0    (BS 0 0 0), H_rad),
  (MkATArgs H False 1    (BS 0 0 0), H_plus),
  (MkATArgs H False (-1) (BS 0 0 0), H_minus),

  -- Oxygen
  (MkATArgs O False 0    (BS 2 0 0), O_sp3),
  (MkATArgs O False 0    (BS 0 1 0), O_sp2),
  (MkATArgs O False 0    (BS 1 0 0), O_sp3_radical),
  (MkATArgs O True  0    (BS 2 0 0), O_sp2_arom),
  (MkATArgs O False 1    (BS 3 0 0), O_sp3_plus),
  (MkATArgs O False 1    (BS 1 1 0), O_sp2_plus),
  (MkATArgs O False 1    (BS 0 0 1), O_sp_plus),
  (MkATArgs O False 1    (BS 2 0 0), O_sp3_plus_radical),
  (MkATArgs O False 1    (BS 0 1 0), O_sp2_plus_radical),
  (MkATArgs O False (-1) (BS 1 0 0), O_sp3_minus),
  (MkATArgs O False (-2) (BS 0 0 0), O_sp3_minus2),

  -- Sulfur
  (MkATArgs S False 0    (BS 2 0 0), S_2_sp3),
  (MkATArgs S False 0    (BS 0 1 0), S_2_sp2),
  (MkATArgs S False 0    (BS 4 0 0), S_6_sp3d2_anyl),
  (MkATArgs S False 0    (BS 2 1 0), S_4_sp2_inyl),
  (MkATArgs S False 0    (BS 0 2 0), S_4_sp2),
  (MkATArgs S False 0    (BS 1 0 1), S_4_sp2),
  (MkATArgs S False 0    (BS 6 0 0), S_6_sp3d2_octahedral),
  (MkATArgs S False 0    (BS 4 1 0), S_6_sp3d1),
  (MkATArgs S False 0    (BS 2 2 0), S_6_sp3),
  (MkATArgs S False 0    (BS 0 3 0), S_6_sp2_trioxide),
  (MkATArgs S True  0    (BS 2 0 0), S_2_planar3),
  (MkATArgs S True  0    (BS 0 2 0), S_4_sp2_arom_inyl2),
  (MkATArgs S False 1    (BS 3 0 0), S_6_sp2_plus),
  (MkATArgs S False 1    (BS 1 1 0), S_4_sp2_plus),
  (MkATArgs S False 2    (BS 2 2 0), S_4_sp3_plus2),
  (MkATArgs S False (-1) (BS 1 0 0), S_2_sp3_minus),
  (MkATArgs S False (-2) (BS 0 0 0), S_2_minus2)

  ]


-------------------------------------------------------------------------------
-- Determination AtomType
-------------------------------------------------------------------------------

||| Extracts a list of linked elements with their connecting bonds
toPairElemBond : Graph Bond (Atom l)
              -> Node
              -> List(Elem,Bond)
toPairElemBond g n =
  List.mapMaybe (\(node,bond) => map (,bond) (map Atom.elem (lab g node))) (lneighbours g n)


||| Extracts all bonds from an atom
getBondsFromNode : Graph Bond (Atom l) -> Node -> HCount -> Bonds
getBondsFromNode x y h =
  (<+>) (toBonds (map snd (lneighbours x y))) (hCountToBonds h)


||| Returns the number of double bonds to a specific element
hasDblX : List (Elem, Bond) -> Elem -> Nat
hasDblX xs e = count (\x => fst x == e) xs


||| Deals with the special cases
checkSpecialTypes : AtomType -> List (Elem,Bond) -> AtomType
checkSpecialTypes C_sp bs   =
  if hasDblX bs C == 2 then C_sp_allene else C_sp
checkSpecialTypes S_4_sp2 bs =
  if hasDblX bs O == 2 then S_4_planar3_oxide else S_4_sp2
checkSpecialTypes S_6_sp3 bs =
  if hasDblX bs O == 1 && hasDblX bs S == 1 then S_6_sp3_thionyl
  else if hasDblX bs O + hasDblX bs N == 2 then S_6_sp3_thionyl
  else S_6_sp3
checkSpecialTypes at _ = at


||| Help funtion to determine all needed arguments to lookup the AtomType
adjToAtomTypes : Graph Bond (Atom l)
              -> BitMap.Key
              -> Adj Bond (Atom l)
              -> Maybe (Adj Bond (Atom (l,AtomType)))
adjToAtomTypes x y g@(MkAdj a n) =
  let bnd   = getBondsFromNode x y a.hydrogen
      args  = MkATArgs a.elem a.arom a.charge bnd
      neigh = toPairElemBond x y
      at    = map (\z => if z == C_sp || z == S_4_sp2 || z == S_6_sp3
                   then checkSpecialTypes z neigh else z)
                      (Data.List.lookup args atomTypes)
  in traverse (\x => case at of
              Nothing => Nothing
              Just z  => Just $ map (\l => (l,z)) x) g


||| Determines the AtomType if possible
toAtomTypes : Graph Bond (Atom l) -> Maybe (Graph Bond (Atom (l,AtomType)))
toAtomTypes g@(MkGraph bm) = MkGraph <$> traverseWithKey (adjToAtomTypes g) bm


-------------------------------------------------------------------------------
-- Test section
-------------------------------------------------------------------------------

||| Read in a SMILES-string and convert the resulting graph into a graph with
||| AtomTypes and print it
smilesAtomTypeIO : IO ()
smilesAtomTypeIO = do
  str <- map trim getLine
  case parse str of
       Stuck x cs => putStrLn (show x ++ pack cs)
       End g => case (maybe Nothing toAtomTypes (graphWithH g)) of
                     Nothing => putStrLn ("Conversion into Atom or Atom with AtomType failed")
                     Just x  => putStrLn (pretty show show x)


||| Read in a SMILES-string and convert the resulting graph into a graph with
||| AtomTypes
smilesAtomType : String -> Maybe (Graph Bond (Atom (Chirality, AtomType)))
smilesAtomType str =
  case parse str of
       Stuck x cs => Nothing
       End g => maybe Nothing toAtomTypes (graphWithH g)


0 equalA : ATArgs -> ATArgs -> Bool
equalA x y = (==) (Data.List.lookup x atomTypes) (Data.List.lookup y atomTypes)

0 eqArgsTest1 : equalA (MkATArgs C False 0 (BS 1 0 1)) (MkATArgs C False 0 (BS 0 2 0)) === True
eqArgsTest1 = Refl

0 eqArgsTest2 : equalA (MkATArgs C False 0 (BS 2 1 0)) (MkATArgs C False 0 (BS 4 0 0)) === False
eqArgsTest2 = Refl
