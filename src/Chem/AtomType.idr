module Chem.AtomType

import Chem.Types
import Chem.Atom
import Chem.Element
import Text.Smiles
import Data.AssocList
import Data.Graph
import Data.BitMap
import Derive.Prelude
import System

%language ElabReflection
%default total

-------------------------------------------------------------------------------
-- Bond Types
-------------------------------------------------------------------------------

public export
record Bonds where
  constructor BS
  single : Nat
  double : Nat
  triple : Nat

%runElab derive "Bonds" [Show,Eq,Ord]


||| Calculates total number of bonds
||| (triple bond => 1 bond)
public export
bondsTotal : Bonds -> Nat
bondsTotal b = b.single + b.double + b.triple


Semigroup Bonds where
  (<+>) (BS s1 d1 t1) (BS s2 d2 t2) = BS (s1 + s2) (d1 + d2) (t1 + t2)

Monoid Bonds where
  neutral = BS 0 0 0


-- hock: Coding style:
--   * Minimize amount of indentation
--   * Don't use parens around lambda case: Use the dollar operator
--
-- Code reuse: This function is much more useful if we convert
-- just a `Bond` to `Bonds`. The `foldMap` part is then trivial and
-- can be used on all `Foldable`s, not just lists.
||| Folds a list of Bond's to Bonds
||| Caution: Quad-Bond's counts as 0!
public export
toBonds : Bond -> Bonds
toBonds Sngl = BS 1 0 0
toBonds Arom = BS 1 0 0
toBonds Dbl  = BS 0 1 0
toBonds Trpl = BS 0 0 1
toBonds Quad = BS 0 0 0

-- hock: Coding style
--  * Use the dollar operator to reduce the amount of nesting
--  * Record projections don't need to be put in parentheses
--  * Consider implementing `Cast` for such convertions
public export
hCountToBonds : HCount -> Bonds
hCountToBonds h = BS (cast h.value) 0 0


-------------------------------------------------------------------------------
-- AtomType
-------------------------------------------------------------------------------

||| Syntax: element_(std.valence)_hybridisation_aromaticity_charge_radical_specials
public export
data AtomType =
  C_sp3              | C_sp2              | C_sp_allene          | C_sp             |
  C_sp2_radical      | C_sp_radical       | C_planar_radical     | C_sp2_arom       |
  C_sp2_diradical    | C_sp3_diradical    | C_planar_plus        | C_sp2_plus       |
  C_sp_plus          | C_sp2_arom_plus    | C_planar_minus       | C_sp2_minus      |
  C_sp_minus         | C_sp2_arom_minus   | H_sgl                | H_plus           |
  H_minus            | O_sp3              | O_sp2                | O_sp3_radical    |
  O_sp2_arom         | O_sp3_plus         | O_sp2_plus           | O_sp_plus        |
  O_sp3_plus_radical | O_sp2_plus_radical | O_sp3_minus          | O_sp3_minus2     |
  S_2_sp3            | S_2_sp2            | S_6_sp3d2_anyl       | S_4_sp2_inyl     |
  S_4_sp2            | S_4_planar3_oxide  | S_6_sp3d2_octahedral | S_6_sp3d1        |
  S_6_sp3            | S_6_sp3_thionyl    | S_6_sp3_onyl         | S_6_sp2_trioxide |
  S_2_planar3        | S_4_sp2_arom_inyl2 | S_6_sp2_plus         | S_4_sp2_plus     |
  S_4_sp3_plus2      | S_2_sp3_minus      | S_2_minus2

%runElab derive "AtomType" [Show,Eq,Ord]


-- hock
-- I think, this should be an internal utility type. We should not
-- export this.
-- Coding style
--   * For data types we use a lot in pattern matches, choose short
--     constructor names. Especially if they are only used internally.
--     This reduces code clutter.
||| ATArgs represents the arguments needed to evaluate the associated AtomType
record ATArgs where
  constructor AA
  element  : Elem
  arom     : Bool
  charge   : Charge
  bondType : Bonds

%runElab derive "ATArgs" [Show,Eq,Ord]


-------------------------------------------------------------------------------
-- AtomType / Argument List
-------------------------------------------------------------------------------

||| Includes a list with matching ATArgs and AtomType Pairs
public export
atomTypes : List (ATArgs, AtomType)
atomTypes = [
  -- Carbon
  (AA C False 0    (BS 4 0 0), C_sp3),
  (AA C False 0    (BS 2 1 0), C_sp2),
  (AA C False 0    (BS 1 0 1), C_sp),
  (AA C False 0    (BS 0 2 0), C_sp),
  (AA C False 0    (BS 1 1 0), C_sp2_radical),
  (AA C False 0    (BS 1 0 0), C_sp_radical),
  (AA C False 0    (BS 3 0 0), C_planar_radical),
  (AA C False 0    (BS 0 1 0), C_sp2_diradical),
  (AA C False 0    (BS 2 0 0), C_sp3_diradical),
  (AA C True  0    (BS 2 0 0), C_sp2_arom),
  (AA C True  0    (BS 3 0 0), C_sp2_arom),
  (AA C False 1    (BS 3 0 0), C_planar_plus),
  (AA C False 1    (BS 1 1 0), C_sp2_plus),
  (AA C False 1    (BS 0 0 1), C_sp_plus),
  (AA C True  1    (BS 2 0 0), C_sp2_arom_plus),
  (AA C True  1    (BS 3 0 0), C_sp2_arom_plus),
  (AA C False (-1) (BS 3 0 0), C_planar_minus),
  (AA C False (-1) (BS 1 1 0), C_sp2_minus),
  (AA C False (-1) (BS 0 0 1), C_sp_minus),
  (AA C True  (-1) (BS 2 0 0), C_sp2_arom_minus),
  (AA C True  (-1) (BS 3 0 0), C_sp2_arom_minus),

  -- Hydrogen
  (AA H False 0    (BS 1 0 0), H_sgl),
  (AA H False 1    (BS 0 0 0), H_plus),
  (AA H False (-1) (BS 0 0 0), H_minus),

  -- Oxygen
  (AA O False 0    (BS 2 0 0), O_sp3),
  (AA O False 0    (BS 0 1 0), O_sp2),
  (AA O False 0    (BS 1 0 0), O_sp3_radical),
  (AA O True  0    (BS 2 0 0), O_sp2_arom),
  (AA O False 1    (BS 3 0 0), O_sp3_plus),
  (AA O False 1    (BS 1 1 0), O_sp2_plus),
  (AA O False 1    (BS 0 0 1), O_sp_plus),
  (AA O False 1    (BS 2 0 0), O_sp3_plus_radical),
  (AA O False 1    (BS 0 1 0), O_sp2_plus_radical),
  (AA O False (-1) (BS 1 0 0), O_sp3_minus),
  (AA O False (-2) (BS 0 0 0), O_sp3_minus2),

  -- Sulfur
  (AA S False 0    (BS 2 0 0), S_2_sp3),
  (AA S False 0    (BS 0 1 0), S_2_sp2),
  (AA S False 0    (BS 4 0 0), S_6_sp3d2_anyl),
  (AA S False 0    (BS 2 1 0), S_4_sp2_inyl),
  (AA S False 0    (BS 0 2 0), S_4_sp2),
  (AA S False 0    (BS 1 0 1), S_4_sp2),
  (AA S False 0    (BS 6 0 0), S_6_sp3d2_octahedral),
  (AA S False 0    (BS 4 1 0), S_6_sp3d1),
  (AA S False 0    (BS 2 2 0), S_6_sp3),
  (AA S False 0    (BS 0 3 0), S_6_sp2_trioxide),
  (AA S True  0    (BS 2 0 0), S_2_planar3),
  (AA S True  0    (BS 0 2 0), S_4_sp2_arom_inyl2),
  (AA S False 1    (BS 3 0 0), S_6_sp2_plus),
  (AA S False 1    (BS 1 1 0), S_4_sp2_plus),
  (AA S False 2    (BS 2 2 0), S_4_sp3_plus2),
  (AA S False (-1) (BS 1 0 0), S_2_sp3_minus),
  (AA S False (-2) (BS 0 0 0), S_2_minus2)

  ]


-------------------------------------------------------------------------------
-- Determination AtomType
-------------------------------------------------------------------------------




-- hock:
-- Code reuse
--   * Use `Eq` implementation for `Pair`
--
-- Design:
--   Does this need to be exported or is it an internal function?
||| Returns the number of double bonds from the determining element
||| to a specific element
public export
hasDblX : List (Elem, Bond) -> Elem -> Nat
hasDblX xs e = count ((e,Dbl) ==) xs

-- hock:
-- Code reuse
--   * Use `isJust` or `not . null` to test if a `Maybe` is inhabited
--     (`null` comes from `Foldable`)
--   * Better still: Use `elem` and drop this altogether.
--
-- Coding style:
--   * Prefer currying and operator sections in anonymous functions
||| Returns True, if an aromatic bond is present
hasArom : List Bond -> Bool
hasArom = isJust . find (== Arom)

public export
isPiBond : Bond -> Bool
isPiBond Sngl = False
isPiBond Arom = True
isPiBond Dbl  = True
isPiBond Trpl = True
isPiBond Quad = False -- hock: not sure about this


-- hock:
-- Code reuse
--   * Use `elem` instead of custom function
--
-- Coding style:
--   * Prefer `if then else` if it fits on a single line.
--   * Don't use doc strings (starting with `|||`) for commenting on
--     private functions

-- Deals with the special case of oxygen
-- Uses the bonds of all the neighbours to check for special
-- Types
-- checkSpecialTypes2 : AtomType -> List Bond -> AtomType
-- checkSpecialTypes2 h xs = if Arom `elem` xs then O_sp2 else h

-- hock:
-- Coding style:
--   * Large anonymous functions are hard to digest when reading code.
--     Use lambdas and/or currying only for short anonymous functions the
--     fit on a single line. Exception: Lambda case (pattern matching) after
--     a dollar operator if the lambda is the last argument of a (maybe
--     curried) higher-order function.
--
--   * It was hard to understand what this function does. The mixture of
--     equality.
--
--   * If the traversal is complex, extract the conversion to a utility
--     function
--
--   * Consider using `parameters` blocks for parameters (unchanging arguments)
--     appearing in several related functions.
--
--   * If something is a helper function, don't export it.
--
-- Code reuse:
--   Use `any` to check if a condition holds for a value in a `Foldable`
--
-- Code correctness:
--   Conjugation for oxygen or nitrogen happens with all neighbours with
--   an electron deficit (C+ or B, for instance) plus atoms bound
--   to a pi-bonds (double, triple, aromatic)

parameters (g   : Graph Bond (Atom l))
           (n   : Node)
           (adj : Adj Bond (Atom l))
  -- hock:
  -- Coding style:
  --   * Place long type signatures on the next line, aligning
  --     the arrows on the left. This means that the type signature will
  --     not have to be realigned if we rename the function
  --   * Do not exceed the line width limit of 80 characters unless strictly
  --     necessary.
  --   * Do not use fully qualified names unless there is a need for
  --     disambiguation
  --   * Use `<$>` instead of `map`, if this reduces the need for parentheses
  --
  -- Performance:
  --   Instead of sequencing calls to `map`, sequence the function calls

  -- Extracts a list of linked elements with their connecting bonds
  labeledBonds : List(Elem,Bond)
  labeledBonds =
    mapMaybe (\(k,b) => (,b) . elem <$> lab g k) (pairs adj.neighbours)

  doubleTo : Elem -> Nat
  doubleTo e = count isDoubleTo (pairs adj.neighbours)
    where isDoubleTo : (Node,Bond) -> Bool
          isDoubleTo (k,Dbl) = Just e == (elem <$> lab g k)
          isDoubleTo _       = False

  inPiSystem : Bool
  inPiSystem = any (any (isPiBond . snd) . lneighbours g) (keys adj.neighbours)

  refine : AtomType -> AtomType
  refine C_sp    = if doubleTo C == 2 then C_sp_allene else C_sp
  refine O_sp3   = if inPiSystem then O_sp2 else O_sp3
  refine S_4_sp2 = if doubleTo O == 2 then S_4_planar3_oxide else S_4_sp2
  refine S_6_sp3 =
    if doubleTo O == 1 && doubleTo S == 1 then S_6_sp3_thionyl
    else if (doubleTo O + doubleTo N) == 2 then S_6_sp3_onyl
    else S_6_sp3
  refine at = at

  -- hock:
  -- Coding style:
  --   * Prefer infix notation for operators
  --
  -- Performance:
  --   * `toBonds` and `map` will traverse the list twice. `hCountToBonds`
  --     builds up a `Bonds` value just to take it appart again
  --   * There is no need to lookup the edge lables via `lneighbours`
  --     if we already have access to the `Adj` of a node.
  --
  -- Design:
  --   Does this need to be exported or is it an internal function?
  -- bonds : Foldable t => t Bond -> HCount -> Bonds
  -- bonds bs h = foldMap toBonds bs <+> BS (cast h.value) 0 0

  atArgs : ATArgs
  atArgs =
    let MkAtom el ar _ ch _ h := label adj
        bs := foldMap toBonds adj.neighbours <+> BS (cast h.value) 0 0
     in AA el ar ch bs

  -- Wrap-up the new atom type with the existing adjacency information
  relabel : AtomType -> Adj Bond (Atom (l,AtomType))
  relabel aa = (map . map) (,aa) adj

  -- Helper funtion to determine all needed arguments to lookup the AtomType
  adj : Maybe (Adj Bond (Atom (l,AtomType)))
  adj = relabel . refine <$> lookup atArgs atomTypes

-- --     let bnd   = getBondsFromNode x y a.hydrogen
-- --         args  = AA a.elem a.arom a.charge bnd
-- --         neigh = toPairElemBond x y
-- --         neighB = any (any (isPiBond . snd) . lneighbours x . snd) (lneighbours x y)
-- --         at    = map (\z => if z == C_sp || z == S_4_sp2 || z == S_6_sp3
-- --                      then checkSpecialTypes z neigh
-- --                      else if z == O_sp3
-- --                      then checkSpecialTypes2 z neighB
-- --                      else z)
-- --                         (Data.List.lookup args atomTypes)
-- --     --
-- --     in traverse (\x => case at of
-- --                 Nothing => Nothing
-- --                 Just z  => Just $ map (\l => (l,z)) x) g
-- --
--
||| Determines the AtomType if possible
public export
toAtomTypes : Graph Bond (Atom l) -> Maybe (Graph Bond (Atom (l,AtomType)))
toAtomTypes g = MkGraph <$> traverseWithKey (adj g) (graph g)


-------------------------------------------------------------------------------
-- Test section
-------------------------------------------------------------------------------

public export
fromSmiles : String -> Either String (Graph Bond (Atom (Chirality, AtomType)))
fromSmiles s =
  let End g   := parse s  | Stuck x cs => Left (show x ++ pack cs)
      Just g2 := graphWithH g
        | Nothing => Left "Failed to determine implicit hydrogens"
      Just g3 := toAtomTypes g2
        | Nothing => Left "Failed to determine atom types"
   in Right g3

-- hock
-- Code reuse:
--  * `Maybe` is a `Monad`
--  * Use `System.die` to terminate with an error message plus error condition
--
-- Design:
--   Extract pure conversion function to the top-level
||| Read in a SMILES-string and convert the resulting graph into a graph with
||| AtomTypes and print it
public export
smilesAtomTypeIO : IO ()
smilesAtomTypeIO = do
  str <- map trim getLine
  case fromSmiles str of
    Left s  => die s
    Right g => putStrLn (pretty show show g)


-- hock: No longer needed
-- ||| Read in a SMILES-string and convert the resulting graph into a graph with
-- ||| AtomTypes
-- smilesAtomType : String -> Maybe (Graph Bond (Atom (Chirality, AtomType)))
-- smilesAtomType str =
--   case parse str of
--        Stuck x cs => Nothing
--        End g => maybe Nothing toAtomTypes (graphWithH g)


0 equalA : ATArgs -> ATArgs -> Bool
equalA x y = (==) (Data.List.lookup x atomTypes) (Data.List.lookup y atomTypes)

0 eqArgsTest1 : equalA (AA C False 0 (BS 1 0 1)) (AA C False 0 (BS 0 2 0)) === True
eqArgsTest1 = Refl

0 eqArgsTest2 : equalA (AA C False 0 (BS 2 1 0)) (AA C False 0 (BS 4 0 0)) === False
eqArgsTest2 = Refl
