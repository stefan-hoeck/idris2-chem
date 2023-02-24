module Chem.AtomType

import Chem.Types
import Chem.Atom
import Chem.Element
import Text.Smiles
import Data.Graph
import Data.BitMap
import Derive.Prelude

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
toBonds : List Bond -> Bonds
toBonds = foldMap (\case
                  Sngl => BS 1 0 0
                  Arom => BS 1 0 0
                  Dbl  => BS 0 1 0
                  Trpl => BS 0 0 1
                  Quad => BS 0 0 0)


-- hock: Coding style
--  * Use the dollar operator to reduce the amount of nesting
--  * Record projections don't need to be put in parentheses
--  * Consider implementing `Cast` for such convertions
public export
hCountToBonds : HCount -> Bonds
hCountToBonds h = BS (cast (h.value)) 0 0


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
--   * For data types used a lot in pattern matches, choose short
--     constructor names. Especially if they are only used internally.
--     This reduces code clutter. Example: `AA` or even `A`
||| ATArgs represents the arguments needed to evaluate the associated AtomType
public export
record ATArgs where
  constructor MkATArgs
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

-- hock:
--
-- Performance:
--   * We already have access to the `Adj` when this is called. no need to
--     look it up again via `lneighbours`.
--   * Instead of sequencing calls to `map`, sequence the functions:
--     `mapMaybe (\(k,b) => (,b) . elem <$> lab g k) (lneighbours g n)`
--
-- Design
--   * Don't export internal utility functions.
||| Extracts a list of linked elements with their connecting bonds
public export
toPairElemBond : Graph Bond (Atom l)
              -> Node
              -> List(Elem,Bond)
toPairElemBond g n =
  List.mapMaybe (\(node,bond) => map (,bond) (map Atom.elem (lab g node))) (lneighbours g n)


-- hock:
-- Code reuse
--   * By rewriting `toBonds` as suggested, we could use `foldMap` here.
--     (On the `Adj`, which we already have access to).
--
-- Coding stel
--   * Use operators in infix notation to reduce amount of paretheses.
||| Extracts all bonds from an atom
public export
getBondsFromNode : Graph Bond (Atom l) -> Node -> HCount -> Bonds
getBondsFromNode x y h =
  (<+>) (toBonds (map snd (lneighbours x y))) (hCountToBonds h)


-- hock:
-- Code reuse
--   * Use `Eq` implementation for `Pair`:
--     `hasDblX xs e = count ((e,Dbl) ==) xs`
--
-- Design:
--   Does this need to be exported or is it an internal function?
||| Returns the number of double bonds from the determining element
||| to a specific element
public export
hasDblX : List (Elem, Bond) -> Elem -> Nat
hasDblX xs e = count (\x => fst x == e && snd x == Dbl) xs

-- hock:
-- Code reuse
--   * Use `isJust` or `not . null` to test if a `Maybe` is inhabited
--     (`null` comes from `Foldable`)
--   * Better still: Use `elem` and drop this altogether:
--     `elem Arom xs`, which is then so trivial that this function
--     can be dropped altogether
--
-- Coding style:
--   * Prefer currying and operator sections in anonymous functions
--   * Do not fully qualify identifiers unless they need to be
--     disambiguated.
||| Returns True, if an aromatic bond is present
hasArom : List Bond -> Bool
hasArom xs = case Data.List.find (\x =>x == Arom) xs of
  Nothing => False
  _       => True


||| Deals with the special cases
public export
checkSpecialTypes : AtomType -> List (Elem,Bond) -> AtomType
checkSpecialTypes C_sp bs   =
  if hasDblX bs C == 2 then C_sp_allene else C_sp
checkSpecialTypes S_4_sp2 bs =
  if hasDblX bs O == 2 then S_4_planar3_oxide else S_4_sp2
checkSpecialTypes S_6_sp3 bs =
  if hasDblX bs O == 1 && hasDblX bs S == 1 then S_6_sp3_thionyl
  else if (hasDblX bs O + hasDblX bs N) == 2 then S_6_sp3_onyl
  else S_6_sp3
checkSpecialTypes at _ = at


-- Coding style:
--   * Don't use doc-strings for commenting non-exported functions.
||| Deals with the special case of oxygen
||| Uses the bonds of all the neighbours to check for special
||| Types
checkSpecialTypes2 : AtomType -> List Bond -> AtomType
checkSpecialTypes2 h xs = case hasArom xs of
  False => h
  True  => O_sp2


-- hock:
-- Coding style:
--   * Large anonymous functions are hard to digest when reading code.
--     Use lambdas and/or currying only for short anonymous functions the
--     fit on a single line. Exception: Lambda case (pattern matching) after
--     a dollar operator if the lambda is the last argument of a (maybe
--     curried) higher-order function.
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
||| Help funtion to determine all needed arguments to lookup the AtomType
public export
adjToAtomTypes : Graph Bond (Atom l)
              -> BitMap.Key
              -> Adj Bond (Atom l)
              -> Maybe (Adj Bond (Atom (l,AtomType)))
adjToAtomTypes x y g@(MkAdj a n) =
  let bnd   = getBondsFromNode x y a.hydrogen
      args  = MkATArgs a.elem a.arom a.charge bnd
      neigh = toPairElemBond x y
      neighB = foldMap (\w => map snd (lneighbours x w)) (map fst (lneighbours x y))
      at    = map (\z => if z == C_sp || z == S_4_sp2 || z == S_6_sp3
                   then checkSpecialTypes z neigh
                   else if z == O_sp3
                   then checkSpecialTypes2 z neighB
                   else z)
                      (Data.List.lookup args atomTypes)
  in traverse (\x => case at of
              Nothing => Nothing
              Just z  => Just $ map (\l => (l,z)) x) g


||| Determines the AtomType if possible
public export
toAtomTypes : Graph Bond (Atom l) -> Maybe (Graph Bond (Atom (l,AtomType)))
toAtomTypes g@(MkGraph bm) = MkGraph <$> traverseWithKey (adjToAtomTypes g) bm


-------------------------------------------------------------------------------
-- Test section
-------------------------------------------------------------------------------

||| Read in a SMILES-string and convert the resulting graph into a graph with
||| AtomTypes and print it
public export
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
