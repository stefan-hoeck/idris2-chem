module Chem.AtomType

import Chem
import Text.Smiles
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

||| Folds a list of Bond's to Bonds
||| Caution: Quad-Bond's counts as 0!
public export
toBonds : Bond -> Bonds
toBonds Sngl = BS 1 0 0
toBonds Arom = BS 1 0 0
toBonds Dbl  = BS 0 1 0
toBonds FW   = BS 0 1 0
toBonds BW   = BS 0 1 0
toBonds Trpl = BS 0 0 1
toBonds Quad = BS 0 0 0

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

public export
isPiBond : Bond -> Bool
isPiBond Sngl = False
isPiBond Arom = True
isPiBond Dbl  = True
isPiBond FW   = True
isPiBond BW   = True
isPiBond Trpl = True
isPiBond Quad = False -- hock: not sure about this

parameters (g   : Graph Bond (Atom l))
           (n   : Node)
           (adj : Adj Bond (Atom l))
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

||| Determines the AtomType if possible
public export
toAtomTypes : Graph Bond (Atom l) -> Maybe (Graph Bond (Atom (l,AtomType)))
toAtomTypes g = MkGraph <$> traverseWithKey (adj g) (graph g)

-- TODO : Algorithm needed to check all atomtypes on possibility to generate a more
-- specific atomtype based on neighbouring atomtypes
--
-- 1.  Determine all atomtypes with function 'toAtomTypes'.
-- 2.  Start with the loop. Apply 'update' a first time.
-- 3a. If nothing is modified, stop the loop and return the Graph.
-- 3b. If something is modified, reapply 'update' a second time.
-- 4.  Repeat step 3. until a) 3a. is reached or b) break if step 3b. runs more
--     than ?maybe four times.
--
-- Function to update the atomtypes:
-- update' : Graph Bond (Atom (l,AtomType))
--   -> Maybe (Graph Bond (Atom (l,AtomType)))
--
update : Graph Bond (Atom (l,AtomType))
  -> (flag : Nat)
  -> Maybe ((Graph Bond (Atom (l,AtomType))), Nat)
-- Flag needed to stop the loop -> set maximum number of iterations to prevent
-- long calculation times => mark this as an error (Nothing)
-- set flag to 0 if nothing has changed, else iterate and decrease flag by one
-- until value of flag reached zero
