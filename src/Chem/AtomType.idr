module Chem.AtomType

import Chem
import Chem.Types
import Text.Smiles
import Derive.Prelude
import System
import Data.Graph.Util

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
toBonds : Smiles.Types.Bond -> Bonds
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
  C_sp3              | C_sp2              | C_sp2_carbonyl       | C_sp2_carboxyl   | C_sp_allene          | C_sp             |
  C_sp2_radical      | C_sp_radical       | C_planar_radical     | C_sp2_arom       |
  C_sp2_diradical    | C_sp3_diradical    | C_planar_plus        | C_sp2_plus       |
  C_sp_plus          | C_sp2_arom_plus    | C_planar_minus       | C_sp2_minus      |
  C_sp_minus         | C_sp2_arom_minus   | H_sgl                | H_plus           |
  H_minus            | O_sp3              | O_sp2                | O_sp2_sngl       | O_sp2_hydroxyl   | O_sp2_carbonyl   | O_sp3_radical    |
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

parameters (n    : Node)
           (adj  : Adj Bond (Atom l, List (Atom l,Bond)))

  doubleTo : Elem -> Nat
  doubleTo e = count isDoubleTo (snd adj.label)
    where isDoubleTo : (Atom l,Bond) -> Bool
          isDoubleTo (a,Dbl) = e == a.elem
          isDoubleTo _       = False

  inPiSystem : Bool
  inPiSystem = any (\x => any isPiBond (map snd x)) (map snd adj)

  refine : AtomType -> AtomType
  refine C_sp           = if doubleTo C == 2 then C_sp_allene else C_sp
  refine C_sp2          = if doubleTo O == 1 then C_sp2_carbonyl else C_sp2
  refine O_sp3          =
    if inPiSystem && (count (\(a,b) => a.hydrogen == 1) (snd adj.label)) == 1 then O_sp2_hydroxyl
    else if inPiSystem then O_sp2_sngl else O_sp3
  refine S_4_sp2        = if doubleTo O == 2 then S_4_planar3_oxide else S_4_sp2
  refine S_6_sp3        =
    if doubleTo O == 1 && doubleTo S == 1 then S_6_sp3_thionyl
    else if (doubleTo O + doubleTo N) == 2 then S_6_sp3_onyl
    else S_6_sp3
  refine at = at

  atArgs : ATArgs
  atArgs =
    let MkAtom el ar _ ch _ h := label (map fst adj)
        bs := foldMap (foldMap (toBonds . snd)) (map snd adj) <+> BS (cast h.value) 0 0
     in AA el ar ch bs

  -- Wrap-up the new atom type with the existing adjacency information
  relabel : AtomType -> Adj Bond (Atom (l,AtomType), List (Atom l,Bond))
  relabel aa = map (\x => (x,snd $ label adj)) $ (map . map) (,aa) (map fst adj)

  -- Helper funtion to determine all needed arguments to lookup the AtomType
  adj : Maybe (Adj Bond (Atom (l,AtomType), List (Atom l,Bond)))
  adj = relabel . refine <$> lookup atArgs atomTypes


-- Determines the AtomType if possible
firstAtomTypes :
  Graph Bond (Atom l, List (Atom l,Bond))
  -> Maybe (Graph Bond (Atom (l,AtomType), List (Atom l,Bond)))
firstAtomTypes g = MkGraph <$> traverseWithKey adj (graph g)


-- Changes the addition information from neighbour atoms with their bonds
-- or their AtomTypes to the new neighbour atoms
neighboursWithAT :
     Graph Bond (Atom (l,AtomType), _)  --List (Atom l,Bond))
  -> Graph Bond (Atom (l,AtomType), List (Atom (l,AtomType)))
neighboursWithAT g =
  pairWithNeighbours' (map fst g)

-------------------------------------------------------------------------------
-- Second Refinement

secondRefine : AtomType -> List AtomType -> AtomType
secondRefine O_sp2 xs =
  if elem C_sp2_carbonyl xs then O_sp2_carbonyl else O_sp2
secondRefine O_sp3 xs =
  if elem C_sp2_carboxyl xs then O_sp2_hydroxyl else O_sp2
secondRefine C_sp2_carbonyl xs =
  if elem O_sp2_carbonyl xs then C_sp2_carboxyl else C_sp2_carbonyl
secondRefine x xs = x

helpFunction :
     (Atom (l,AtomType), List (Atom (l,AtomType)))
  -> (Atom (l,AtomType), List (Atom (l,AtomType)))
helpFunction (a, li) =
  let newAT := secondRefine (snd a.label) (map (snd . label) li)
  in (map (\(lab,_) => (lab,newAT)) a, li)

secondAtomTypes :
     Graph Bond (Atom (l,AtomType), List (Atom (l,AtomType)))
  -> Graph Bond (Atom (l,AtomType), List (Atom (l,AtomType)))
secondAtomTypes g =
  neighboursWithAT $ MkGraph (map (map (helpFunction)) (graph g))


repeatRefine :
  Graph Bond (Atom (l,AtomType) , List (Atom (l,AtomType)))
  -> (c : Nat)
  -> Graph Bond (Atom (l,AtomType) , List (Atom (l,AtomType)))
repeatRefine x 0 = x
repeatRefine x (S k) = repeatRefine (secondAtomTypes x) k


-------------------------------------------------------------------------------
-- Main function

atomType :
  Graph Bond (Atom l)
  -> Maybe $ Graph Bond (Atom (l,AtomType))
atomType g =
  let prepare := pairWithNeighbours g
      first   := firstAtomTypes prepare
  in case first of
    Nothing => Nothing
    Just x  => case pairWithNeighbours' (map fst x) of
      v => Just $ map fst $ repeatRefine v 4

test :
  Graph Bond (Atom l)
  -> Show l
  => String
test g = case firstAtomTypes $ pairWithNeighbours g of
  Nothing => "Nothing"
  (Just x) => show x

-------------------------------------------------------------------------------
-- Test Section
-------------------------------------------------------------------------------

testMolecule : String
testMolecule = "c1cccc(c1)CC(=O)O"

testMolecule2 : String
testMolecule2 = "O=CO"

testAT1 : String -> String
testAT1 str =
  case parse str of
    Left x  => "Parsing step went wrong"
    Right x => case graphWithH x of
      Nothing => "ImplH went wrong"
      Just y  => case firstAtomTypes $ pairWithNeighbours y of
        Nothing => "First AtomType determination failed"
        Just z  => show z

testAT : String -> String
testAT str =
  case parse str of
    Left x  => "Parsing step went wrong"
    Right x => case graphWithH x of
      Nothing => "ImplH went wrong"
      Just y  => case atomType y of
        Nothing => "Atomtype determination went wrong"
        Just z  => show z
