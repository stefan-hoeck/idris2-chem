module Test.Chem.AtomType

import Chem
import Chem.AtomType
import Data.List.Quantifiers.Extra
import Data.Maybe
import Data.List
import Text.Smiles
import Text.Smiles.Parser
import Text.Smiles.ImplH
import Hedgehog

%default total

{-
  * parse SMILES string
  * convert to graph annotated with atom types
  * extract list of atom types from graph
  * return `[]` if any of the above steps fails
-}

-- Only temporary. Will be in `Data.List.Quantifiers.Extra`
All (Show . f) ts => Show (Any f ts) where
  showPrec @{_ :: _} p (Here v)  = showCon p "Here" (showArg v)
  showPrec @{_ :: _} p (There v) = showCon p "There" (showArg v)


lErrors : List Type
lErrors = [HErr, ATErr, SmilesParseErr]

calcAtomTypes :
     Has HErr lErrors
  => Has ATErr lErrors
  => Has SmilesParseErr lErrors
  => String
  -> ChemRes lErrors (List AtomType)
calcAtomTypes str = do
  g1 <- parse str
  g2 <- graphWithH g1
  g3 <- atomType g2
  pure $ snd . label . label <$> sortBy (comparing node) (labNodes g3)

prop : (String,List AtomType) -> (PropertyName,Property)
prop (s,ats) = MkPair (fromString "SMILES \{s}") $ property1 $
               calcAtomTypes {lErrors} s === (Right ats)


-- Pairs of SMILES strings and expected list of atom types
pairs : List (String,List AtomType)
pairs =
  -- carbon
    -- sp3
  [  ("CC",[C_sp3,C_sp3]),
    -- sp2
     ("C=C",[C_sp2,C_sp2]),
    -- sp
     ("C#CC#C",[C_sp,C_sp,C_sp,C_sp]),
     ("C#[O+]",[C_sp,O_sp_plus]),
    -- planar plus
     ("[CH3+]",[C_planar_plus]),
    -- sp2 plus
     ("C=[CH+]",[C_sp2,C_sp2_plus]),
--  -- sp2 arom plus
--   ("c1cc[c+]cc1",[C_sp2_arom,C_sp2_arom,C_sp2_arom,C_sp2_arom_plus,C_sp2_arom,C_sp2_arom]),
    -- planar radical
     ("[CH3]",[C_planar_radical]),
    -- sp3 diradical
     ("C[CH]",[C_sp3,C_sp3_diradical]),
    -- sp2 radical
     ("C=[CH]",[C_sp2,C_sp2_radical]),
    -- sp2 diradical
     ("C=[C]",[C_sp2,C_sp2_diradical]),
    -- sp radical
     ("C#[C]",[C_sp,C_sp_radical]),
    -- carbonyl
     ("CC(=O)C",[C_sp3,C_carbonyl,O_carbonyl,C_sp3]),
    -- carboxyl
     ("CC(=O)O",[C_sp3,C_carboxyl,O_carbonyl,O_sp2_hydroxyl]),
    -- aldehyde
     ("CC(=O)",[C_sp3,C_aldehyde,O_carbonyl]),
    -- ester
     ("CC(=O)OC",[C_sp3,C_ester,O_carbonyl,O_ester,C_sp3]),
    -- arom
     ("c1ccccc1",[C_sp2_arom,C_sp2_arom,C_sp2_arom,C_sp2_arom,C_sp2_arom,C_sp2_arom]),
    -- allene
     ("C=C=C=C",[C_sp2,C_sp_allene,C_sp_allene,C_sp2]),

  -- Hydrogen
     ("[H]O[H]",[H_sgl,O_sp3,H_sgl]),
     ("[H-]",[H_minus]),
     ("[H+]",[H_plus]),

  -- Oxygen
    -- hydroxyl
     ("CCO",[C_sp3,C_sp3,O_sp3_hydroxyl]),
    -- hydroxyl plus
     ("CC[OH2+]",[C_sp3,C_sp3,O_sp3_hydroxyl_plus]),
    -- hydroxyl sp2
     ("C=CO",[C_sp2,C_sp2,O_sp2_hydroxyl]),
    -- hydroxyl plus sp2
     ("C=C[OH2+]",[C_sp2,C_sp2,O_sp2_hydroxyl_plus]),
    -- sp3
     ("COC",[C_sp3,O_sp3,C_sp3]),
    -- carbonyl
     ("CC(=O)C",[C_sp3,C_carbonyl,O_carbonyl,C_sp3]),
    -- carbonyl plus
     ("CC(=[OH+])C",[C_sp3,C_carbonyl,O_carbonyl_plus,C_sp3]),
    -- ester
     ("C(=O)OC",[C_ester,O_carbonyl,O_ester,C_sp3]),
    -- sp2
     ("C=COC=C",[C_sp2,C_sp2,O_sp2_snglB,C_sp2,C_sp2]),
     ("CCOC=C",[C_sp3,C_sp3,O_sp2_snglB,C_sp2,C_sp2]),
    -- arom
     ("c1occc1",[C_sp2_arom,O_sp2_arom,C_sp2_arom,C_sp2_arom,C_sp2_arom]),
    -- phenol
     ("Oc1ccccc1",[O_sp2_phenol,C_sp2_arom,C_sp2_arom,C_sp2_arom,C_sp2_arom,C_sp2_arom,C_sp2_arom]),
    -- singel bond sp2
     ("COc1ccccc1",[C_sp3,O_sp2_snglB,C_sp2_arom,C_sp2_arom,C_sp2_arom,C_sp2_arom,C_sp2_arom,C_sp2_arom]),
    -- sp3 radical
     ("[OH]",[O_sp3_radical]),
    -- sp2 radical
     ("[O]c1ccccc1",[O_sp2_radical,C_sp2_arom,C_sp2_arom,C_sp2_arom,C_sp2_arom,C_sp2_arom,C_sp2_arom]),
    -- sp3 plus
     ("[OH3+]",[O_sp3_plus]),
    -- sp2 plus
     ("S=[OH+]",[S_2_sp2,O_sp2_plus]),
    -- sp2 plus
     ("C#[O+]",[C_sp,O_sp_plus]),
    -- sp3 minus
     ("CC[O-]",[C_sp3,C_sp3,O_sp3_minus]),
    -- sp2 minus
     ("C=C[O-]",[C_sp2,C_sp2,O_sp2_minus]),  -- not fully correct, only sp2 if the neighbouring atoms inclueds a C_sp2!

    -- sp3 minus
     ("CC[O-]",[C_sp3,C_sp3,O_sp3_minus]),
    -- sp3 radical
     ("CC[O]",[C_sp3,C_sp3,O_sp3_radical])
    -- radical cation
      -- not found a way to store it in a smiles string

  ]

export
props : Group
props = MkGroup "AtomType Properties" $ map prop pairs
