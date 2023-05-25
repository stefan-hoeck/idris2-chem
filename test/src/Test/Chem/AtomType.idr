module Test.Chem.AtomType

import Chem
import Chem.AtomType
import Data.Maybe
import Data.List
import Text.Smiles
import Hedgehog

%default total

{-
  * parse SMILES string
  * convert to graph annotated with atom types
  * extract list of atom types from graph
  * return `[]` if any of the above steps fails

  Use `labNodes` to extract labeled nodes from the graph
  and sort them by key (using `Data.List.sortBy`) before
  extracting the labels, because they might be listed in arbitrary
  order.
-}
calcAtomTypes : String -> List AtomType
calcAtomTypes str = fromMaybe [] $ do
  g1 <- either (const Nothing) Just $ parse str
  g2 <- graphWithH g1
  g3 <- atomType g2
  pure $ snd . label . label <$> sortBy (comparing node) (labNodes g3)

prop : (String,List AtomType) -> (PropertyName,Property)
prop (s,ats) = MkPair (fromString "SMILES \{s}") $ property1 $
  calcAtomTypes s === ats


-- hock: While these tests are surely useful, the are kind of arbitrary
--       and hard to digest if they go wrong. Try to provide one or several
--       minimal examples for every atom type to make sure the conversion
--       works correctly.
--
-- Pairs of SMILES strings and expected list of atom types
pairs : List (String,List AtomType)
pairs =
  -- Hydrogen
  [  ("[H]O[H]",[H_sgl,O_sp3,H_sgl]),
     ("[H-]",[H_minus]),
     ("[H+]",[H_plus]),
  -- Oxygen
    -- hydroxyl
     ("CCO",[C_sp3,C_sp3,O_sp3_hydroxyl]),
    -- hydroxyl sp2
     ("C=CO",[C_sp2,C_sp2,O_sp2_hydroxyl]),
    -- carbonyl
     ("C(=O)C",[C_sp2_carbonyl,O_sp2_carbonyl,C_sp3]),
    -- sp2
     ("C=COC=C",[C_sp2,C_sp2,O_sp2_snglB,C_sp2,C_sp2]),
    -- sp3
     ("COC",[C_sp3,O_sp3,C_sp3]),
    -- phenol
     ("Oc1ccccc1",[O_sp2_phenol,C_sp2_arom,C_sp2_arom,C_sp2_arom,C_sp2_arom,C_sp2_arom,C_sp2_arom]),
    -- sp3 radical
     ("[OH]",[O_sp3_radical]),
    -- sp3 plus
     ("[OH3+]",[O_sp3_plus]),
    -- sp2 plus
     ("C=[OH+]",[C_sp2_carbonyl,O_sp2_plus]), -- own type O_sp2_hydroxyl_plus

    -- sp2 minus
     ("C=C[O-]",[C_sp2,C_sp2,O_sp2_minus]),
    -- sp3 minus
     ("CC[O-]",[C_sp3,C_sp3,O_sp3_minus]),
  -- carbon
    -- arom
     ("c1ccccc1",[C_sp2_arom,C_sp2_arom,C_sp2_arom,C_sp2_arom,C_sp2_arom,C_sp2_arom])
  ]
{-
pairs = [("CCO"                      ,[C_sp3,C_sp3,O_sp3_hydroxyl]),
         ("[O-]S(=O)(=S)[O-]"        ,[O_sp3_minus,S_6_sp3_thionyl,O_sp2,S_2_sp2,O_sp3_minus]),
         ("OS(=O)(=O)O"              ,[O_sp3_hydroxyl,S_6_sp3_onyl,O_sp2,O_sp2,O_sp3_hydroxyl]),
         ("COc1ccccc1OC(=O)Cc2ccccc2",[C_sp3,O_sp2_snglB,C_sp2_arom,C_sp2_arom,C_sp2_arom,
                                       C_sp2_arom,C_sp2_arom,C_sp2_arom,O_sp2_snglB,C_sp2_carboxyl,O_sp2_carbonyl,
                                       C_sp3,C_sp2_arom,C_sp2_arom,C_sp2_arom,C_sp2_arom,
                                       C_sp2_arom,C_sp2_arom]),
         ("COc1ccccc1OC[C@@H](CO)O"  ,[C_sp3,O_sp2_snglB,C_sp2_arom,C_sp2_arom,C_sp2_arom,
                                      C_sp2_arom,C_sp2_arom,C_sp2_arom,O_sp2_snglB,C_sp3,
                                      C_sp3,C_sp3,O_sp3_hydroxyl,O_sp3_hydroxyl]),
         ("[H-]"                     ,[H_minus])
         ]
         -}

export
props : Group
props = MkGroup "AtomType Properties" $ map prop pairs
