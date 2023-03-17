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
  g3 <- toAtomTypes g2
  pure $ snd . label . label <$> sortBy (comparing node) (labNodes g3)

prop : (String,List AtomType) -> (PropertyName,Property)
prop (s,ats) = MkPair (fromString "SMILES \{s}") $ property1 $
  calcAtomTypes s === ats


-- hock: While these tests are surely useful, the are kind of arbitrary
--       and hard to digest if they go wrong. Try to provide one or several
--       minimal examples for every atom type to make sure the conversion
--       works correctly.
--
--       The third example is currently not correct (I changed it), because
--       we consider the bonds going to neighbours instead of the neighbours
--       themselves.
-- Pairs of SMILES strings and expected list of atom types
pairs : List (String,List AtomType)
pairs = [("CCO"                      ,[C_sp3,C_sp3,O_sp3]),
         ("[O-]S(=O)(=S)[O-]"        ,[O_sp3_minus,S_6_sp3_thionyl,O_sp2,S_2_sp2,O_sp3_minus]),
         ("OS(=O)(=O)O"              ,[O_sp2,S_6_sp3_onyl,O_sp2,O_sp2,O_sp2]),
         ("COc1ccccc1OC(=O)Cc2ccccc2",[C_sp3,O_sp2,C_sp2_arom,C_sp2_arom,C_sp2_arom,
                                       C_sp2_arom,C_sp2_arom,C_sp2_arom,O_sp2,C_sp2,
                                       O_sp2,C_sp3,C_sp2_arom,C_sp2_arom,C_sp2_arom,
                                       C_sp2_arom,C_sp2_arom,C_sp2_arom]),
         ("COc1ccccc1OC[C@@H](CO)O"  ,[C_sp3,O_sp2,C_sp2_arom,C_sp2_arom,C_sp2_arom,
                                      C_sp2_arom,C_sp2_arom,C_sp2_arom,O_sp2,C_sp3,
                                      C_sp3,C_sp3,O_sp3,O_sp3]),
         ("[H-]"                     ,[H_minus])
         ]

export
props : Group
props = MkGroup "AtomType Properties" $ map prop pairs
