module Test.Chem.AtomType

import Chem.AtomType
import Chem.Atom
import Text.Smiles
import Data.List
import Data.Graph

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
calcAtomTypes str = case parse str of
  Stuck _ _ => []
  End result => case Prelude.maybe Nothing toAtomTypes (graphWithH result) of
    Nothing => []
    Just g  =>
      map (\a => snd (Atom.label a.label))
          (sortBy (\x,y => compare x.node y.node) (labNodes g))


prop : (String,List AtomType) -> (PropertyName,Property)
prop (s,ats) = MkPair (fromString "SMILES \{s}") $ withTests 1 $ property $
  calcAtomTypes s === ats


-- Pairs of SMILES strings and expected list of atom types
pairs : List (String,List AtomType)
pairs = [("CCO"                      ,[C_sp3,C_sp3,O_sp3]),
         ("[O-]S(=O)(=S)[O-]"        ,[O_sp3_minus,S_6_sp3_thionyl,O_sp2,S_2_sp2,O_sp3_minus]),
         ("OS(=O)(=O)O"              ,[O_sp3,S_6_sp3_onyl,O_sp2,O_sp2,O_sp3]),
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