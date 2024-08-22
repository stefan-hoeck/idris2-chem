module Test.Chem.Query

import Chem
import Chem.Aromaticity
import Chem.Query
import Data.Vect
import Hedgehog
import Text.Smiles
import Text.Smiles.AtomType

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

readMol : String -> Either String (Graph SmilesBond SmilesAtomAT)
readMol = map perceiveSmilesAtomTypes . readSmiles'

testQuery : String -> String -> Maybe (List Nat) -> Property
testQuery x y vs = property1 $ test === Right vs
  where
    test : Either String (Maybe $ List Nat)
    test = do
      g1 <- readMol x
      g2 <- readMol y
      pure $ substructure (smilesQuery g1) (smilesTarget g2)

--------------------------------------------------------------------------------
-- Chains
--------------------------------------------------------------------------------

prop_ether : Property
prop_ether = testQuery "CCO" "CCCCOC" (Just [2,3,4])

prop_ethanol : Property
prop_ethanol = testQuery "CCO[H]" "CCCCO" (Just [2,3,4])

prop_ethanolExplicit : Property
prop_ethanolExplicit = testQuery "CCO[H]" "CCCCO[H]" (Just [2,3,4])

prop_ethanolFail : Property
prop_ethanolFail = testQuery "CCO[H]" "CCCCOC" Nothing

prop_acid : Property
prop_acid = testQuery "C(O)=O" "CCC(C(=O)O)CCC" (Just [3,5,4])

prop_aromatic : Property
prop_aromatic =
  testQuery "C1=CC(C)=NC=C1" "C1=CC=C(C)N=C1" $ Just $ [1,2,3,4,5,6,0]

prop_amine : Property
prop_amine =
  testQuery "C(C12)N3C1.C2.C3" "O=C(CCC=1C=CC=CC=1)N1CCC1C=1C=CC=CC=1" Nothing

prop_amine2 : Property
prop_amine2 =
  testQuery "CN(C)C" "C1NC1" $ Nothing



--------------------------------------------------------------------------------
-- props
--------------------------------------------------------------------------------

export
props : Group
props =
  MkGroup "Query"
    [ ("prop_ether", prop_ether)
    , ("prop_ethanol", prop_ethanol)
    , ("prop_ethanolExplicit", prop_ethanolExplicit)
    , ("prop_ethanolFail", prop_ethanolFail)
    , ("prop_acid", prop_acid)
    , ("prop_aromatic", prop_aromatic)
    , ("prop_amine", prop_amine)
    , ("prop_amine2", prop_amine2)
    ]
