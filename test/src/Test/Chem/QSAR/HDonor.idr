module Test.Chem.QSAR.HDonor

import Chem
import Chem.Aromaticity
import Chem.QSAR.HDonor
import Text.Smiles
import Text.Smiles.AtomType
import Hedgehog

%default total

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

readArom : String -> Either String (Graph (AromBond SmilesBond) SmilesAtomAT)
readArom = map (aromatize atomType . perceiveSmilesAtomTypes) . readSmiles'

testDonors : String -> Nat -> Property
testDonors s n = property1 $ map donors (readArom s) === Right n
  where
    donors : Graph (AromBond SmilesBond) SmilesAtomAT -> Nat
    donors (G _ g) = hDonorCount g

export
props : Group
props =
  MkGroup "HDonor"
    [ ("prop_benzene", testDonors "C1C=CC=CC=1" 0)
    , ("prop_phenol", testDonors "C1C=C(O)C=CC=1" 1)
    , ("prop_phenolether", testDonors "C1C=C(OC)C=CC=1" 0)
    , ("prop_anilin", testDonors "C1C=C(N)C=CC=1" 1)
    , ("prop_glycine", testDonors "NCC(=O)O" 2)
    , ("prop_glycine_ionic", testDonors "[NH3+]CC(=O)[O-]" 1)
    , ("prop_triethylamine", testDonors "CCN(CC)CC" 0)
    , ("prop_triethylammonium", testDonors "CC[NH+](CC)CC" 1)
    ]
