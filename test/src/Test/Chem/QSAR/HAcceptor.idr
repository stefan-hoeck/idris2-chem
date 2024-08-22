module Test.Chem.QSAR.HAcceptor

import Chem
import Chem.Aromaticity
import Chem.QSAR.HAcceptor
import Text.Smiles
import Text.Smiles.AtomType
import Hedgehog

%default total

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

readArom : String -> Either String (Graph (AromBond SmilesBond) SmilesAtomAT)
readArom = map (aromatize atomType . perceiveSmilesAtomTypes) . readSmiles'

testAcceptors : String -> Nat -> Property
testAcceptors s n = property1 $ map acceptors (readArom s) === Right n
  where
    acceptors : Graph (AromBond SmilesBond) SmilesAtomAT -> Nat
    acceptors (G _ g) = hAcceptorCount g

export
props : Group
props =
  MkGroup "HDonor"
    [ ("prop_benzene", testAcceptors "C1C=CC=CC=1" 0)
    , ("prop_phenol", testAcceptors "C1C=C(O)C=CC=1" 1)
    , ("prop_phenolether", testAcceptors "C1C=C(OC)C=CC=1" 0)
    , ("prop_anilin", testAcceptors "C1C=C(N)C=CC=1" 1)
    , ("prop_glycine", testAcceptors "NCC(=O)O" 3)
    , ("prop_glycine_ionic", testAcceptors "[NH3+]CC(=O)[O-]" 2)
    , ("prop_triethylamine", testAcceptors "CCN(CC)CC" 1)
    , ("prop_triethylammonium", testAcceptors "CC[NH+](CC)CC" 0)
    , ("prop_noxide", testAcceptors "CCNO" 0)
    ]
