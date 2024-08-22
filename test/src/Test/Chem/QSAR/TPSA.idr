module Test.Chem.QSAR.TPSA

import Chem
import Chem.Aromaticity
import Chem.QSAR.TPSA
import Text.Smiles
import Text.Smiles.AtomType
import Hedgehog

%default total

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

readArom : String -> Either String (Graph (AromBond SmilesBond) SmilesAtomAT)
readArom = map (aromatize atomType . perceiveSmilesAtomTypes) . readSmiles'

testTPSA : String -> Double -> Property
testTPSA s n = property1 $ map tpsa_ (readArom s) === Right n
  where
    tpsa_ : Graph (AromBond SmilesBond) SmilesAtomAT -> Double
    tpsa_ (G _ g) = tpsa g

export
props : Group
props =
  MkGroup "TPSA"
    [ ("prop_acetic", testTPSA "O=C(O)CC" 37.3)
    , ("prop_nitrile", testTPSA "C=NC(CC#N)N(C)C" 39.39)
    , ("prop_nitro", testTPSA "CCCN(=O)=O" 45.82)
    , ("prop_cycle", testTPSA "C#N=CC(CNC)N1CC1" 28.64)
    , ("prop_pyridine", testTPSA "C1=CC=CC=N1" 12.89)
    , ("prop_explicitH", testTPSA "[H][N+]([H])(C)C" 16.61)
    , ("prop_none", testTPSA "C(I)I" 0.0)
    , ("prop_acetal", testTPSA "C(O)O" 40.46)
    , ("prop_ring", testTPSA "C1CCCC1CCC2CCCNC2" 12.03)
    ]
