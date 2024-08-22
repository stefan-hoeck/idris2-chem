module Test.Chem.QSAR.JPlogP

import Chem
import Chem.Aromaticity
import Chem.QSAR.JPlogP
import Text.Smiles
import Text.Smiles.AtomType
import Hedgehog

%default total

readArom : String -> Either String (Graph (AromBond SmilesBond) SmilesAtomAT)
readArom = map (aromatize atomType . perceiveSmilesAtomTypes) . readSmiles'

testJPlogP : String -> Double -> Property
testJPlogP s x =
  property1 $ case readArom s of
    Left err      => failWith Nothing err
    Right (G o g) => do
      footnoteShow (map (jpLogPContrib g) (nodes g))
      jpLogP g === Just x

export
props : Group
props =
  MkGroup "JPlogP"
    [ ("prop_pyridin", testJPlogP "C1=CC=CC=N1" 0.9118821610432022)
    , ("prop_pyridin_explicit", testJPlogP "C1([H])=C([H])C([H])=C([H])C([H])=N1" 0.9118821610432022)
    , ("prop_propionicacid", testJPlogP "CCC(=O)O" 0.3156266695201928)
    , ("prop_acetonitrile", testJPlogP "CC#N" 0.4470176804052204)
    , ("prop_aniline", testJPlogP "NC1=CC=CC=C1" 1.2292858121641856)
    , ("prop_fluorobenzene", testJPlogP "FC1=CC=CC=C1" 2.0146287965757566)
    ]
