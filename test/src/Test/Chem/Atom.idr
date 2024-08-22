module Test.Chem.Atom

import Hedgehog
import Text.Smiles
import Text.Smiles.AtomType

%default total

readArom : String -> Either String (Graph SmilesBond SmilesAtomAT)
readArom = map (perceiveSmilesAtomTypes) . readSmiles'

toNat : MolecularMass -> Nat
toNat = cast . (* 1_000_000) . value

testMass : String -> Nat -> Property
testMass s mass =
  property1 $ map (toNat . foldMap molecularMass) (readArom s) === Right mass

export
props : Group
props =
  MkGroup "Chem.Atom"
    [("prop_ethanol_mass", testMass "CCO" 46_068_521)
    ,("prop_mol1_mass", testMass "FS(=O)(=O)c1ccc(cc1)CC(=O)O" 218_203_580)
    ,("prop_mol2_mass", testMass "ClS(=O)(=O)c1ccc(cc1)CC(=O)O" 234_658_114)
    ]

