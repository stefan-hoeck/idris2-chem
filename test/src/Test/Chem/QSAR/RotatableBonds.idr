module Test.Chem.QSAR.RotatableBonds

import Chem
import Chem.QSAR.RotatableBonds
import Data.Graph.Indexed.Ring.Bonds
import Data.Graph.Indexed.Ring.Util
import Data.SortedSet
import Hedgehog
import Text.Smiles
import Text.Smiles.AtomType

%default total

readArom : String -> Either String (Graph SmilesBond SmilesAtomAT)
readArom = map (perceiveSmilesAtomTypes) . readSmiles'

testRotBonds :
     String
  -> (includeTerminals, excludeAmides : Bool)
  -> Nat
  -> Property
testRotBonds s it ea n = property1 $ map rotBonds (readArom s) === Right n
  where
    rotBonds : Graph SmilesBond SmilesAtomAT -> Nat
    rotBonds (G o g) =
      let rs := ringBonds g
       in rotatableBondCount rs it ea g

prop_bicycle : Property
prop_bicycle = testRotBonds "CC2CCC(C1CCCCC1)CC2" True False 2

prop_ethaneWithTerminals : Property
prop_ethaneWithTerminals = testRotBonds "CC" True False 1

prop_ethane : Property
prop_ethane = testRotBonds "CC" False False 0

prop_ethaneExplicitHs : Property
prop_ethaneExplicitHs = testRotBonds "[H]C([H])([H])C([H])([H])[H]" False False 0

prop_butaneWithTerminals : Property
prop_butaneWithTerminals = testRotBonds "CCCC" True False 3

prop_butane : Property
prop_butane = testRotBonds "CCCC" False False 1

prop_amide : Property
prop_amide = testRotBonds "CCNC(=O)CC(C)C" False False 4

prop_amideExcluded : Property
prop_amideExcluded = testRotBonds "CCNC(=O)CC(C)C" False True 3

export
props : Group
props =
  MkGroup "RotatableBonds"
    [ ("prop_bicycle", prop_bicycle)
    , ("prop_ethaneWithTerminals", prop_ethaneWithTerminals)
    , ("prop_ethane", prop_ethane)
    , ("prop_ethaneExplicitHs", prop_ethaneExplicitHs)
    , ("prop_butaneWithTerminals", prop_butaneWithTerminals)
    , ("prop_butane", prop_ethane)
    , ("prop_amide", prop_amide)
    , ("prop_amideExcluded", prop_amideExcluded)
    ]
