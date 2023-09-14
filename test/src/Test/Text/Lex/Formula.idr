module Test.Text.Lex.Formula

import Chem
import Chem.Formula
import Data.List.Quantifiers.Extra
import Test.Chem.Formula
import Text.Lex.Formula

import Hedgehog

%default total

prop_roundTrip : Property
prop_roundTrip = property $ do
  f <- forAll formula
  Right f === readFormula {es = [FormulaErr]} "\{f}"

export
props : Group
props = MkGroup "Text.Lex.Formula"
  [ ("prop_roundTrip", prop_roundTrip)
  ]

