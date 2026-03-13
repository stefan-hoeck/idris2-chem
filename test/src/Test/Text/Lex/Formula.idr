module Test.Text.Lex.Formula

import Test.Chem.Generators
import Text.Lex.Formula
import Text.ParseError

%default total

prop_roundTrip : Property
prop_roundTrip = property $ do
  f <- forAll formula
  Right f === parseFormula "\{f}"

export
props : Group
props = MkGroup "Text.Lex.Formula"
  [ ("prop_roundTrip", prop_roundTrip)
  ]

