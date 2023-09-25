module Test.Text.Lex.Formula

import Test.Chem.Generators
import Text.Lex.Formula

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

