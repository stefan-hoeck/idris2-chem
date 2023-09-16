module Test.Text.Lex.Elem

import Chem
import Data.Finite
import Text.Lex.Elem
import Hedgehog

%default total

prop_lexElement : Property
prop_lexElement =
  withTests 1 . property . for_ values $ \e =>
    readElement (symbol e) === Just e

export
props : Group
props = MkGroup "Text.Lex.Element"
  [ ("prop_lexElement", prop_lexElement)
  ]
