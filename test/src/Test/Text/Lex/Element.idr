module Test.Text.Lex.Element

import Chem.Element
import Text.Lex.Element
import Hedgehog

%default total

prop_lexElement : Property
prop_lexElement =
  withTests 1 . property . for_ elements $ \e =>
    readElement (symbol e) === Just e

export
props : Group
props = MkGroup "Text.Lex.Element"
  [ ("prop_lexElement", prop_lexElement)
  ]
