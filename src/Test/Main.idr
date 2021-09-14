module Test.Main

import Hedgehog
import Test.Text.Molfile

main : IO ()
main = test . pure $ Test.Text.Molfile.props
