module Test.Main

import Hedgehog
import Test.Data.IntMap
import Test.Text.Molfile

main : IO ()
main = test [ Molfile.props
            , IntMap.props
            ]
