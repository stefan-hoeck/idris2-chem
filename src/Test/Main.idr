module Test.Main

import Hedgehog
import Test.Data.Graph
import Test.Data.IntMap
import Test.Text.Molfile

main : IO ()
main = test [ Graph.props 
            , IntMap.props
            , Molfile.props
            ]
