module Test.Main

import Hedgehog
import Test.Data.Graph
import Test.Text.Molfile
import Test.Text.Smiles.Parser

main : IO ()
main = test [ Graph.props
            , Parser.props
            , Molfile.props
            ]
