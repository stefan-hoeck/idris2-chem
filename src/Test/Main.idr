module Test.Main

import Hedgehog
import Test.Data.Graph
import Test.Text.Molfile
import Test.Text.Smiles.Parser
import Test.Data.SubGraph

main : IO ()
main = do
       _ <- subgraphTests
       test [ Graph.props
            , Parser.props
            , Molfile.props
            ]
