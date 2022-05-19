module Test.Main

import Hedgehog
import Test.Data.Graph
import Test.Text.Molfile
import Test.Text.Smiles.Parser
import Test.Data.SubGraph
import Test.Data.Isomorphism

main : IO ()
main = do
       _ <- subgraphTests
       test [ Graph.props
            , Parser.props
            , Molfile.props
            , Isomorphism.props
            ]
