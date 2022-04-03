module Test.Main

import Hedgehog
import Test.Data.Graph
import Test.Data.IntMap
import Test.Text.Molfile
import Test.Text.Smiles.Parser
import Test.Data.SubGraph

main : IO ()
main = do
       _ <- testUllImp
       test [ Graph.props 
            , IntMap.props
            , Parser.props
            , Molfile.props
            ]
