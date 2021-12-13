module Test.Main

import Hedgehog
import Test.Data.Graph
import Test.Data.GraphAlgorithms
import Test.Data.IntMap
import Test.Text.Molfile
import Test.Text.Smiles.Parser


main : IO ()
main = do 
  test [ Graph.props
       , IntMap.props
       , Parser.props
       , Molfile.props
       , GraphAlgorithms.props
       ]
