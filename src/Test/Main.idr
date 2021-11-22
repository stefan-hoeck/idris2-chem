module Test.Main

import Hedgehog
import Test.Data.Graph
import Test.Data.GraphAlgorithms
import Test.Data.IntMap
import Test.Text.Molfile
import Test.Text.Smiles.Parser


main : IO ()
main = do 
       showAlgoResults  -- TODO: Improve. Was just here to visualize the output
       test [ Graph.props
       , IntMap.props
       , Parser.props
       , Molfile.props
       ]
