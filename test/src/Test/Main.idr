module Test.Main

import Hedgehog
import Test.Data.Graph
import Test.Text.Molfile
import Test.Text.Smiles.Parser
import Test.Chem.AtomType

main : IO ()
main = test [ Graph.props
        --    , Parser.props
        --    , Molfile.props
        --    , AtomType.props
            ]
