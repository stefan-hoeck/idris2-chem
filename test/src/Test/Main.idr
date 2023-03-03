module Test.Main

import Hedgehog
import Test.Data.Graph
import Test.Chem.AtomType
import Test.Text.Lex.Element
import Test.Text.Molfile
import Test.Text.Smiles.Parser

main : IO ()
main = test [ Graph.props
            , Lex.Element.props
        --    , Parser.props
        --    , Molfile.props
        --    , AtomType.props
            ]
