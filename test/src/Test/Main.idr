module Test.Main

import Hedgehog
import Test.Data.Graph
import Test.Chem.Elem
import Test.Chem.AtomType
import Test.Text.Lex.Elem
import Test.Text.Lex.Formula
import Test.Text.Molfile
import Test.Text.Smiles.Lexer
import Test.Text.Smiles.Parser

main : IO ()
main =
  test
    [ Lex.Elem.props
    , Chem.Elem.props
    , Smiles.Lexer.props
    , Smiles.Parser.props
    , Molfile.props
    , Formula.props
    ]
