module Test.Main

import Hedgehog
import Test.Data.Graph
import Test.Chem.Element
import Test.Chem.AtomType
import Test.Chem.Hydrogens
import Test.Text.Lex.Element
import Test.Text.Molfile
import Test.Text.Smiles.Lexer
import Test.Text.Smiles.Parser

main : IO ()
main = test
  [ Hydrogens.props
  , Graph.props
  , Lex.Element.props
  , Chem.Element.props
  , Smiles.Lexer.props
  , Smiles.Parser.props
  , Molfile.props
  , AtomType.props
  ]
