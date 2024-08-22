module Test.Main

import Hedgehog
import Test.Chem.Aromaticity
import Test.Chem.Atom
import Test.Chem.AtomType
import Test.Chem.CyByBug
import Test.Chem.Elem
import Test.Chem.Query
import Test.Chem.QSAR.HDonor
import Test.Chem.QSAR.HAcceptor
import Test.Chem.QSAR.JPlogP
import Test.Chem.QSAR.RotatableBonds
import Test.Chem.QSAR.TPSA
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
    , Aromaticity.props
    , Query.props
    , CyByBug.props
    , HDonor.props
    , HAcceptor.props
    , RotatableBonds.props
    , TPSA.props
    , JPlogP.props
    , Atom.props
    ]
