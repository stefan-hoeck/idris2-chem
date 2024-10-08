module Test.Text.Smiles.Parser

import Data.SOP
import Data.Vect
import Test.Text.Smiles.Generators

%default total

parse' : String -> ChemRes [SmilesParseErr] SmilesGraph
parse' s = readSmiles s

--------------------------------------------------------------------------------
--          Properties
--------------------------------------------------------------------------------

parse_atom : Property
parse_atom = property $ do
  a <- forAll atom
  let str = interpolate a
  footnote "Encoded: \{str}"
  parse' str === Right (G 1 $ mkGraph [a] Nil)

parse_bond : Property
parse_bond = property $ do
  [a1,a2,b] <- forAll $ np [atom,atom,bond]
  let str = "\{a1}\{b}\{a2}"
  footnote "Encoded: \{str}"
  parse' str === Right (G 2 $ mkGraph [a1, a2] [E 0 1 b])

parse_branch : Property
parse_branch = property $ do
  [a1,a2,a3,b1,b2] <- forAll $ np [atom,atom,atom,bond,bond]
  let str = "\{a1}(\{b1}\{a2})\{b2}\{a3}"
  footnote "Encoded: \{str}"
  parse' str === Right (G 3 $ mkGraph [a1, a2, a3] [E 0 1 b1, E 0 2 b2])

parse_ring : Property
parse_ring = property $ do
  [a1,a2,b1] <- forAll $ np [atom,atom,bond]
  let str = "\{a1}\{b1}1.\{a2}1"
  footnote "Encoded: \{str}"
  parse' str === Right (G 2 $ mkGraph [a1,a2] [E 0 1 b1])

--------------------------------------------------------------------------------
--          props
--------------------------------------------------------------------------------

export
props : Group
props = MkGroup "SMILES Properties"
  [ ("parse_atom", parse_atom)
  , ("parse_bond", parse_bond)
  , ("parse_branch", parse_branch)
  , ("parse_ring", parse_ring)
  ]
