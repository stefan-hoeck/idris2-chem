module Test.Text.Smiles.Lexer

import Test.Text.Smiles.Generators

%default total

lexSingle :
     Show a
  => Eq a
  => Interpolation a
  => Gen a
  -> (a -> SmilesToken)
  -> Property
lexSingle as f = property $ do
  v <- forAll as
  let enc := interpolate v
  footnote "Encoded: \{enc}"
  (map fst <$> lexSmiles enc) === Right [f v]

lexMany :
     Show a
  => Eq a
  => Interpolation a
  => Gen a
  -> (a -> SmilesToken)
  -> Property
lexMany as f = property $ do
  vs <- forAll (list (linear 0 100) as)
  let enc := concatMap interpolate vs
  footnote "Encoded: \{enc}"
  (map fst <$> lexSmiles enc) === Right (map f vs)

prop_bond : Property
prop_bond = lexSingle bond TB

prop_atom : Property
prop_atom = lexSingle atom TA

prop_ringNr : Property
prop_ringNr = lexSingle ringNr TR

prop_token : Property
prop_token = lexSingle token id

prop_bonds : Property
prop_bonds = lexMany bond TB

prop_atoms : Property
prop_atoms = lexMany atom TA

prop_ringNrs : Property
prop_ringNrs = lexMany ringNr TR

prop_tokens : Property
prop_tokens = lexMany token id

export
props : Group
props = MkGroup "Text.Smiles.Lexer"
  [("prop_bond", prop_bond)
  ,("prop_atom", prop_atom)
  ,("prop_ringNr", prop_ringNr)
  ,("prop_token", prop_token)
  ,("prop_bonds", prop_bonds)
  ,("prop_atoms", prop_atoms)
  ,("prop_ringNrs", prop_ringNrs)
  ,("prop_tokens", prop_tokens)
  ]
