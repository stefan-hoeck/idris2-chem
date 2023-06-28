module Test.Chem.Hydrogens

import Chem
import Chem.Hydrogens
import Test.Data.Graph
import Text.Smiles
import Test.Text.Smiles.Generators

import Hedgehog

-- No hydrogens can be generated
notH : Gen Elem
notH = map (\x => if x == H then C else x) element

pair : Gen (Elem,Nat)
pair = [| MkPair notH (nat $ linear 0 10) |]

-- Generate graphs
graph : Gen (Graph Bond (Elem,Nat))
graph = lgraph (linear 0 50) (linear 0 50) bond pair

-- Expand and then collapse an originally collapsed graph
prop_expand_roundTrip : Property
prop_expand_roundTrip =
  property $ do
    g <- forAll graph
    noExplicitHs (noImplicitHs g) === g

export
props : Group
props = MkGroup "Hydrogen Properties"
  [ ("prop_expand_roundTrip", prop_expand_roundTrip) ]
