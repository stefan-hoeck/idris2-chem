module Test.Chem.Hydrogens

import Chem
import Chem.Hydrogens
import Test.Data.Graph
import Text.Smiles
import Test.Text.Smiles.Generators

import Hedgehog

notH : Gen Elem
notH = map (\x => if x == H then C else x) element

pair : Gen (Elem,Nat)
pair = [| MkPair notH (nat $ linear 0 10) |]

--pair = element $  map (,0) ?something
--               ++ map (,1) ?something2
--               ++ map (,2) ?something3
--               ++ map (,3) ?something4
--               ++ map (,4) ?something5

-- from github:
-- genAtom : Gen (Elem,Bool)
-- genAtom = element $  map (,False) [B,C,N,O,F,S,Cl,P,Br,I]
--                   ++ map (,True)  [B,C,N,O,F,S,Cl,P,Br,I]


-- Graphen generieren?
graph : Gen (Graph Bond (Elem,Nat))
graph = lgraph (linear 0 50) (linear 0 50) bond pair

-- Graph vorher und nachher vergleichen
prop_expand_roundTrip : Property
prop_expand_roundTrip =
  property $ do
    g <- forAll graph
    noExplicitHs (noImplicitHs g) === g

export
props : Group
props = MkGroup "Hydrogen Properties"
  [ ("prop_expand_roundTrip", prop_expand_roundTrip) ]
