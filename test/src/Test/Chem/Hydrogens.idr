module Test.Chem.Hydrogens

import Chem
import Chem.Hydrogens
import Test.Data.Graph
import Text.Smiles
import Test.Text.Smiles.Generators

import Hedgehog


pair : Gen (Elem,Nat)
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
  property . ?hole $ \g => noExplicitHs (testExpand g) === g
