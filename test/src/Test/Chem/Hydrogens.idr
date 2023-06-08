module Test.Chem.Hydrogens

import Chem
import Chem.Hydrogens
import Test.Data.Graph
import Text.Smiles

import Hedgehog

-- Graphen generieren?
graph : Gen (Graph Bond (Elem,Nat))
graph = ?graph_rhs

-- Graph vorher und nachher vergleichen
prop_expand_roundTrip : Property
prop_expand_roundTrip =
  ?prop_expand_roundTrip_rhs $ \g => ?noExplicitHs (testExpand g) === g
