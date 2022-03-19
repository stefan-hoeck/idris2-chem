module Test.Data.SubGraph

import Hedgehog


-- Generators -----------------------------------------------------------------


-- Group ----------------------------------------------------------------------
export
props : Group
props = MkGroup "Graph Properties"
          []

