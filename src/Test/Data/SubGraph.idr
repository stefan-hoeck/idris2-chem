module Test.Data.SubGraph

import Hedgehog
import Text.Smiles
import Data.SubGraph.UllmannImp

-- Generators -----------------------------------------------------------------


-- Group ----------------------------------------------------------------------
export
props : Group
props = MkGroup "Graph Properties"
          []





-- Test the functionality -----------------------------------------------------

-- TODO: Mapping is currently in reversed order, but that shouldn't be a problem
-- :module Text.Smiles
-- :let qry = case parse "CCO" of End x => x
-- :let trg = case parse "CCCO" of End x => x
-- :let stt = MkSettings qry trg (==) (==)
-- :let qs = getQueryVertices stt
-- :let ts = getTargetVertices stt
-- :let m1 = case prematch {s = stt} of MkPrematched m => m
-- :let co1 = getCodomain (MkVq 1) map1
-- :let ei = electiveInst co1
-- :let m2 = setInst (MkVq 0) (MkVt 2) m1
-- :let m3 = domainReduction (MkVt 2) [MkVq 2, MkVq 1] m2
-- :let m4 = domainReduction (MkVt 3) [MkVq 2, MkVq 1] m3
-- isIsomorphism m2
-- isIsomorphism m3
-- isIsomorphism m4
-- ullmannImp stt


