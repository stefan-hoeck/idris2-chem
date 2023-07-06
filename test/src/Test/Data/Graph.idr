module Test.Data.Graph

import Chem
import Data.List
import Data.Refined.Bits32
import Data.Vect
import Hedgehog

--------------------------------------------------------------------------------
--          Generators
--------------------------------------------------------------------------------

export
edge : {k : _} -> Gen e -> Gen (Edge (S $ S k) e)
edge lbl =
  let gnode = fin {n = S (S k)} (constant FZ last)
   in [| toEdge gnode gnode lbl |]
  where
    toEdge : Fin (S $ S k) -> Fin (S $ S k) -> e -> Edge (S $ S k) e
    toEdge k j l = fromMaybe (E 0 1 l) (mkEdge k j l)

export
edges :
     {k : _}
  -> (nrEdges    : Hedgehog.Range Nat)
  -> (label      : Gen e)
  -> Gen (List $ Edge k e)
edges {k = S (S m)} nr lbl = list nr (edge lbl)
edges               _  _   = pure []

export
lgraph :
     (nrNodes   : Hedgehog.Range Nat)
  -> (nrEdges   : Hedgehog.Range Nat)
  -> (edgeLabel : Gen e)
  -> (nodeLabel : Gen n)
  -> Gen (Graph e n)
lgraph nrn nre el nl = do
  ns <- list nrn nl
  es <- edges nre el
  pure $ (G (length ns) $ mkGraphL ns es)
