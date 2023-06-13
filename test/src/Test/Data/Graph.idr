module Test.Data.Graph

import Chem
import Data.List
import Data.Refined.Bits32
import Data.Vect
import Hedgehog

--------------------------------------------------------------------------------
--          Generators
--------------------------------------------------------------------------------

-- zips elements with their index an returns the resulting
-- list of labeled nodes plus the value of the next node
toNodes : List n -> (Node, List $ LNode n)
toNodes = go 0 Nil
  where go : Node -> List (LNode n) -> List n -> (Node, List $ LNode n)
        go i res []        = (i, reverse res)
        go i res (x :: xs) = go (i+1) (MkLNode i x :: res) xs

export
edge :
     (upperBound : Node)
  -> {auto 0 p : 1 < upperBound}
  -> (lbl : Gen e)
  -> Gen (LEdge e)
edge ub lbl =
  let gnode = bits32 (linear 0 (ub-1))
   in [| toEdge gnode gnode lbl |]
  where
    toEdge : Node -> Node -> e -> LEdge e
    toEdge k j l = MkLEdge (fromMaybe (MkEdge 0 1 %search) (mkEdge k j)) l

export
edges :
     (upperBound : Node)
  -> (nrEdges    : Hedgehog.Range Nat)
  -> (label      : Gen e)
  -> Gen (List $ LEdge e)
edges ub nr lbl = case lt 1 ub of
  Just0 _  => list nr (edge ub lbl)
  Nothing0 => pure []

export
lgraph :
     (nrNodes   : Hedgehog.Range Nat)
  -> (nrEdges   : Hedgehog.Range Nat)
  -> (edgeLabel : Gen e)
  -> (nodeLabel : Gen n)
  -> Gen (Graph e n)
lgraph nrn nre el nl = do
  (upperBound, ns) <- toNodes <$> list nrn nl
  es               <- edges upperBound nre el
  pure $ mkGraph ns es

-- a graph with characters '-', '=', or '#' as edge labels
-- and lower case characters ('a' .. 'z')
smallGraph : Gen (Graph Char Char)
smallGraph =
  let bond = element ['-', '=', '#']
   in lgraph (linear 0 10) (linear 0 25) bond lower

-- a non-empty graph with characters '-', '=', or '#' as edge labels
-- and lower case characters ('a' .. 'z')
nonEmptySmallGraph : Gen (Graph Char Char)
nonEmptySmallGraph =
  let bond = element ['-', '=', '#']
   in lgraph (linear 1 10) (linear 0 25) bond lower

--------------------------------------------------------------------------------
--          Properties
--------------------------------------------------------------------------------

gmap_id : Property
gmap_id = property $ do
  g <- forAll smallGraph
  g === gmap id g

add_matchAny : Property
add_matchAny = property $ do
  g <- forAll nonEmptySmallGraph
  case matchAny g of
    Split ctxt gr => g === add ctxt gr
    Empty         => failWith Nothing "Unexpected empty graph"

add_match : Property
add_match = property $ do
  g <- forAll nonEmptySmallGraph
  n <- forAll (bits32 $ linear 0 (cast (order g) - 1))
  case match n g of
    Split ctxt gr => g === add ctxt gr
    Empty         => failWith Nothing "Unexpected empty context"

--------------------------------------------------------------------------------
--          Group
--------------------------------------------------------------------------------

export
props : Group
props = MkGroup "Graph Properties"
  [ ("gmap_id", gmap_id)
  , ("add_matchAny", add_matchAny)
  , ("add_match", add_match)
  ]
