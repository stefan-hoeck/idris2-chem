module Geom.Gen2D.Types

import public Chem
import public Data.Graph.Indexed.Subgraph
import Data.Graph.Indexed.Query.Visited
import Data.Queue
import Data.SortedMap
import Derive.Prelude

%default total
%language ElabReflection

--------------------------------------------------------------------------------
--      Components
--------------------------------------------------------------------------------

public export
data AttachPoint : (g : Graph e n) -> Type where
  None   : AttachPoint g
  Attach : (parent : Node g) -> (node : Node g) -> AttachPoint g

%runElab deriveIndexed "AttachPoint" [Show,Eq]

public export
0 SubgraphType : Bool -> (g : Graph e n) -> Type
SubgraphType True  g = Subgraph g
SubgraphType False _ = ()

||| A component is a part of a molecular graph that will be placed
||| as a single unit.
|||
||| Every componenent `c` except the first (the "main component")
||| comes with an attachement point: A node in another component
||| that will be placed before `c`.
public export
record Component (g : Graph e n) where
  constructor C
  attach   : AttachPoint g
  nodes    : Nodes g
  isRing   : Bool
  subgraph : SubgraphType isRing g

public export
0 SnocComps : Graph e n -> Type
SnocComps = SnocList . Component

public export
0 Comps : Graph e n -> Type
Comps = List . Component

setAttach : (a,x : Node g) -> Component g -> Component g
setAttach a x = {attach := Attach a x}

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

-- A mapping from a node to the ring it belongs to (if any).
0 RingMap : Graph e n -> Type
RingMap g = IArray g.order (Maybe $ Component g)

children : (g : Graph e n) -> Visited g -> Component g -> List (Node g, Node g)
children g v c =
  nodes c >>= \a => (a,) <$> filter (flip unvisited v) (neighbours a)

--------------------------------------------------------------------------------
-- Component Partition
--------------------------------------------------------------------------------

pairs : Subgraph g -> List (Nat, Maybe $ Component g)
pairs g =
 let ns := labels g
     c  := Just (C None ns True g)
  in map (\x => (cast x ,c)) ns

-- Extracts the ring systems from a graph storing them in an array and
-- returning the largest of them as the molecule's main component.
-- Returns `Nothing` in case the molecule is acyclic.
rings : (g : Graph e n) -> Maybe (Component g, RingMap g)
rings g =
  case reverse $ sortBy (comparing order) (biconnectedComponents g) of
    []    => Nothing
    r::rs => Just (C None (labels r) True r, fromPairs _ Nothing (rs >>= pairs))

parameters (g : Graph e n)
           (m : RingMap g)

  -- `True` if the given node is not in a ring and has not yet been visited
  nonVisitedInChain : Visited g -> Node g -> Bool
  nonVisitedInChain v n = isNothing (m `atN` n) && unvisited n v

  -- runner for `chain`
  lcf : Sedon g -> Queue (Sedon g, Node g) -> Visited g -> Sedon g
  lcf sx q vis =
    case dequeue q of
      Nothing          => sx
      Just ((sy,y),q2) =>
       let ss := sy:<y
           ns := filter (nonVisitedInChain vis) (neighbours y)
           v2 := assert_smaller vis (visitAll ns vis)
        in lcf ss (enqueueAll q2 $ (ss,) <$> ns) v2

  -- computes the longest chain of atoms not in a ring
  -- from the given starting point
  chain : Visited g -> Node g -> Sedon g
  chain vis x = lcf [<] (enqueue empty ([<], x)) (visit x vis)

  nextComp : Visited g -> (a,x : Node g) -> Component g
  nextComp v a x =
    maybe (C (Attach a x) (chain v x <>> []) False ()) (setAttach a x) (atN m x)

  -- Iteratively computes the longest chains from the attachment
  -- points of already found components
  chains : SnocComps g -> Queue (Node g, Node g) -> Visited g -> (Comps g)
  chains sx q vis =
    case dequeue q of
      Nothing         => sx <>> []
      Just ((a,n),q2) =>
       let c    := nextComp vis a n
           vis2 := assert_smaller vis $ visitAll (nodes c) vis
           q3   := enqueueAll q2 (children g vis2 c)
        in chains (sx:<c) q3 vis2

||| Partitions the nodes of a graph into disjoint components,
||| which will be placed individually in the given order.
|||
||| The first component to be placed will be the most complex
||| cyclic system (if any) or the longest chain. All other
||| components in the list are linked via an `AttachPoint` to
||| a parent component, which will be placed first.
export
components : (g : Graph e n) -> List (Component g)
components g =
  case tryNode {g} 0 of
    Nothing   => []
    Just zero => case rings g of
      Just (c,m) =>
       let vis := visitAll (nodes c) ini
        in chains g m [<c] (fromList $ children g vis c) vis
      Nothing     =>
       let m      := fill g.order Nothing
           _ :< n := chain g m ini zero | [<] => []
           ns     := reverse $ chain g m ini n <>> []
           c      := C None ns False ()
           vis    := visitAll ns ini
        in chains g m [<c] (fromList $ children g vis c) vis
