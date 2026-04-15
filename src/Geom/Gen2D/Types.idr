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
0 Nodes : Nat -> Type
Nodes = List . Fin

public export
0 SnocNodes : Nat -> Type
SnocNodes = SnocList . Fin

public export
data AttachPoint : (k : Nat) -> Type where
  None   : AttachPoint k
  Attach : (parent : Fin k) -> (node : Fin k) -> AttachPoint k

%runElab deriveIndexed "AttachPoint" [Show,Eq]

public export
0 SubgraphType : Bool -> Nat -> Type -> Type -> Type
SubgraphType True  k e n = Subgraph k e n
SubgraphType False _ _ _ = ()

||| A component is a part of a molecular graph that will be placed
||| as a single unit.
|||
||| Every componenent `c` except the first (the "main component")
||| comes with an attachement point: A node in another component
||| that will be placed before `c`.
public export
record Component (k : Nat) (e,n : Type) where
  constructor C
  attach   : AttachPoint k
  nodes    : List (Fin k)
  isRing   : Bool
  subgraph : SubgraphType isRing k e n

public export
0 SnocComps : Nat -> Type -> Type -> Type
SnocComps k e = SnocList . Component k e

public export
0 Comps : Nat -> Type -> Type -> Type
Comps k e = List . Component k e

setAttach : (a,x : Fin k) -> Component k e n -> Component k e n
setAttach a x = {attach := Attach a x}

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

-- A mapping from a node to the ring it belongs to (if any).
0 RingMap : Nat -> Type -> Type -> Type
RingMap k e n = IArray k (Maybe $ Component k e n)

%inline
subnodes : Subgraph k e n -> List (Fin k)
subnodes (G _ g) = fst <$> labels g

children : IGraph k e n -> Visited k -> Component k e n -> List (Fin k, Fin k)
children g v c =
  nodes c >>= \a => (a,) <$> filter (flip unvisited v) (neighbours g a)

--------------------------------------------------------------------------------
-- Component Partition
--------------------------------------------------------------------------------

pairs : Subgraph k e n -> List (Nat, Maybe $ Component k e n)
pairs g =
 let ns := subnodes g
     c  := Just (C None ns True g)
  in map (\x => (finToNat x ,c)) ns

-- Extracts the ring systems from a graph storing them in an array and
-- returning the largest of them as the molecule's main component.
-- Returns `Nothing` in case the molecule is acyclic.
rings : {k : _} -> (g : IGraph k e n) -> Maybe (Component k e n, RingMap k e n)
rings g =
  case reverse $ sortBy (comparing order) (biconnectedComponents g) of
    []    => Nothing
    r::rs => Just (C None (subnodes r) True r, fromPairs k Nothing (rs >>= pairs))

parameters {k : Nat}
           (g : IGraph k e n)
           (m : RingMap k e n)

  -- `True` if the given node is not in a ring and has not yet been visited
  nonVisitedInChain : Visited k -> Fin k -> Bool
  nonVisitedInChain v n = isNothing (m `at` n) && unvisited n v

  -- runner for `chain`
  lcf : SnocNodes k -> Queue (SnocNodes k, Fin k) -> Visited k -> SnocNodes k
  lcf sx q vis =
    case dequeue q of
      Nothing          => sx
      Just ((sy,y),q2) =>
       let ss := sy:<y
           ns := filter (nonVisitedInChain vis) (neighbours g y)
           v2 := assert_smaller vis (visitAll ns vis)
        in lcf ss (enqueueAll q2 $ (ss,) <$> ns) v2

  -- computes the longest chain of atoms not in a ring
  -- from the given starting point
  chain : Visited k -> Fin k -> SnocList (Fin k)
  chain vis x = lcf [<] (enqueue empty ([<], x)) (visit x vis)

  nextComp : Visited k -> (a,x : Fin k) -> Component k e n
  nextComp v a x =
    maybe (C (Attach a x) (chain v x <>> []) False ()) (setAttach a x) (at m x)

  -- Iteratively computes the longest chains from the attachment
  -- points of already found components
  chains : SnocComps k e n -> Queue (Fin k,Fin k) -> Visited k -> (Comps k e n)
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
components : {k : _} -> IGraph k e n -> List (Component k e n)
components {k = Z}   g = []
components {k = S x} g =
  case rings g of
    Just (c,m) =>
     let vis := visitAll (nodes c) ini
      in chains g m [<c] (fromList $ children g vis c) vis
    Nothing     =>
     let m      := fill (S x) Nothing
         _ :< n := chain g m ini FZ | [<] => []
         ns     := reverse $ chain g m ini n <>> []
         c      := C None ns False ()
         vis    := visitAll ns ini
      in chains g m [<c] (fromList $ children g vis c) vis
