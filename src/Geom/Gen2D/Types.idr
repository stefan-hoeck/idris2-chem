module Geom.Gen2D.Types

import public Chem
import Data.Graph.Indexed.Query.Visited
import Data.Graph.Indexed.Subgraph
import Data.Queue
import Data.SortedMap
import Derive.Prelude

%default total
%language ElabReflection

--------------------------------------------------------------------------------
--      Settings
--------------------------------------------------------------------------------

||| Checks if a number is in the range [0,1[
public export
ValidSensitivity : Double -> Bool
ValidSensitivity x = 0.0 <= x && x < 1.0

||| Overlap sensitivity for limiting optimization iterations
public export
record Sensitivity where
  constructor OSS
  value : Double
  {auto 0 prf : Holds ValidSensitivity value}

%runElab derive "Sensitivity" [Show,Eq]

export
Cast Sensitivity Double where
  cast oss = oss.value

||| General options for drawing and placing smiles molecules
public export
record Gen2DSettings where
  constructor S2D
  bondLength       : Double
  sensivity        : Sensitivity
  maxResolveCycles : Nat

%runElab derive "Gen2DSettings" [Show,Eq]

--------------------------------------------------------------------------------
--      Overlapping score
--------------------------------------------------------------------------------

public export
0 ScoreMap : Nat -> Type
ScoreMap n = SortedMap (Fin n) Double

||| Record for the overlapping score
public export
record OScore k where
  constructor OS
  ||| Overlapping score for the whole drawn molecule
  tot     : Double

  ||| Map of atoms with an overlapping score
  scoreA  : ScoreMap k

  ||| List of overlapping scores between two atoms
  scoreAA : List (Fin k, Fin k, Double)

%runElab deriveIndexed "OScore" [Show,Eq]

--------------------------------------------------------------------------------
--      Components
--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

-- A mapping from a node to the ring it belongs to (if any).
0 RingMap : Nat -> Type -> Type -> Type
RingMap k e n = IArray k (Maybe $ Component k e n)

%inline
subnodes : Subgraph k e n -> List (Fin k)
subnodes (G _ g) = fst <$> labels g

notVisited : Visited k -> Fin k -> Bool
notVisited vis n = not $ n `visited` vis

children : IGraph k e n -> Visited k -> Component k e n -> List (Fin k, Fin k)
children g vis c = do
  a <- nodes c
  n <- filter (notVisited vis) (neighbours g a)
  pure (a,n)

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
    r::rs =>
      Just (C None (subnodes r) True r, fromPairs k Nothing (rs >>= pairs))

parameters {k : Nat}
           (g : IGraph k e n)
           (m : RingMap k e n)

  -- `True` if the given node is not in a ring and has not yet been visited
  nonVisitedInChain : Visited k -> Fin k -> Bool
  nonVisitedInChain vis n =
    case m `at` n of
      Nothing => not (n `visited` vis)
      Just _  => False

  -- runner for `longestChainFrom`
  lcf :
       SnocList (Fin k)
    -> Queue (SnocList $ Fin k, Fin k)
    -> Visited k
    -> SnocList (Fin k)
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
  %inline
  longestChainFrom : Visited k -> Fin k -> SnocList (Fin k)
  longestChainFrom vis x = lcf [<] (enqueue empty ([<], x)) (visit x vis)

  -- Iteratively computes the longest chains from the attachment
  -- points of already found components
  chains :
       SnocList (Component k e n)
    -> Queue (Fin k,Fin k)
    -> Visited k
    -> (List $ Component k e n)
  chains sx q vis =
    case dequeue q of
      Nothing     => sx <>> []
      Just ((a,n),q2) => case m `at` n of
        Just c  =>
         let vis2 := assert_smaller vis $ visitAll (nodes c) vis
             q3   := enqueueAll q2 (children g vis2 c)
          in chains (sx:<{attach := Attach a n} c) q3 vis2
        Nothing =>
         let c    := C (Attach a n) (longestChainFrom vis n <>> []) False ()
             vis2 := assert_smaller vis $ visitAll (nodes c) vis
             q3   := enqueueAll q2 (children g vis2 c)
          in chains (sx:<c) q3 vis2

||| Partitions the nodes of a graph into disjoint components,
||| which will be placed in the given order.
export
components : {k : _} -> IGraph k e n -> List (Component k e n)
components g =
  case tryNatToFin 0 of
    Nothing => []
    Just z  => case rings g of
      Just (c,m) =>
       let vis := visitAll (nodes c) ini
        in chains g m [<c] (fromList $ children g vis c) vis
      Nothing     =>
       let m      := fill k Nothing
           _ :< n := longestChainFrom g m ini z | [<] => []
           ns     := reverse $ longestChainFrom g m ini n <>> []
           c      := C None ns False ()
           vis    := visitAll ns ini
        in chains g m [<c] (fromList $ children g vis c) vis
