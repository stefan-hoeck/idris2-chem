module Chem.Rings.Relevant

import Data.Graph.Indexed
import Data.Graph.Indexed.Subgraph
import Data.Graph.Indexed.Query.Util
import Data.Graph.Indexed.Query.Visited
import Data.List
import Data.Queue
import Data.SnocList
import Debug.Trace
import Derive.Prelude

import Syntax.T1

%default total
%language ElabReflection

||| A shortest path of length `length` from a starting node to node `last`.
||| Boolean `keep` indicates if all nodes are strictly smaller than
||| the starting node (according to an ordering `<`, where x < y means that
||| deg x <= deg y; this is the ordering `pi` given in the paper).
|||
||| Node `first` is the first node after the root node, and is used to
||| check if two paths are disjoint.
public export
record Path (k : Nat) where
  constructor P
  length : Nat
  keep   : Bool
  path   : SnocList (Fin k)
  first  : Fin k
  last   : Fin k

%runElab deriveIndexed "Path" [Show,Eq]

public export
0 Cycle : Nat -> Type
Cycle k = List (Fin k)

revOnto : SnocList a -> SnocList a -> SnocList a 
revOnto sx [<] = sx
revOnto sx (sy:<y) = revOnto (sx :< y) sy

toCycle : a -> SnocList a -> SnocList a -> List a
toCycle r sx sy = r :: (revOnto sx sy <>> [r])

parameters {o    : Nat}
           (g    : ISubgraph o k e n)
           (root : Fin o)
           (rdeg : Nat)

  %inline smaller : Fin o -> Bool
  smaller n =
    case compare (deg g n) rdeg of
      LT => True
      EQ => root < n
      GT => False

  init : Fin o -> Path o
  init n = P 1 (smaller n) [<n] n n

  append : Path o -> Fin o -> Path o
  append (P l kp p fs ls) n = P (S l) (kp && smaller n) (p :< n) fs n

  covering
  shortestL : SnocList (Path o) -> Queue (Path o) -> MVis o (List (Path o))
  shortestL sp q r t =
    case dequeue q of
      Nothing => (sp <>> []) # t
      Just (p,q2) =>
        let False # t := mvisited r p.last t | True # t => shortestL sp q2 r t
            ns        := map (append p) (neighbours g p.last)
            sp2       := if p.keep then sp :< p else sp
            _ #     t := mvisit r p.last t
         in shortestL sp2 (enqueueAll q2 ns) r t

  ||| Computes the shortest paths to all nodes reachable from
  ||| the given starting node. This is a simplified version of
  ||| Dijkstra's algorithm for unweighted edges.
  |||
  ||| Runs in O(n+m) time and O(n) memory.
  export
  shortestPaths : List (Path o)
  shortestPaths =
    let q := fromList $ map init (neighbours g root)
     in assert_total $ visiting o $ \r => T1.do
          mvisit r root
          shortestL [<] q r

  -- Takes a list of reverse paths starting all from the same node and
  -- sorted by length (this is by construction: the `shortestPaths` algorithm
  -- will produce shorter paths earlier than longer paths). It will pair every
  -- path with all successors of equal length (resulting in odd cycles) and
  -- one node longer (resulting in even cycles) and connect the pair if it
  -- builds a proper, disjoint cycle.
  cycleSystem : List (Cycle k)
  cycleSystem = go [<] shortestPaths
    where
      %inline cycle : (p1,p2 : SnocList (Fin o)) -> Cycle k
      cycle p1 p2 = fst . lab g <$> toCycle root p1 p2
  
      addCs : SnocList (Cycle k) -> Path o -> List (Path o) -> SnocList (Cycle k)
      addCs sc p [] = sc
      addCs sc p@(P len1 _ p1 f1 l1) (P len2 _ p2 f2 l2::qs) =
        let True  := len1 == len2     | False => sc
            False := f1 == f2         | True  => addCs sc p qs
            False := adjacent g l1 l2 | True  => addCs (sc :< cycle p1 p2) p qs
            ns    := keys $ intersect (neighboursAsAL g l1) (neighboursAsAL g l2)
         in addCs (sc <>< map (cycle p1 . (p2 :<)) (filter smaller ns)) p qs
    
      -- for the current path, we take from the remaining paths those
      -- that are at most one node longer and try to pair them to
      -- form a cycle.
      go : SnocList (Cycle k) -> List (Path o) -> List (Cycle k)
      go sxs []        = sxs <>> []
      go sxs (p :: ps) = go (addCs sxs p ps) ps

findCycles : Subgraph k e n -> List (Cycle k)
findCycles (G 0 g) = []
findCycles (G (S k) g) =
  case filter ((2 <) . deg g) (nodes g) of
    [] => [Builtin.fst . lab g <$> (nodes g ++ [FZ])] -- this is already an elementary cycle
    ns => ns >>= \n => cycleSystem g n (deg g n) -- this is a system of cycles

-- cuts a graph into strongly connected components and computes
-- the potential relevant cycles for each component in isolation.
export
computeCI' : {k : _} -> IGraph k e n -> List (Cycle k)
computeCI' g = biconnectedComponents g >>= findCycles
