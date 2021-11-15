||| Implementations according to
|||
||| Inductive Graphs and Functional Graph Algorithms
||| Martn Erwig
|||
||| Structure:
|||
||| 0. General: Postorder
|||
||| 1. Nodes in order visited
||| 1.1 Depth-first search
||| 1.2 Breadth-first search
||| 
||| 2. Spanning trees / spanning forest
||| 2.1 Depth-first spanning tree
||| 2.2 Breadth-first spanning tree
||| 2.3 Minimal spanning tree
|||
||| 3. Shortest Path
|||
||| 4. Independent node sets
|||
||| For both, unlabeled & labeled (Parts A & B)
|||
module Data.Graph.GraphAlgorithms

import Data.Bifoldable
import Data.IntMap
import Data.Graph.Types
import Data.Graph.Util


-- TODO: Disabled as discussed for the time being
-- %default total


-- General ---------------------------------------------------------------------

-- Multi-way tree
data MWTree a = Br a (List (MWTree a))

||| Postorder traversal
||| Visits the nodes of all subtrees before the root
export
postorder : MWTree a -> List a
postorder (Br v ts) = concatMap postorder ts ++ [v]


-- A. Unlabeled Graphs ---------------------------------------------------------

||| Representation of a list of nodes
||| unlabeled
Path : Type
Path = List Node

||| Root Path tree
||| Unlabeled
RTree : Type
RTree = List Path

-- 1.1 dfs
||| Depth First search
|||
||| Requires a list of all nodes of the graph
||| to make sure that all nodes are visited.
|||
||| Output:
||| List of nodes in depth first order
export
dfs : List Node -> Graph e n -> List Node
dfs []        _ = []
dfs (v :: vs) g = if isEmpty g then [] else
  case match v g of
    Split c g' => v :: dfs (?trd c ++ vs) g'
    Empty => dfs vs g


-- 1.2 bfs
||| Breadth First Search
|||
||| Output:
||| List of nodes in breadth first order
export
bfs : List Node -> Graph e n -> List Node
bfs []        _ = []
bfs (v :: vs) g = if isEmpty g then [] else
  case match v g of
    Split c g' => v :: bfs (vs ++ ?trb c) g'
    Empty => bfs vs g


-- Spanning Trees --------------------------------------------------------------

-- TODO: Function implementation



-- Root Path Tree --------------------------------------------------------------


-- breadth first algorithm for constructing the root-path tree
bf : List Path -> Graph e n -> RTree
bf []                _  = []
bf (p@(v :: _) :: ps) g = if isEmpty g then [] else
  case match v g of
    Split c g' => p :: bf (ps ++ map ?df ?fg) g'
    Empty      => bf ps g
bf (p :: ps)          g = bf ps g


||| Breadth first algorithm
||| Output
||| Root-path tree (list of lists actually)
export
bft : Node -> Graph e n -> RTree
bft v = bf [[v]] 

-- 3. esp
||| Shortest Path
export
esp : Node -> Node -> Graph e n -> Path
--esp s t = firt (\(v::_) => v == t) . bft s
--  where firt : (a -> Bool) -> List a -> a
--        firt p = head . ?ilter p


-- Minimum spanning tree -------------------------------------------------------

||| Minimal spanning tree
||| TODO: They did not do this for an unlabeled graph
mst : Node -> Graph e n -> RTree


-- 5. Node sets ----------------------------------------------------------------

||| Finding the largest independent node sets
indep : Graph e n -> List Node


||| Maximum clique problem but for undirected graphs
||| TODO: Does this make sense?
dep : Graph e n -> List (List Node)



-- Labeled Graphs --------------------------------------------------------------

||| Representation of a list of nodes
||| unlabeled
LPath : Type -> Type
LPath a = List (LNode a)

||| Root Path tree
||| Unlabeled
LRTree : Type -> Type
LRTree a = List (LPath a)
-- TODO: Instances missing for heap ordering

getPath : Node -> LRTree a -> Path


-- Search ----------------------------------------------------------------------
-- 1.1 dfs 
||| Depth First search
|||
||| Requires a list of all nodes of the graph
||| to make sure that all nodes are visited.
|||
||| Output:
||| List of nodes in depth first order
export
dfsL : List (LNode a) -> Graph e n -> List (LNode a)
dfsL []        _ = []
dfsL (v :: vs) g = if isEmpty g then [] else
  case match ?dv g of
    Split c g' => v :: dfsL (?trdL c ++ vs) g'
    Empty => dfsL vs g


-- 1.2 bfs
||| Breadth First Search
|||
||| Output:
||| List of nodes in breadth first order
export
bfsL : List (LNode a) -> Graph e n -> List (LNode a)
bfsL []        _ = []
bfsL (v :: vs) g = if isEmpty g then [] else
  case match ?bv g of
    Split c g' => v :: bfsL (vs ++ ?trbL c) g'
    Empty => bfsL vs g

-- Spanning Trees --------------------------------------------------------------

-- Minimum spanning tree 


||| Minimal spanning tree
||| TODO: They did not do this for an unlabeled graph
mstL : LNode a -> Graph e n -> LRTree a

-- Shortest Path ---------------------------------------------------------------

-- 3. esp
||| Shortest Path
export
espL : LNode a -> LNode a -> Graph e n -> LPath a


-- Node sets -------------------------------------------------------------------

||| Finding the largest independent node sets
indepL : Graph e n -> List (LNode a)


||| Maximum clique problem but for undirected graphs
||| This function would group all nodes
||| which are connected to each other
||| List of subgraphs
||| TODO: Does this make sense?
depL : Graph e n -> List (List (LNode a))
