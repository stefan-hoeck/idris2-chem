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
 -- TODO: might need show instance?


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
    Split c g' => v :: dfs ((keys $ neighbours c) ++ vs) g'
    Empty      => dfs vs g


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
    Split c g' => v :: bfs (vs ++ (keys $ neighbours c)) g'
    Empty => bfs vs g


-- Spanning Trees --------------------------------------------------------------

df : List Node -> Graph e n -> (List (MWTree Node), Graph e n)
df []        g = ([],g)
df (v :: vs) g = if isEmpty g then ([],empty) else 
    case match v g of
      Split c g' => ?tras-- (Br v (f :: f'), g2)
      Empty      => df vs g
 --       where
 --dfhelp : Node -> Context e n -> Graph e n -> (MWTree Node, Graph e n)
 --dfhelp v c g = 
 --           let (f, g1) = df (keys $ neighbours c) g
 --               (f',g2) = df vs g1
 --           in  (Br v (f :: f') ,g2)


||| Depth first spanning forest
dff : List Node -> Graph e n -> List (MWTree Node)
dff vs g = fst (df vs g)



-- Root Path Tree --------------------------------------------------------------

-- TODO: Not checked correct result
-- breadth first algorithm for constructing the root-path tree
bf : List Path -> Graph e n -> RTree
bf []                _  = []
bf (p@(v :: _) :: ps) g = if isEmpty g then [] else
  case match v g of
    Split c g' => p :: bf (ps ++ map (\x => x :: p) (keys $ neighbours c)) g'
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

-- Minimum spanning tree -------------------------------------------------------

||| Minimal spanning tree
||| TODO: They did not do this for an unlabeled graph
|||       Not sure if this makes sense
mst : Node -> Graph e n -> RTree


-- 5. Node sets ----------------------------------------------------------------

||| Finding the largest independent node sets
indep : Graph e n -> List Node


||| Maximum clique problem but for undirected graphs
||| Groups all subgraphs Nodes
||| TODO: Does this make sense?
dep : Graph e n -> List (List Node)

