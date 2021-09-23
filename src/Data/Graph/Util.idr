||| Core and utility functionality for graphs
module Data.Graph.Util

import Data.IntMap
import Data.Maybe
import Data.List
import Data.So
import Data.Graph.Types

%default total

--------------------------------------------------------------------------------
--          Internal utilities
--------------------------------------------------------------------------------

delNeighbour : Node -> Adj e n -> Adj e n
delNeighbour n = record { neighbours $= delete n }

delEdgeTo : Node -> GraphRep e n -> (Node,e) -> GraphRep e n
delEdgeTo n m (n2,_) = update n2 (delNeighbour n) m

delNeighbours : Node -> GraphRep e n -> IntMap e -> GraphRep e n
delNeighbours n g = foldl (delEdgeTo n) g . pairs

addEdge : Node -> e -> Adj e n -> Adj e n
addEdge k lbl (MkAdj l ns) = MkAdj l $ insert k lbl ns

addEdgeTo : Node -> GraphRep e n -> (Node,e) -> GraphRep e n
addEdgeTo k m (n2,lbl) = update n2 (addEdge k lbl) m

addEdgesTo : Node -> GraphRep e n -> IntMap e -> GraphRep e n
addEdgesTo n g = foldl (addEdgeTo n) g . pairs

toContext : (Node,Adj e n) -> Context e n
toContext (k,MkAdj l es) = MkContext k l es

toLNode : (Node,Adj e n) -> LNode n
toLNode (k,MkAdj l _) = MkLNode k l

-- we return only edges to nodes greater than the node in the
-- context to avoid returning every edge twice in `labEdges`.
ctxtEdges : Context e n -> List (LEdge e)
ctxtEdges (MkContext k _ ns) = go Nil (pairs ns)
  where go : List (LEdge e) -> List (Node,e) -> List (LEdge e)
        go es Nil            = es
        go es ((j,lbl) :: t) = case choose (j > k) of
          Left oh => go (MkLEdge (MkEdge k j oh) lbl :: es) t
          _       => go es t

--------------------------------------------------------------------------------
--          Decomposing Graphs
--------------------------------------------------------------------------------

||| Decompose a `Graph` into the `Context` found
||| for the given node and the remaining `Graph`.
|||
||| All edges leading to `node` will be removed from the
||| resulting `Graph`.
export
match : (node : Node) -> Graph e n -> Decomp e n
match node (MkGraph g) = case lookup node g of
  Nothing              => Empty
  Just (MkAdj lbl ns)  =>
    let g1   = MkGraph $ delNeighbours node (delete node g) ns
        ctxt = MkContext node lbl ns
     in Split ctxt g1

||| Decompose a graph into the `Context` for the largest `Node`
||| and the remaining `Graph`.
export
matchAny : Graph e n -> Decomp e n
matchAny (MkGraph g) = case decomp g of
  Done                   => Empty
  Dec k (MkAdj lbl ns) m =>
    Split (MkContext k lbl ns) (MkGraph $ delNeighbours k m ns)

--------------------------------------------------------------------------------
--          Inspecting Graphs
--------------------------------------------------------------------------------

||| True, if the given graph is empty
export
isEmpty : Graph e n -> Bool
isEmpty = isEmpty . graph

||| A list of contexts of a graph
export
contexts : Graph e n -> List (Context e n)
contexts = map toContext . pairs . graph

||| A list of all labeled nodes of a `Graph`
export
labNodes  : Graph e n -> List (LNode n)
labNodes = map toLNode . pairs . graph

||| Find the label for a `Node`.
export
lab : Graph e n -> Node -> Maybe n
lab (MkGraph m) v = label <$> lookup v m

||| Find the label for an `Edge`.
export
elab : Graph e n -> Node -> Node -> Maybe e
elab (MkGraph g) k j = lookup k g >>= lookup j . neighbours

||| List all 'Node's in the 'Graph'.
export
nodes : Graph e n -> List Node
nodes = map fst . pairs . graph

||| `True` if the `Node` is present in the `Graph`.
export
gelem : Node -> Graph e n -> Bool
gelem v = isJust . lookup v . graph

||| The number of `Node`s in a `Graph`.
export
order : Graph e n -> Nat
order = length . labNodes

||| A list of all `LEdge`s in the `Graph` (in lexicographic order).
export
labEdges  : Graph e n -> List (LEdge e)
labEdges = foldl (\es,c => ctxtEdges c ++ es) Nil . contexts

||| List all 'Edge's in the 'Graph'.
export
edges : Graph e n -> List Edge
edges = map edge . labEdges

||| The number of edges in the graph.
export
size : Graph e n -> Nat
size = length . labEdges

||| Find the labelled links to a `Node`.
export
lneighbours : Graph e n -> Node -> List (Node, e)
lneighbours (MkGraph g) k = maybe Nil (pairs . neighbours) $ lookup k g

||| Find the neighbours for a 'Node'.
export
neighbours : Graph e n -> Node -> List Node
neighbours g = map fst . lneighbours g

||| The degree of the `Node`.
export
deg : Graph e n -> Node -> Nat
deg g = length . lneighbours g

||| Checks if there is an undirected edge between two nodes.
export
hasNeighbour : Graph e n -> Node -> Node -> Bool
hasNeighbour g k = isJust . elab g k

||| Checks if there is an edge between two nodes.
export
hasEdge : Graph e n -> Edge -> Bool
hasEdge g (MkEdge k j _) = hasNeighbour g k j

||| Checks if there is a labelled edge between two nodes.
export
hasLEdge : Eq e => Graph e n -> LEdge e -> Bool
hasLEdge g (MkLEdge (MkEdge k j _) le) = maybe False (le ==) $ elab g k j

--------------------------------------------------------------------------------
--          Modifying Graphs
--------------------------------------------------------------------------------

||| Merge the `Context` into the `DynGraph`.
|||
||| Context adjacencies should only refer to either a Node already
||| in a graph.
|||
||| Behaviour is undefined if the specified 'Node' already exists
||| in the graph.
export
add : Context e n -> Graph e n -> Graph e n
add (MkContext k lbl ns) (MkGraph m) =
  let m1 = insert k (MkAdj lbl ns) m
   in MkGraph $ addEdgesTo k m1 ns

||| Fold a function over the graph by recursively calling 'match'.
export
ufold : (Context e n -> c -> c) -> c -> Graph e n -> c
ufold f acc g = case matchAny g of
  Split ctxt gr => f ctxt (ufold f acc $ assert_smaller g gr)
  Empty         => acc

||| Map a function over the graph by recursively calling `match`.
export
gmap : (Context e1 n1 -> Context e2 n2) -> Graph e1 n1 -> Graph e2 n2
gmap f = ufold (\c => add (f c)) (MkGraph empty)

||| Insert a labeled node into the `Graph`.
||| The behavior is undefined if the node is already
||| in the graph.
export
insNode : Node -> (lbl : n) -> Graph e n -> Graph e n
insNode v l (MkGraph m) = MkGraph $ insert v (MkAdj l empty) m

||| Insert a `LEdge` into the 'Graph'.
||| Behavior is undefined if the edge does not
||| connect two nodes already in the graph.
export
insEdge : LEdge e -> Graph e n -> Graph e n
insEdge (MkLEdge (MkEdge n1 n2 _) lbl) (MkGraph g) =
  let g1 = update n1 (addEdge n2 lbl) g
   in MkGraph $ update n2 (addEdge n1 lbl) g1

||| Insert multiple `LNode`s into the `Graph`.
export
insNodes : List (LNode n) -> Graph e n -> Graph e n
insNodes vs g = foldl (\g2,(MkLNode k l) => insNode k l g2) g vs

||| Insert multiple `LEdge`s into the `Graph`.
export
insEdges : List (LEdge e) -> Graph e n -> Graph e n
insEdges es g = foldl (flip insEdge) g es

||| Remove a 'Node' from the 'Graph'.
export
delNode : Node -> Graph e n -> Graph e n
delNode v g = case match v g of
  Split _ gr => gr
  Empty      => g

||| Remove multiple 'Node's from the 'Graph'.
export
delNodes : List Node -> Graph e n -> Graph e n
delNodes vs g = foldl (flip delNode) g vs

||| Remove an 'Edge' from the 'Graph'.
export
delEdge : Edge -> Graph e n -> Graph e n
delEdge (MkEdge i j _) g = case match i g of
  Split (MkContext n l ns) gr => add (MkContext n l (delete j ns)) gr
  Empty                       => g

||| Remove multiple 'Edge's from the 'Graph'.
export
delEdges : List Edge -> Graph e n -> Graph e n
delEdges es g = foldl (flip delEdge) g es

||| Returns the subgraph only containing the labelled nodes which
||| satisfy the given predicate.
export
labnfilter : (LNode n -> Bool) -> Graph e n -> Graph e n
labnfilter p gr = delNodes (map node . filter (not . p) $ labNodes gr) gr

||| Returns the subgraph only containing the nodes which satisfy the
||| given predicate.
export
nfilter : (Node -> Bool) -> Graph e n -> Graph e n
nfilter f = labnfilter (f . node)

||| Returns the subgraph only containing the nodes whose labels
||| satisfy the given predicate.
export
labfilter : (n -> Bool) -> Graph e n -> Graph e n
labfilter f = labnfilter (f . label)

--------------------------------------------------------------------------------
--          Creating Graphs
--------------------------------------------------------------------------------

||| An empty `Graph`
export
empty : Graph e n
empty = MkGraph empty

||| Create a `Graph` from the list of labeled nodes and
||| edges.
|||
||| TODO: Can we easily enforce that the edges only point
|||       To the nodes in the list?
export
mkGraph : List (LNode n) -> List (LEdge e) -> Graph e n
mkGraph ns es = insEdges es (insNodes ns empty)

-- ||| Returns the subgraph induced by the supplied nodes.
-- export
-- subgraph : List Node -> Graph e n -> Graph e n
-- subgraph vs = let vs' = IntSet.fromList vs
--                in nfilter (`IntSet.member` vs')

--------------------------------------------------------------------------------
--          Displaying Graphs
--------------------------------------------------------------------------------

export
Show e => Show n => Show (Graph e n) where
  showPrec p g =
    showCon p "mkGraph" $
    showArg (labNodes g) ++ showArg (labEdges g)
