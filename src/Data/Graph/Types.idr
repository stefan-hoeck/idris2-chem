||| A representation for sparse, simple, undirected
||| labeled graphs.
|||
||| This module provides only the data types plus
||| interface implementations.
module Data.Graph.Types

import Data.IntMap
import Data.So
import Generics.Derive

%default total
%language ElabReflection

--------------------------------------------------------------------------------
--          Nodes and Edges
--------------------------------------------------------------------------------

||| A node in an undirected graph.
public export
Node : Type
Node = Bits32

||| An edge in a simple, undirected graph.
||| Since edges go in both directions and loops are not allowed,
||| we can enforce without loss of generality
||| that `n2 > n1 = True`.
public export
record Edge where
  constructor MkEdge
  node1 : Node
  node2 : Node
  0 prf : So (node2 > node1)

public export
Eq Edge where
  (==) = (==) `on` (\e => (e.node1, e.node2))

public export
Ord Edge where
  compare = compare `on` (\e => (e.node1, e.node2))


export
Show Edge where
  showPrec p (MkEdge n1 n2 _) =
    showCon p "MkEdge" $ showArg n1 ++ showArg n2 ++ " Oh"

--------------------------------------------------------------------------------
--          Labeled Nodes and Edges
--------------------------------------------------------------------------------

||| A labeled node in a graph.
public export
record LNode n where
  constructor MkLNode
  node  : Node
  label : n

%runElab derive "LNode" [Generic,Meta,Eq,Ord,Show]

public export %inline
Functor LNode where
  map f = record { label $= f }

public export %inline
Foldable LNode where
  foldl f a n  = f a n.label
  foldr f a n  = f n.label a
  foldMap  f n = f n.label
  null _       = False
  toList n     = [n.label]
  foldlM f a n = f a n.label

public export %inline
Traversable LNode where
  traverse f (MkLNode n l) = MkLNode n <$> f l

||| A labeled edge in an undirected graph
public export
record LEdge e where
  constructor MkLEdge
  edge  : Edge
  label : e

%runElab derive "LEdge" [Generic,Meta,Eq,Ord,Show]

public export %inline
Functor LEdge where
  map f = record { label $= f }

public export %inline
Foldable LEdge where
  foldl f a n  = f a n.label
  foldr f a n  = f n.label a
  foldMap  f n = f n.label
  null _       = False
  toList n     = [n.label]
  foldlM f a n = f a n.label

public export %inline
Traversable LEdge where
  traverse f (MkLEdge n l) = MkLEdge n <$> f l

--------------------------------------------------------------------------------
--          Context
--------------------------------------------------------------------------------

||| Adjacency info of a `Node` in a labeled graph.
|||
||| This consists of the node's label plus
||| a list of all its neighboring nodes and
||| the labels of the edges connecting them.
|||
||| This is what is stored in underlying `IntMap`
||| representing the graph.
public export
record Adj e n where
  constructor MkAdj
  label      : n
  neighbours : List (Node, e)

public export
Functor (Adj e) where
  map f = record { label $= f }

public export
Foldable (Adj e) where
  foldl f a n  = f a n.label
  foldr f a n  = f n.label a
  foldMap  f n = f n.label
  null _       = False
  toList n     = [n.label]
  foldlM f a n = f a n.label

public export %inline
Traversable (Adj e) where
  traverse f (MkAdj n l) = (`MkAdj` l) <$> f n

public export
Bifunctor Adj where
  bimap  f g (MkAdj l es) = MkAdj (g l) (map f <$> es)
  mapFst f (MkAdj l es)   = MkAdj l (map f <$> es)
  mapSnd g (MkAdj l es)   = MkAdj (g l) es

public export
Bifoldable Adj where
  bifoldr f g acc (MkAdj l es) =
    foldr (\(_,e) => f e) (g l acc) es
  bifoldl f g acc (MkAdj l es) =
    g (foldl (\a,(_,e) => f a e) acc es) l
  binull _ = False

public export
Bitraversable Adj where
  bitraverse f g (MkAdj l es) =
    [| MkAdj (g l) (traverse (\(n,e) => (n,) <$> f e) es) |]


||| The Context of a `Node` in a labeled graph
||| including the `Node` itself, its label, plus
||| its direct neighbors together with the
||| labels of the edges leading to them.
public export
record Context e n where
  constructor MkContext
  node       : Node
  label      : n
  neighbours : List (Node, e)

public export
Functor (Context e) where
  map f = record { label $= f }

public export
Foldable (Context e) where
  foldl f a n  = f a n.label
  foldr f a n  = f n.label a
  foldMap  f n = f n.label
  null _       = False
  toList n     = [n.label]
  foldlM f a n = f a n.label

public export %inline
Traversable (Context e) where
  traverse f (MkContext n l es) =
    (\l2 => MkContext n l2 es) <$> f l

public export
Bifunctor Context where
  bimap  f g (MkContext n l es) = MkContext n (g l) (map f <$> es)
  mapFst f (MkContext n l es)   = MkContext n l (map f <$> es)
  mapSnd g (MkContext n l es)   = MkContext n (g l) es

public export
Bifoldable Context where
  bifoldr f g acc (MkContext _ l es) =
    foldr (\(_,e) => f e) (g l acc) es
  bifoldl f g acc (MkContext _ l es) =
    g (foldl (\a,(_,e) => f a e) acc es) l
  binull _ = False

public export
Bitraversable Context where
  bitraverse f g (MkContext n l es) =
    [| MkContext (pure n) (g l) (traverse (\(n,e) => (n,) <$> f e) es) |]

--------------------------------------------------------------------------------
--          Graph
--------------------------------------------------------------------------------

||| Internal representation of labeled graphs.
public export
GraphRep : (e : Type) -> (n : Type) -> Type
GraphRep e n = IntMap (Adj e n)

public export
record Graph e n where
  constructor MkGraph
  graph : GraphRep e n

public export
Functor (Graph e) where
  map f = record { graph $= map (map f) }

public export
Foldable (Graph e) where
  foldl f a  = foldl (\a',adj => f a' adj.label) a . graph
  foldr f a  = foldr (f . label) a . graph
  foldMap  f = foldMap (f . label) . graph
  toList     = map label . toList . graph
  null g     = isEmpty $ graph g

public export %inline
Traversable (Graph e) where
  traverse f (MkGraph g) = MkGraph <$> traverse (traverse f) g

public export
Bifunctor Graph where
  bimap  f g (MkGraph m) = MkGraph $ bimap f g <$> m
  mapFst f (MkGraph m)   = MkGraph $ mapFst f <$> m
  mapSnd g (MkGraph m)   = MkGraph $ mapSnd g <$> m

public export
Bifoldable Graph where
  bifoldr f g acc =
    foldr (flip $ bifoldr f g) acc . graph
  bifoldl f g acc =
    foldl (bifoldl f g) acc . graph
  binull = null

public export
Bitraversable Graph where
  bitraverse f g (MkGraph m) =
    [| MkGraph (traverse (bitraverse f g) m) |]

--------------------------------------------------------------------------------
--          Decomposition
--------------------------------------------------------------------------------

public export
data Decomp : (e : Type) -> (n : Type) -> Type where
  Split : (ctxt : Context e n) -> (gr : Graph e n) -> Decomp e n
  Empty : Decomp e n
