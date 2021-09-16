module Data.Graph.Types

import Data.IntMap
import Data.So
import Generics.Derive

%default total
%language ElabReflection

--------------------------------------------------------------------------------
--          Nodes and Edges
--------------------------------------------------------------------------------

||| A node in an undirected graph
public export
Node : Type
Node = Bits32

||| An edge in a simple, undirected graph.
||| Since edges go in both directions and loops are not allowed,
||| we can enforce without loss of generality that `n2 > n1 = True`.
public export
record Edge where
  constructor MkEdge
  node1 : Node
  node2 : Node
  0 prf : So (node2 > node1)

public export
Eq Edge where
  MkEdge a1 a2 _ == MkEdge b1 b2 _ = a1 == b1 && a2 == b2

public export
Ord Edge where
  compare (MkEdge a1 a2 _) (MkEdge b1 b2 _) =
    case compare a1 b1 of
      EQ => compare a2 b2
      o  => o

export
Show Edge where
  showPrec p (MkEdge n1 n2 _) =
    showCon p "MkEdge" $ showArg n1 ++ showArg n2 ++ " Oh"

||| Predicate that an `Edge` ends at the given `Node`.
public export
data EdgeTo : (n : Node) -> (e : Edge) -> Type where
  At1 : {0 prf : _} -> EdgeTo n1 (MkEdge n1 n2 prf)
  At2 : {0 prf : _} -> EdgeTo n2 (MkEdge n1 n2 prf)

--------------------------------------------------------------------------------
--          Labeled Nodes and Edges
--------------------------------------------------------------------------------

||| A labeled node in an undirected graph
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

public export
record Adj e n where
  constructor MkAdj
  label : n
  edges : List (LEdge e)

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
    foldr (\e => f e.label) (g l acc) es
  bifoldl f g acc (MkAdj l es) =
    g (foldl (\a,e => f a e.label) acc es) l
  binull _ = False

public export
Bitraversable Adj where
  bitraverse f g (MkAdj l es) =
    [| MkAdj (g l) (traverse (traverse f) es) |]

public export
record Context e n where
  constructor MkContext
  node  : Node
  label : n
  edges : List (LEdge e)

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
    foldr (\e => f e.label) (g l acc) es
  bifoldl f g acc (MkContext _ l es) =
    g (foldl (\a,e => f a e.label) acc es) l
  binull _ = False

public export
Bitraversable Context where
  bitraverse f g (MkContext n l es) =
    [| MkContext (pure n) (g l) (traverse (traverse f) es) |]

public export %inline
toContext : (Node,Adj e n) -> Context e n
toContext (k,MkAdj l es) = MkContext k l es

public export %inline
toLNode : (Node,Adj e n) -> LNode n
toLNode (k,MkAdj l _) = MkLNode k l

--------------------------------------------------------------------------------
--          Graph
--------------------------------------------------------------------------------

public export
record Graph e n where
  constructor MkGraph
  graph : IntMap (Adj e n)

--------------------------------------------------------------------------------
--          Decomposition
--------------------------------------------------------------------------------

public export
record Decomp e n where
  constructor MkDecomp
  context : Context e n
  graph   : Graph e n
