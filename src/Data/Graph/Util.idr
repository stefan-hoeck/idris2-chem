||| Core and utility functionality for graphs
module Data.Graph.Util

import Data.IntMap
import Data.Graph.Types

%default total

||| An empty `Graph`
public export
empty : Graph e n
empty = MkGraph empty

||| True, if the given graph is empty
public export
isEmpty : Graph e n -> Bool
isEmpty = isEmpty . graph

||| Decompose a `Graph` into the `Context` found
||| for the given node and the remaining `Graph`.
||| TODO
public export
match : Node -> Graph e n -> Maybe (Decomp e n)

||| Create a `Graph` from the list of labeled nodes and
||| edges.
|||
||| TODO: Can we easily enforce that the edges only point
|||       To the nodes in the list?
public export
mkGraph : List (LNode n) -> List (LEdge e) -> Graph e n

||| A list of contexts of a graph
public export
contexts : Graph e n -> List (Context e n)
contexts = map toContext . pairs . graph

||| A list of all labeled nodes of a `Graph`
public export
labNodes  : Graph e n -> List (LNode n)
labNodes = map toLNode . pairs . graph

--  -- | Decompose a graph into the 'Context' for an arbitrarily-chosen 'Node'
--  -- and the remaining 'Graph'.
-- TODO: We should have a proof of non-emptiness on `IntMap`
--       and hence on `Graph` and use that to totally decompose
--       a graph without the need of intermediary `Maybe`s
--  matchAny  :: gr a b -> GDecomp gr a b

||| The number of `Node`s in a `Graph`.
public export
order : Graph e n -> Nat
order = length . labNodes

||| A list of all `LEdge`s in the `Graph`.
public export
labEdges  : Graph e n -> List (LEdge e)

-- | Merge the 'Context' into the 'DynGraph'.
--
--   Context adjacencies should only refer to either a Node already
--   in a graph or the node in the Context itself (for loops).
--
--   Behaviour is undefined if the specified 'Node' already exists
--   in the graph.
-- TODO
public export
add : Context e n -> Graph e n -> Graph e n

||| The number of edges in the graph.
public export
size : Graph e n -> Nat
size = length . labEdges

||| Fold a function over the graph by recursively calling 'match'.
||| TODO
public export
ufold : (Context e n -> c -> c) -> c -> Graph e n -> c

||| Map a function over the graph by recursively calling 'match'.
public export
gmap : (Context e1 n1 -> Context e2 n2) -> Graph e1 n1 -> Graph e2 n2
gmap f = ufold (\c => add (f c)) empty

||| Map a function over the 'Node' labels in a graph.
public export
nmap : (n -> n2) -> Graph e n -> Graph e n2
nmap f (MkGraph m) = MkGraph $ map f <$> m 

||| Map a function over the `Edge` labels in a graph.
public export
emap : (e -> e2) -> Graph e n -> Graph e2 n
emap f (MkGraph m) = MkGraph $ mapFst f <$> m 

||| Map functions over both the `Node` and `Edge`
||| labels in a graph.
public export
nemap : (e1 -> e2) -> (n1 -> n2) -> Graph e1 n1 -> Graph e2 n2
nemap f g (MkGraph m) = MkGraph $ bimap f g <$> m 

||| List all 'Node's in the 'Graph'.
public export
nodes : Graph e n -> List Node
nodes = map fst . pairs . graph 

||| List all 'Edge's in the 'Graph'.
public export
edges : Graph e n -> List Edge
edges = map edge . labEdges

||| `True` if the `Node` is present in the `Graph`.
public export
gelem : Node -> Graph e n -> Bool
gelem v = isKey v . graph

-- -- | Insert a 'LNode' into the 'Graph'.
-- insNode :: (DynGraph gr) => LNode a -> gr a b -> gr a b
-- insNode (v,l) = (([],v,l,[])&)
-- {-# NOINLINE [0] insNode #-}
-- 
-- -- | Insert a 'LEdge' into the 'Graph'.
-- insEdge :: (DynGraph gr) => LEdge b -> gr a b -> gr a b
-- insEdge (v,w,l) g = (pr,v,la,(l,w):su) & g'
--   where
--     (mcxt,g') = match v g
--     (pr,_,la,su) = fromMaybe
--                      (error ("insEdge: cannot add edge from non-existent vertex " ++ show v))
--                      mcxt
-- {-# NOINLINE [0] insEdge #-}
-- 
-- -- | Remove a 'Node' from the 'Graph'.
-- delNode :: (Graph gr) => Node -> gr a b -> gr a b
-- delNode v = delNodes [v]
-- 
-- -- | Remove an 'Edge' from the 'Graph'.
-- --
-- --   NOTE: in the case of multiple edges, this will delete /all/ such
-- --   edges from the graph as there is no way to distinguish between
-- --   them.  If you need to delete only a single such edge, please use
-- --   'delLEdge'.
-- delEdge :: (DynGraph gr) => Edge -> gr a b -> gr a b
-- delEdge (v,w) g = case match v g of
--                     (Nothing,_)          -> g
--                     (Just (p,v',l,s),g') -> (p,v',l,filter ((/=w).snd) s) & g'
-- 
-- -- | Remove an 'LEdge' from the 'Graph'.
-- --
-- --   NOTE: in the case of multiple edges with the same label, this
-- --   will only delete the /first/ such edge.  To delete all such
-- --   edges, please use 'delAllLedge'.
-- delLEdge :: (DynGraph gr, Eq b) => LEdge b -> gr a b -> gr a b
-- delLEdge = delLEdgeBy delete
-- 
-- -- | Remove all edges equal to the one specified.
-- delAllLEdge :: (DynGraph gr, Eq b) => LEdge b -> gr a b -> gr a b
-- delAllLEdge = delLEdgeBy (filter . (/=))
-- 
-- delLEdgeBy :: (DynGraph gr) => ((b,Node) -> Adj b -> Adj b)
--               -> LEdge b -> gr a b -> gr a b
-- delLEdgeBy f (v,w,b) g = case match v g of
--                            (Nothing,_)          -> g
--                            (Just (p,v',l,s),g') -> (p,v',l,f (b,w) s) & g'
-- 
-- -- | Insert multiple 'LNode's into the 'Graph'.
-- insNodes   :: (DynGraph gr) => [LNode a] -> gr a b -> gr a b
-- insNodes vs g = foldl' (flip insNode) g vs
-- {-# INLINABLE insNodes #-}
-- 
-- -- | Insert multiple 'LEdge's into the 'Graph'.
-- insEdges :: (DynGraph gr) => [LEdge b] -> gr a b -> gr a b
-- insEdges es g = foldl' (flip insEdge) g es
-- {-# INLINABLE insEdges #-}
-- 
-- -- | Remove multiple 'Node's from the 'Graph'.
-- delNodes :: (Graph gr) => [Node] -> gr a b -> gr a b
-- delNodes vs g = foldl' (snd .: flip match) g vs
-- 
-- -- | Remove multiple 'Edge's from the 'Graph'.
-- delEdges :: (DynGraph gr) => [Edge] -> gr a b -> gr a b
-- delEdges es g = foldl' (flip delEdge) g es
-- 
-- -- | Build a 'Graph' from a list of 'Context's.
-- --
-- --   The list should be in the order such that earlier 'Context's
-- --   depend upon later ones (i.e. as produced by @'ufold' (:) []@).
-- buildGr :: (DynGraph gr) => [Context a b] -> gr a b
-- buildGr = foldr (&) empty
-- 
-- -- | Build a quasi-unlabeled 'Graph'.
-- mkUGraph :: (Graph gr) => [Node] -> [Edge] -> gr () ()
-- mkUGraph vs es = mkGraph (labUNodes vs) (labUEdges es)
--    where
--      labUEdges = map (`toLEdge` ())
--      labUNodes = map (flip (,) ())
-- 
-- -- | Build a graph out of the contexts for which the predicate is
-- -- satisfied by recursively calling 'match'.
-- gfiltermap :: DynGraph gr => (Context a b -> MContext c d) -> gr a b -> gr c d
-- gfiltermap f = ufold (maybe id (&) . f) empty
-- 
-- -- | Returns the subgraph only containing the labelled nodes which
-- -- satisfy the given predicate.
-- labnfilter :: Graph gr => (LNode a -> Bool) -> gr a b -> gr a b
-- labnfilter p gr = delNodes (map fst . filter (not . p) $ labNodes gr) gr
-- 
-- -- | Returns the subgraph only containing the nodes which satisfy the
-- -- given predicate.
-- nfilter :: DynGraph gr => (Node -> Bool) -> gr a b -> gr a b
-- nfilter f = labnfilter (f . fst)
-- 
-- -- | Returns the subgraph only containing the nodes whose labels
-- -- satisfy the given predicate.
-- labfilter :: DynGraph gr => (a -> Bool) -> gr a b -> gr a b
-- labfilter f = labnfilter (f . snd)
-- 
-- -- | Returns the subgraph induced by the supplied nodes.
-- subgraph :: DynGraph gr => [Node] -> gr a b -> gr a b
-- subgraph vs = let vs' = IntSet.fromList vs
--               in nfilter (`IntSet.member` vs')
-- 
-- -- | Find the context for the given 'Node'.  Causes an error if the 'Node' is
-- -- not present in the 'Graph'.
-- context :: (Graph gr) => gr a b -> Node -> Context a b
-- context g v = fromMaybe (error ("Match Exception, Node: "++show v))
--                         (fst (match v g))
-- 
-- -- | Find the label for a 'Node'.
-- lab :: (Graph gr) => gr a b -> Node -> Maybe a
-- lab g v = fmap lab' . fst $ match v g
-- 
-- -- | Find the neighbors for a 'Node'.
-- neighbors :: (Graph gr) => gr a b -> Node -> [Node]
-- neighbors = map snd .: lneighbors
-- 
-- -- | Find the labelled links coming into or going from a 'Context'.
-- lneighbors :: (Graph gr) => gr a b -> Node -> Adj b
-- lneighbors = maybe [] lneighbors' .: mcontext
-- 
-- -- | Find all 'Node's that have a link from the given 'Node'.
-- suc :: (Graph gr) => gr a b -> Node -> [Node]
-- suc = map snd .: context4l
-- 
-- -- | Find all 'Node's that link to to the given 'Node'.
-- pre :: (Graph gr) => gr a b -> Node -> [Node]
-- pre = map snd .: context1l
-- 
-- -- | Find all 'Node's that are linked from the given 'Node' and the label of
-- -- each link.
-- lsuc :: (Graph gr) => gr a b -> Node -> [(Node,b)]
-- lsuc = map flip2 .: context4l
-- 
-- -- | Find all 'Node's that link to the given 'Node' and the label of each link.
-- lpre :: (Graph gr) => gr a b -> Node -> [(Node,b)]
-- lpre = map flip2 .: context1l
-- 
-- -- | Find all outward-bound 'LEdge's for the given 'Node'.
-- out :: (Graph gr) => gr a b -> Node -> [LEdge b]
-- out g v = map (\(l,w)->(v,w,l)) (context4l g v)
-- 
-- -- | Find all inward-bound 'LEdge's for the given 'Node'.
-- inn :: (Graph gr) => gr a b -> Node -> [LEdge b]
-- inn g v = map (\(l,w)->(w,v,l)) (context1l g v)
-- 
-- -- | The outward-bound degree of the 'Node'.
-- outdeg :: (Graph gr) => gr a b -> Node -> Int
-- outdeg = length .: context4l
-- 
-- -- | The inward-bound degree of the 'Node'.
-- indeg :: (Graph gr) => gr a b -> Node -> Int
-- indeg  = length .: context1l
-- 
-- -- | The degree of the 'Node'.
-- deg :: (Graph gr) => gr a b -> Node -> Int
-- deg = deg' .: context
-- 
-- -- | The 'Node' in a 'Context'.
-- node' :: Context a b -> Node
-- node' (_,v,_,_) = v
-- 
-- -- | The label in a 'Context'.
-- lab' :: Context a b -> a
-- lab' (_,_,l,_) = l
-- 
-- -- | The 'LNode' from a 'Context'.
-- labNode' :: Context a b -> LNode a
-- labNode' (_,v,l,_) = (v,l)
-- 
-- -- | All 'Node's linked to or from in a 'Context'.
-- neighbors' :: Context a b -> [Node]
-- neighbors' (p,_,_,s) = map snd p++map snd s
-- 
-- -- | All labelled links coming into or going from a 'Context'.
-- lneighbors' :: Context a b -> Adj b
-- lneighbors' (p,_,_,s) = p ++ s
-- 
-- -- | All 'Node's linked to in a 'Context'.
-- suc' :: Context a b -> [Node]
-- suc' = map snd . context4l'
-- 
-- -- | All 'Node's linked from in a 'Context'.
-- pre' :: Context a b -> [Node]
-- pre' = map snd . context1l'
-- 
-- -- | All 'Node's linked from in a 'Context', and the label of the links.
-- lsuc' :: Context a b -> [(Node,b)]
-- lsuc' = map flip2 . context4l'
-- 
-- -- | All 'Node's linked from in a 'Context', and the label of the links.
-- lpre' :: Context a b -> [(Node,b)]
-- lpre' = map flip2 . context1l'
-- 
-- -- | All outward-directed 'LEdge's in a 'Context'.
-- out' :: Context a b -> [LEdge b]
-- out' c@(_,v,_,_) = map (\(l,w)->(v,w,l)) (context4l' c)
-- 
-- -- | All inward-directed 'LEdge's in a 'Context'.
-- inn' :: Context a b -> [LEdge b]
-- inn' c@(_,v,_,_) = map (\(l,w)->(w,v,l)) (context1l' c)
-- 
-- -- | The outward degree of a 'Context'.
-- outdeg' :: Context a b -> Int
-- outdeg' = length . context4l'
-- 
-- -- | The inward degree of a 'Context'.
-- indeg' :: Context a b -> Int
-- indeg' = length . context1l'
-- 
-- -- | The degree of a 'Context'.
-- deg' :: Context a b -> Int
-- deg' (p,_,_,s) = length p+length s
-- 
-- -- | Checks if there is a directed edge between two nodes.
-- hasEdge :: Graph gr => gr a b -> Edge -> Bool
-- hasEdge gr (v,w) = w `elem` suc gr v
-- 
-- -- | Checks if there is an undirected edge between two nodes.
-- hasNeighbor :: Graph gr => gr a b -> Node -> Node -> Bool
-- hasNeighbor gr v w = w `elem` neighbors gr v
-- 
-- -- | Checks if there is a labelled edge between two nodes.
-- hasLEdge :: (Graph gr, Eq b) => gr a b -> LEdge b -> Bool
-- hasLEdge gr (v,w,l) = (w,l) `elem` lsuc gr v
-- 
-- -- | Checks if there is an undirected labelled edge between two nodes.
-- hasNeighborAdj :: (Graph gr, Eq b) => gr a b -> Node -> (b,Node) -> Bool
-- hasNeighborAdj gr v a = a `elem` lneighbors gr v
-- 
-- ----------------------------------------------------------------------
-- -- GRAPH EQUALITY
-- ----------------------------------------------------------------------
-- 
-- slabNodes :: (Graph gr) => gr a b -> [LNode a]
-- slabNodes = sortBy (compare `on` fst) . labNodes
-- 
-- glabEdges :: (Graph gr) => gr a b -> [GroupEdges b]
-- glabEdges = map (GEs . groupLabels)
--             . groupBy ((==) `on` toEdge)
--             . sortBy (compare `on` toEdge)
--             . labEdges
--   where
--     groupLabels les = toLEdge (toEdge (head les)) (map edgeLabel les)
-- 
-- equal :: (Eq a,Eq b,Graph gr) => gr a b -> gr a b -> Bool
-- equal g g' = slabNodes g == slabNodes g' && glabEdges g == glabEdges g'
-- -- This assumes that nodes aren't repeated (which shouldn't happen for
-- -- sane graph instances).  If node IDs are repeated, then the usage of
-- -- slabNodes cannot guarantee stable ordering.
-- 
-- -- Newtype wrapper just to test for equality of multiple edges.  This
-- -- is needed because without an Ord constraint on `b' it is not
-- -- possible to guarantee a stable ordering on edge labels.
-- newtype GroupEdges b = GEs (LEdge [b])
--   deriving (Show, Read)
-- 
-- instance (Eq b) => Eq (GroupEdges b) where
--   (GEs (v1,w1,bs1)) == (GEs (v2,w2,bs2)) = v1 == v2
--                                            && w1 == w2
--                                            && eqLists bs1 bs2
-- 
-- eqLists :: (Eq a) => [a] -> [a] -> Bool
-- eqLists xs ys = null (xs \\ ys) && null (ys \\ xs)
-- -- OK to use \\ here as we want each value in xs to cancel a *single*
-- -- value in ys.
-- 
-- ----------------------------------------------------------------------
-- -- UTILITIES
-- ----------------------------------------------------------------------
-- 
-- -- auxiliary functions used in the implementation of the
-- -- derived class members
-- --
-- (.:) :: (c -> d) -> (a -> b -> c) -> a -> b -> d
-- -- f .: g = \x y->f (g x y)
-- -- f .: g = (f .) . g
-- -- (.:) f = ((f .) .)
-- -- (.:) = (.) (.) (.)
-- (.:) = (.) . (.)
-- 
-- flip2 :: (a,b) -> (b,a)
-- flip2 (x,y) = (y,x)
-- 
-- -- projecting on context elements
-- --
-- context1l :: (Graph gr) => gr a b -> Node -> Adj b
-- context1l = maybe [] context1l' .: mcontext
-- 
-- context4l :: (Graph gr) => gr a b -> Node -> Adj b
-- context4l = maybe [] context4l' .: mcontext
-- 
-- mcontext :: (Graph gr) => gr a b -> Node -> MContext a b
-- mcontext = fst .: flip match
-- 
-- context1l' :: Context a b -> Adj b
-- context1l' (p,v,_,s) = p++filter ((==v).snd) s
-- 
-- context4l' :: Context a b -> Adj b
-- context4l' (p,v,_,s) = s++filter ((==v).snd) p
-- 
-- ----------------------------------------------------------------------
-- -- PRETTY PRINTING
-- ----------------------------------------------------------------------
-- 
-- -- | Pretty-print the graph.  Note that this loses a lot of
-- --   information, such as edge inverses, etc.
-- prettify :: (DynGraph gr, Show a, Show b) => gr a b -> String
-- prettify g = foldr (showsContext . context g) id (nodes g) ""
--   where
--     showsContext (_,n,l,s) sg = shows n . (':':) . shows l
--                                 . showString "->" . shows s
--                                 . ('\n':) . sg
-- 
-- -- | Pretty-print the graph to stdout.
-- prettyPrint :: (DynGraph gr, Show a, Show b) => gr a b -> IO ()
-- prettyPrint = putStr . prettify
-- 
-- instance Graph Gr where
--     empty           = Gr IM.empty
-- 
--     isEmpty (Gr g)  = IM.null g
-- 
--     match           = matchGr
-- 
--     mkGraph vs es   = insEdges es
--                       . Gr
--                       . IM.fromList
--                       . map (second (\l -> (IM.empty,l,IM.empty)))
--                       $ vs
-- 
--     labNodes (Gr g) = [ (node, label)
--                             | (node, (_, label, _)) <- IM.toList g ]
-- 
--     noNodes   (Gr g) = IM.size g
-- 
--     nodeRange (Gr g) = fromMaybe (error "nodeRange of empty graph")
--                        $ liftA2 (,) (ix (IM.minViewWithKey g))
--                                     (ix (IM.maxViewWithKey g))
--       where
--         ix = fmap (fst . fst)
-- 
--     labEdges (Gr g) = do (node, (_, _, s)) <- IM.toList g
--                          (next, labels)    <- IM.toList s
--                          label             <- labels
--                          return (node, next, label)
-- 
-- instance DynGraph Gr where
--     (p, v, l, s) & (Gr g)
--         = let !g1 = IM.insert v (preds, l, succs) g
--               !(np, preds) = fromAdjCounting p
--               !(ns, succs) = fromAdjCounting s
--               !g2 = addSucc g1 v np preds
--               !g3 = addPred g2 v ns succs
--           in Gr g3
-- 
-- #if MIN_VERSION_containers (0,4,2)
-- instance (NFData a, NFData b) => NFData (Gr a b) where
--   rnf (Gr g) = rnf g
-- #endif
-- 
-- #if MIN_VERSION_base (4,8,0)
-- instance Bifunctor Gr where
--   bimap = fastNEMap
-- 
--   first = fastNMap
-- 
--   second = fastEMap
-- #endif
-- 
-- matchGr :: Node -> Gr a b -> Decomp Gr a b
-- matchGr node (Gr g)
--     = case IM.lookup node g of
--         Nothing
--             -> (Nothing, Gr g)
-- 
--         Just (p, label, s)
--             -> let !g1 = IM.delete node g
--                    !p' = IM.delete node p
--                    !s' = IM.delete node s
--                    !g2 = clearPred g1 node s'
--                    !g3 = clearSucc g2 node p'
--                in (Just (toAdj p', node, label, toAdj s), Gr g3)
-- 
-- ----------------------------------------------------------------------
-- -- OVERRIDING FUNCTIONS
-- ----------------------------------------------------------------------
-- 
-- {-# RULES
--       "insNode/Data.Graph.Inductive.PatriciaTree"  insNode = fastInsNode
--   #-}
-- fastInsNode :: LNode a -> Gr a b -> Gr a b
-- fastInsNode (v, l) (Gr g) = g' `seq` Gr g'
--   where
--     g' = IM.insert v (IM.empty, l, IM.empty) g
-- 
-- {-# RULES
--       "insEdge/Data.Graph.Inductive.PatriciaTree"  insEdge = fastInsEdge
--   #-}
-- fastInsEdge :: LEdge b -> Gr a b -> Gr a b
-- fastInsEdge (v, w, l) (Gr g) = g2 `seq` Gr g2
--   where
--     g1 = IM.adjust addS' v g
--     g2 = IM.adjust addP' w g1
-- 
--     addS' (ps, l', ss) = (ps, l', IM.insertWith addLists w [l] ss)
--     addP' (ps, l', ss) = (IM.insertWith addLists v [l] ps, l', ss)
-- 
-- {-# RULES
--       "gmap/Data.Graph.Inductive.PatriciaTree"  gmap = fastGMap
--   #-}
-- fastGMap :: forall a b c d. (Context a b -> Context c d) -> Gr a b -> Gr c d
-- fastGMap f (Gr g) = Gr (IM.mapWithKey f' g)
--   where
--     f' :: Node -> Context' a b -> Context' c d
--     f' = ((fromContext . f) .) . toContext
-- 
-- {-# RULES
--       "nmap/Data.Graph.Inductive.PatriciaTree"  nmap = fastNMap
--   #-}
-- fastNMap :: forall a b c. (a -> c) -> Gr a b -> Gr c b
-- fastNMap f (Gr g) = Gr (IM.map f' g)
--   where
--     f' :: Context' a b -> Context' c b
--     f' (ps, a, ss) = (ps, f a, ss)
-- 
-- {-# RULES
--       "emap/Data.Graph.Inductive.PatriciaTree"  emap = fastEMap
--   #-}
-- fastEMap :: forall a b c. (b -> c) -> Gr a b -> Gr a c
-- fastEMap f (Gr g) = Gr (IM.map f' g)
--   where
--     f' :: Context' a b -> Context' a c
--     f' (ps, a, ss) = (IM.map (map f) ps, a, IM.map (map f) ss)
-- 
-- {-# RULES
--       "nemap/Data.Graph.Inductive.PatriciaTree"  nemap = fastNEMap
--   #-}
-- fastNEMap :: forall a b c d. (a -> c) -> (b -> d) -> Gr a b -> Gr c d
-- fastNEMap fn fe (Gr g) = Gr (IM.map f g)
--   where
--     f :: Context' a b -> Context' c d
--     f (ps, a, ss) = (IM.map (map fe) ps, fn a, IM.map (map fe) ss)
-- 
-- ----------------------------------------------------------------------
-- -- UTILITIES
-- ----------------------------------------------------------------------
-- 
-- toAdj :: IntMap [b] -> Adj b
-- toAdj = concatMap expand . IM.toList
--   where
--     expand (n,ls) = map (flip (,) n) ls
-- 
-- fromAdj :: Adj b -> IntMap [b]
-- fromAdj = IM.fromListWith addLists . map (second (:[]) . swap)
-- 
-- data FromListCounting a = FromListCounting !Int !(IntMap a)
--   deriving (Eq, Show, Read)
-- 
-- getFromListCounting :: FromListCounting a -> (Int, IntMap a)
-- getFromListCounting (FromListCounting i m) = (i, m)
-- {-# INLINE getFromListCounting #-}
-- 
-- fromListWithKeyCounting :: (Int -> a -> a -> a) -> [(Int, a)] -> (Int, IntMap a)
-- fromListWithKeyCounting f = getFromListCounting . foldl' ins (FromListCounting 0 IM.empty)
--   where
--     ins (FromListCounting i t) (k,x) = FromListCounting (i + 1) (IM.insertWithKey f k x t)
-- {-# INLINE fromListWithKeyCounting #-}
-- 
-- fromListWithCounting :: (a -> a -> a) -> [(Int, a)] -> (Int, IntMap a)
-- fromListWithCounting f = fromListWithKeyCounting (\_ x y -> f x y)
-- {-# INLINE fromListWithCounting #-}
-- 
-- fromAdjCounting :: Adj b -> (Int, IntMap [b])
-- fromAdjCounting = fromListWithCounting addLists . map (second (:[]) . swap)
-- 
-- -- We use differenceWith to modify a graph more than bulkThreshold times,
-- -- and repeated insertWith otherwise.
-- bulkThreshold :: Int
-- bulkThreshold = 5
-- 
-- toContext :: Node -> Context' a b -> Context a b
-- toContext v (ps, a, ss) = (toAdj ps, v, a, toAdj ss)
-- 
-- fromContext :: Context a b -> Context' a b
-- fromContext (ps, _, a, ss) = (fromAdj ps, a, fromAdj ss)
-- 
-- -- A version of @++@ where order isn't important, so @xs ++ [x]@
-- -- becomes @x:xs@.  Used when we have to have a function of type @[a]
-- -- -> [a] -> [a]@ but one of the lists is just going to be a single
-- -- element (and it isn't possible to tell which).
-- addLists :: [a] -> [a] -> [a]
-- addLists [a] as  = a : as
-- addLists as  [a] = a : as
-- addLists xs  ys  = xs ++ ys
-- 
-- addSucc :: forall a b . GraphRep a b -> Node -> Int -> IM.IntMap [b] -> GraphRep a b
-- addSucc g0 v numAdd xs
--   | numAdd < bulkThreshold = foldlWithKey' go g0 xs
--   where
--     go :: GraphRep a b -> Node -> [b] -> GraphRep a b
--     go g p l = IMS.adjust f p g
--       where f (ps, l', ss) = let !ss' = IM.insertWith addLists v l ss
--                              in (ps, l', ss')
-- addSucc g v _ xs = IMS.differenceWith go g xs
--   where
--     go :: Context' a b -> [b] -> Maybe (Context' a b)
--     go (ps, l', ss) l = let !ss' = IM.insertWith addLists v l ss
--                         in Just (ps, l', ss')
-- 
-- foldlWithKey' :: (a -> IM.Key -> b -> a) -> a -> IntMap b -> a
-- foldlWithKey' =
-- #if MIN_VERSION_containers (0,4,2)
--   IM.foldlWithKey'
-- #else
--   IM.foldWithKey . adjustFunc
--   where
--     adjustFunc f k b a = f a k b
-- #endif
-- 
-- addPred :: forall a b . GraphRep a b -> Node -> Int -> IM.IntMap [b] -> GraphRep a b
-- addPred g0 v numAdd xs
--   | numAdd < bulkThreshold = foldlWithKey' go g0 xs
--   where
--     go :: GraphRep a b -> Node -> [b] -> GraphRep a b
--     go g p l = IMS.adjust f p g
--       where f (ps, l', ss) = let !ps' = IM.insertWith addLists v l ps
--                              in (ps', l', ss)
-- addPred g v _ xs = IMS.differenceWith go g xs
--   where
--     go :: Context' a b -> [b] -> Maybe (Context' a b)
--     go (ps, l', ss) l = let !ps' = IM.insertWith addLists v l ps
--                         in Just (ps', l', ss)
-- 
-- clearSucc :: forall a b x . GraphRep a b -> Node -> IM.IntMap x -> GraphRep a b
-- clearSucc g v = IMS.differenceWith go g
--   where
--     go :: Context' a b -> x -> Maybe (Context' a b)
--     go (ps, l, ss) _ = let !ss' = IM.delete v ss
--                        in Just (ps, l, ss')
-- 
-- clearPred :: forall a b x . GraphRep a b -> Node -> IM.IntMap x -> GraphRep a b
-- clearPred g v = IMS.differenceWith go g
--   where
--     go :: Context' a b -> x -> Maybe (Context' a b)
--     go (ps, l, ss) _ = let !ps' = IM.delete v ps
--                        in Just (ps', l, ss)
