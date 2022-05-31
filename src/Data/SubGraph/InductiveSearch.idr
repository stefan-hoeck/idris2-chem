module Data.SubGraph.InductiveSearch

import Data.Graph
import Data.Prim.Bits64
import Data.Maybe.NothingMax
import Data.AssocList
import Data.BitMap
import Data.List
import Data.Vect

export
withVertexLabels : Graph e v -> Maybe (Graph (e,v) v)
withVertexLabels g = MkGraph <$> traverse adj g.graph
  where label : (Node,e) -> Maybe (e,v)
        label (k,ve) = (ve,) <$> lab g k

        adj : Adj e v -> Maybe (Adj (e,v) v)
        adj (MkAdj l ps) = MkAdj l <$> traverseKV label ps


-- Utility Functions ----------------------------------------------------------

||| Degree of a node. Not present in Graph.Util.
||| O(n)   n: Size of neighbours
deg : Context e v -> Nat
deg c = length $ neighbours c

-- Types ----------------------------------------------------------------------

||| Record to store functions which evaluate a possible
||| correspondence of query and target vertices or bonds.
public export
record Matchers (qe,qv,te,tv : Type) where
  constructor MkMatchers
  edgeMatcher   : qe -> te -> Bool
  vertexMatcher : qv -> tv -> Bool

||| List of which query node is mapped to which target node
public export
Mapping : Type
Mapping = List (Node, Node)

||| A record that lists the possible mapping targets (vertices)
||| for a specific query vertex.
record EligibleTarget where
  constructor MkElTrg
  qryN : Node
  trgs : List Node
  {auto 0 prf : NonEmpty trgs}

||| Alternate constructor to build the record from a list
||| O(1)
mkElTrg : Node -> List Node -> Maybe EligibleTarget
mkElTrg _ [] = Nothing
mkElTrg n (x :: xs) = Just $ MkElTrg n (x :: xs)

||| A list that describes which target nodes are potential
||| mapping targets for each corresponding query.
NextMatches : Type
NextMatches = List EligibleTarget

||| Record to goup up the vertices by their label
||| and degree. Counts the number of occurences and
||| stores the nodes belonging to that group.
record NodeClass lv where
  constructor MkNodeCls
  lbl   : lv
  deg   : Nat
  size  : Nat
  {auto 0 prf : IsSucc size}

-- Build node class -----------------------------------------------------------

||| Used for building a list of the node classes from
||| a list of contexts. This function evaluates whether
||| the accumulator list contains a NodeClass corresponding
||| to the context argument. If there is one, then the node
||| is inserted and the count increased. If ther is none,
||| then a new class is added to the list.
|||
||| This function needs to accumulates the labels of one
||| graph and requires an Eq instance (or a comparison function).
||| O(n)   n: Length of NodeClass list
insertNC : Eq lv
        => List (NodeClass lv)
        -> Context le lv
        -> List (NodeClass lv)
insertNC xs c = go (label c) (deg c) xs
 where incCls : NodeClass lv -> NodeClass lv
       incCls (MkNodeCls l d k) = MkNodeCls l d (S k)
       go : lv -> Nat -> List (NodeClass lv) -> List (NodeClass lv)
       go lblc degc []          = [MkNodeCls lblc degc 1]
       go lblc degc (cl :: cls) = if lblc == lbl cl && deg cl == degc
                                  then incCls cl :: cls
                                  else (::) cl $ go lblc degc cls


||| Generates a list of nodes grouped with their label
||| and their degree.
||| O(n * m)     n: Length of the contexts
||| TODO:        m: From insertTargets (grows in each iteration)
export
nodeClasses : Eq tv => List (Context te tv) -> List (NodeClass tv)
nodeClasses = foldl insertNC []

-- Select best starting node --------------------------------------------------

||| Returns the number of possible mapping targets
||| for a context, given the targets node classes.
||| O(k)  k: Length of NodeClass list
nMapTrgs : (qv -> tv -> Bool)
        -> List (NodeClass tv)
        -> Context qe qv
        -> Nat
nMapTrgs p cls (MkContext nq lq ne) = go (length ne) cls
  where pred : Nat -> NodeClass tv -> Bool
        pred degq (MkNodeCls l d s) = p lq l && d >= degq
        go : Nat -> List (NodeClass tv) -> Nat
        go _ [] = Z
        go degq (x :: xs) = if pred degq x then plus (size x) (go degq xs)
                                           else go degq xs

minBy : Ord b => (a -> b) -> (as : List a) -> (0 prf : NonEmpty as) => (a,b)
minBy f (x :: xs) = foldl go (x, f x) xs
   where go : (a,b) -> a -> (a,b)
         go (a,b) va = let vb = f va in if vb < b then (va, vb) else (a,b)

||| Selects the best query context (least no. of possible
||| targets nodes).
||| O(n * m)  n: Length of Context list
|||           m: Length of NodeClass list
bestContext : (qv -> tv -> Bool)
           -> List (NodeClass tv)
           -> (qcs : List (Context qe qv))
           -> (prf : NonEmpty qcs)
           => Maybe (Context qe qv)
bestContext p cls qcs = case minBy (nMapTrgs p cls) qcs of
    (_,0) => Nothing
    res   => Just $ fst res


||| Get the possible target nodes for a specific
||| context from the target graph
possibleTrgs : (qv -> tv -> Bool)
            -> Context qe qv
            -> List (Context (te,tv) tv)
            -> Maybe EligibleTarget
possibleTrgs p (MkContext nq lq neq) cg =
  let degQ = length neq
  in mkElTrg nq $ foldl (pred degQ) Prelude.Nil cg
  where pred : Nat -> List Node -> Context (te,tv) tv -> List Node
        pred degq acc (MkContext nt lt net) = if p lq lt && length net >= degq
                                              then nt :: acc else acc

||| Build a list of the viable matching targets for
||| each query vertex. This is done by first grouping
||| the target vertices to 'NodeClasses'. Such a group
||| is unique in the label combined with its degree
||| (e.g., all vertices with two neighbours and the
||| label 'C' would be grouped together). The vertices
||| of the query are then mapped over to assign them
||| the correspinding targets from the target vertex
||| groups.
||| For subgraph isomorphism, all target vertices with
||| a degree equal to or bigger than the degree of a
||| query vertex are viable mapping targets.
||| A Nothing is returned in case no isomorphism is
||| possible (no viable mapping target).
||| O(bestET) + O(n) + O(nodeClasses)  n: Length of Context list
||| TODO
newQryNode : Eq tv
          => Matchers qe qv te tv
          -> List (NodeClass tv)
          -> List (Context (qe,qv) qv)
          -> List (Context (te,tv) tv)
          -> Maybe EligibleTarget
newQryNode _ _ [] _ = Nothing
newQryNode _ _ _ [] = Nothing
newQryNode m ncs (cq :: cqs) cst =
  let Just bc := bestContext (vertexMatcher m) ncs (cq :: cqs)
               | Nothing => Nothing -- Should be an error
  in possibleTrgs (vertexMatcher m) bc cst

-- Construction of new next matches -------------------------------------------

||| Filter possible mapping targets by node and edge label
||| O(p)     p: Length of the node list
filt : Matchers qe qv te tv -> List (Node,te,tv)
    -> (Node,qe,qv) -> Maybe EligibleTarget
filt m xs (nq,eq,vq) = mkElTrg nq $ mapMaybe
  (\(n,e,v) => if (edgeMatcher m) eq e && (vertexMatcher m) vq v
               then Just n else Nothing) xs

||| Filter possible target nodes to match for a query node.
||| The neighbours should be present, otherwise their invalid graphs.
||| Will fail for an invalid query. Ignores invalid target nodes.
||| Local traverse replacement
||| O(p * q) p: Length of the query neighbours list
|||          q: Length of the target neighbours node list
neighbourTargets : Matchers qe qv te tv
                -> Context (qe,qv) qv -> Context (te,tv) tv
                -> Maybe NextMatches
neighbourTargets m cq ct =
  go (pairs $ neighbours ct) (pairs $ neighbours cq)
  where go : List (Node,te,tv) -> List (Node, qe, qv) -> Maybe NextMatches
        go nT []        = Just []
        go nT (x :: xs) = [| (::) (filt m nT x) (go nT xs) |]

-- Reduction of next matches --------------------------------------------------

||| Intended to remove the instantiated node from all potential target nodes
||| O(n)     n: Length of targets list
rmNodeET : Node -> EligibleTarget -> Maybe EligibleTarget
rmNodeET n (MkElTrg qryN trgs) = mkElTrg qryN $ filter (/= n) trgs

||| Merges two eligible target records to one. If the resulting list
||| of possible targets is empty, then no record is returned. The
||| same is the case, if two records should be combined of different
||| query nodes. (Alternative: intersect instead of go)
||| O(m + n)     m,n: Length of the respective target lists
||| TODO: Not actually correct O notation?
merge : EligibleTarget -> EligibleTarget -> Maybe EligibleTarget
merge (MkElTrg n1 trgs1) (MkElTrg n2 trgs2) = if n1 == n2
        then mkElTrg n1 $ go trgs1 trgs2
        else Nothing
  where go : List Node -> List Node -> List Node
        go [] _ = []
        go _ [] = []
        go (x :: xs) (y :: ys) = case compare x y of
                    GT => go (x :: xs) ys
                    LT => go xs (y :: ys)
                    EQ => x :: (go xs ys)

||| Merges and reduces the exiting list of potential mappings for
||| previously adjacent nodes, with the new set of them. It also removes
||| a specified node from all lists describing potential mapping targets.
||| Note: As in merge, ys must be sorted in ascending order of the
|||       first tuple element.
||| O(m * n)        m: (Sum of) Length of the eligible targets list
|||                 n: Comparisons from rmNodeET and mergeV2
reduce : Node
      -> List EligibleTarget
      -> List EligibleTarget
      -> Maybe NextMatches
reduce  n [] ns                   = pure ns
reduce  n os []                   = trav os
  where trav : List EligibleTarget -> Maybe NextMatches
        trav []        = pure []
        trav (x :: xs) = [| (::) (rmNodeET n x) (trav xs) |]
reduce  n (et1 :: os) (et2 :: ns) =
  case compare (qryN et1) (qryN et2) of
       GT => prepend (rmNodeET n et2) $ reduce n (et1 :: os) ns
       LT => prepend (rmNodeET n et1) $ reduce n os (et2 :: ns)
       EQ => prepend (merge et1 et2) $ reduce n os ns
  where prepend : Maybe EligibleTarget -> Maybe NextMatches -> Maybe NextMatches
        prepend e l = (::) <$> e <*> l

-- Recursion engine -----------------------------------------------------------

||| Continues a subgraph isomorphism search by selecting a starting
||| node if none is present and checking if the query is empty.
recur : Eq tv => Matchers qe qv te tv
     -> List (NodeClass tv)
     -> NextMatches
     -> Graph (qe,qv) qv
     -> Graph (te,tv) tv
     -> Maybe Mapping

||| Finds a matching mapping target for a specific query node.
||| Continues with the next query node mapping if a match for
||| the current one is possible.
||| If the current mapping target is not eligible, continue
||| with the next potential target.
||| TODO: THis is not correct
||| O(k * m * n )   k: Length of potential target nodes
|||                 m: (Sum of) Length of the eligible targets list
|||                 n: Comparisons from rmNodeET and mergeV2
findTargetV : Eq tv => Matchers qe qv te tv
           -> List (NodeClass tv)
           -> Context (qe,qv) qv
           -> List Node
           -> NextMatches
           -> Graph (qe,qv) qv
           -> Graph (te,tv) tv
           -> Maybe Mapping
findTargetV m ncs _ []         _  _ _ = Nothing
findTargetV m ncs cq (x :: xs) ns q t =
  let Split ct rt := match x t                 | Empty   => findTargetV m ncs cq xs ns q t -- Should not occur if properly merged
      Just nsPot  := neighbourTargets m cq ct  | Nothing => findTargetV m ncs cq xs ns q t
      Just nsNew  := reduce (node ct) ns nsPot | Nothing => findTargetV m ncs cq xs ns q t
      Just ms     := recur m ncs nsNew q rt        | Nothing => findTargetV m ncs cq xs ns q t
  in pure $ (node cq, node ct) :: ms


recur m ncs (MkElTrg n nts :: ns) q t =
    let Split c rq := match n q | Empty => Nothing -- Should not occur as proper merging prevents this (exceptions are invalid graphs)
    in findTargetV m ncs c nts ns rq t

recur m ncs [] q t =
  if isEmpty q then Just []
  else let Just x := newQryNode m ncs (contexts q) (contexts t) | Nothing => Nothing -- Should not occur as node extracted from query
       in recur m ncs [x] q t

-- Entry function -------------------------------------------------------------

||| Function to invoke the substructure search with
||| external graph relabelling and nodeclass calculation
inductiveSearch : Eq tv
                => Matchers qe qv te tv
                -> List (NodeClass tv)
                -> Graph (qe,qv) qv
                -> Graph (te,tv) tv
                -> Maybe Mapping
inductiveSearch m ncs q t = recur m ncs [] q t

||| Function to invoke the substructure search
||| without external graph relabelling and nodeclass
||| calculation
export
inductiveSearch' : Eq tv
               => Matchers qe qv te tv
               -> Graph qe qv
               -> Graph te tv
               -> Maybe Mapping
inductiveSearch' m q t = let Just q' := withVertexLabels q | Nothing => Nothing
                             Just t' := withVertexLabels t | Nothing => Nothing
                         in recur m (nodeClasses $ contexts t') [] q' t'
