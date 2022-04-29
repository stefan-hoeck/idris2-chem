module Data.SubGraph.InductiveSearch

import Text.Smiles
import Data.Graph
import Data.IntMap
import Data.List
import Data.Vect


-- Types 

||| Record to store functions which evaluate a possible
||| correspondence of query and target vertices or bonds.
public export
record Matchers (qe,qv,te,tv : Type) where
  constructor MkMatchers
  edgeMatcher   : qe -> te -> Bool
  vertexMatcher : qv -> tv -> Bool

||| List of which query node is mapped to which target node
Mapping : Type
Mapping = List (Node, Node)


record EligibleTarget where
  constructor MkElTrg
  qryN : Node
  trgs : List Node

||| A list that describes which target nodes are potential
||| mapping targets for a specific query.
NextMatches : Type
NextMatches = List EligibleTarget

-- Utility Functions 

-- Finding optimal starting nodes ---------------------------------------------

||| Record to goup up the vertices by their label
||| and degree. Counts the number of occurences and
||| stores the nodes belonging to that group.
record NodeClass lv where
  constructor MkNodeCls
  lbl   : lv
  deg   : Nat
  size  : Nat
  nodes : Vect size Node 

-- Build node classes

||| Degree of a node. Not present in Graph.Util.
deg : Context e v -> Nat
deg = length . toList . neighbours

||| Used for building a list of the node classes from
||| a list of contexts. This function evaluates whether
||| the accumulator list contains a NodeClass corresponding
||| to the context argument. If there is one, then the node
||| is inserted and the count increased. If ther is none,
||| then a new class is added to the list.
|||
||| This function needs to accumulates the labels of one
||| graph and requires an Eq instance or a comparison function.
insertNC : Eq lv 
        => List (NodeClass lv) 
        -> Context le lv 
        -> List (NodeClass lv) 
insertNC xs c = case go xs of
  Just ls => ls
  Nothing => MkNodeCls (label c) (deg c) 
                       1 [node c] :: xs
 where go : List (NodeClass lv) -> Maybe (List (NodeClass lv))
       go []        = Nothing
       go (cls :: xs) = 
         if (label c) == lbl cls && deg cls == (deg c)
         then pure $ {size $= S, nodes $= (::) (node c)} cls :: xs
         else map ((::) cls) $ go xs


||| Generates a list of nodes grouped with their label
||| and their degree.
nodeClasses : Eq tv => Graph te tv -> List (NodeClass tv)
nodeClasses = foldl insertNC [] . contexts


-- Build list of the number of mapping targets

||| Sorts the list of nodes, grouped with the number of valid
||| targets by that number
|||
||| TODO: Change this to an eligible target and change that
|||       record to a vector.
sortNo : List (Node, Nat, List Node) -> List (Node, Nat, List Node)
sortNo = sortBy (\(_,n1,_),(_,n2,_) => compare n1 n2)


||| Accumulates the possible mapping targets of a specific query
||| context. For subgraph isomorphism, it is necessary to combine
||| the targets from all NodeClasses with a degree equal or greater
||| than the degree of the context.
mapTargets : (qv -> tv -> Bool) 
          -> List (NodeClass tv) 
          -> Context qe qv 
          -> Maybe (Node, Nat, List Node)
mapTargets p xs c = case filter pred xs of
                      [] => Nothing
                      xs => Just $ (node c,) $ foldl combine (0,[]) xs
  where pred : NodeClass tv -> Bool
        pred (MkNodeCls l d _ _) = p (label c) l && d >= (deg c)
        combine : (Nat, List Node) -> NodeClass tv -> (Nat, List Node)
        combine (s,ns) x = (plus s $ size x, ns ++ (toList $ nodes x))

||| Generates the mapping targets for every vertex in
||| the query. If any vertex does not have a viable
||| target, then it will return a Nothing to indicate
||| the impossibility of an isomorphism.
mappingNumbers : Eq tv => (qv -> tv -> Bool) 
              -> Graph qe qv 
              -> Graph te tv
              -> Maybe (List (Node, Nat, List Node))
mappingNumbers p g t = traverse (mapTargets p $ nodeClasses t) $ contexts g

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
||| query vertex is a viable mapping target.
||| A Nothing is returned in case no isomorphism is
||| possible (no viable mapping target).
newQryNode : Eq tv 
          => Matchers qe qv te tv
          -> Graph qe qv
          -> Graph te tv
          -> Maybe EligibleTarget
newQryNode m q t = let mn = mappingNumbers (vertexMatcher m) q t
                   in map (\(a,_,c) => MkElTrg a c) $ map sortNo mn >>= head'



-- Construction of new next matches -------------------------------------------

||| Sort a list of tuples based on their first value
sortFirst : Ord a => List (a, b) -> List (a, b)
sortFirst = sortBy (\a => compare (fst a) . fst) 

||| Wrap non-empty lists in a Maybe
notEmpty : List a -> Maybe (List a)
notEmpty [] = Nothing
notEmpty as = Just as

||| Filters a list of potential targets (with their edge label)
||| for nodes which have a corresponding label to the one provided.
filterByEdgeLabel : Matchers qe qv te tv 
                 -> qe 
                 -> List (Node,te) 
                 -> List Node
filterByEdgeLabel m e = map fst . filter (edgeMatcher m e . snd)

||| Match the vertex labels for each node in the 
||| targets node list (ts) to the label of node qn.
||| If lab q qn fails (shouldn't happen), it will 
||| immediately return the empty list, causing the
||| current assignment to fail eventually
filterByNodeLabel : Matchers qe qv te tv 
                 -> Graph qe qv 
                 -> Graph te tv 
                 -> (qn : Node) 
                 -> List Node 
                 -> List Node
filterByNodeLabel m q t qn ts = 
  let Just ql  = lab q qn | Nothing => []
  in filter (vMatch ql) ts
  where vMatch : qv -> Node -> Bool
        vMatch ql tn = case lab t tn of
            Just x  => vertexMatcher m ql x
            Nothing => False

||| Collects the nodes of a target that are valid for matching
||| neighbouring query nodes. Checks whether the label
||| corresponds to the neighbours label and whether the edge
||| label is equivalent (Matcher functions).
||| The neighbours of the currently mapped target node are the
||| initially possible targets for the neighbours of the current
||| query node.
neighbourTargets : Matchers qe qv te tv
                   -> Graph qe qv
                   -> Graph te tv
                   -> Context qe qv 
                   -> Context te tv 
                   -> Maybe NextMatches
neighbourTargets m q t cq ct = 
  let neighsQ = sortFirst $ pairs $ neighbours cq
      neighsT = pairs $ neighbours ct
  in traverse (filt neighsT) neighsQ
    where filt : List (Node,te) -> (Node, qe) -> Maybe EligibleTarget
          filt neighTs (n,e) = map (MkElTrg n) $ notEmpty 
                             $ filterByNodeLabel m q t n 
                             $ filterByEdgeLabel m e neighTs



-- Reduction of next matches --------------------------------------------------

||| Intended to remove the instantiated node from all potential target nodes
rmNode : Node -> List Node -> Maybe (List Node)
rmNode n = notEmpty . filter (/= n)

||| Intended to remove the instantiated node from all potential target nodes
||| TODO: Replace the traverse with a subsequent check for empty lists
|||       to evaluate the performance differences
rmNodeET : Node -> EligibleTarget -> Maybe EligibleTarget
rmNodeET n (MkElTrg qryN trgs) = MkElTrg qryN <$> rmNode n trgs

||| Merges and reduces the exiting list of potential mappings for 
||| previously adjacent nodes, with the new set of them. It also removes
||| a specified node from all lists describing potential mapping targets.
||| Note: As in merge, ys must be sorted in ascending order of the 
|||       first tuple element.
reduce : Node 
      -> List EligibleTarget
      -> List EligibleTarget
      -> Maybe NextMatches

reduce  n [] ns                 = traverse (rmNodeET n) ns
reduce  n os []                 = traverse (rmNodeET n) os
reduce  n (MkElTrg no to :: os) (MkElTrg nn tn :: ns) = 
  case compare no nn of
       GT => prepend (MkElTrg nn <$> rmNode n tn) $ reduce n (MkElTrg no to :: os) ns
       LT => prepend (MkElTrg no <$> rmNode n to) $ reduce n os (MkElTrg nn tn :: ns)
       EQ => prepend (MkElTrg no <$> merge to tn) $ reduce n os ns
       where prepend : Maybe EligibleTarget -> Maybe NextMatches -> Maybe NextMatches
             prepend e l = (::) <$> e <*> l
             merge : List Node -> List Node -> Maybe (List Node)
             merge xs ys = rmNode n $ intersect xs ys 



----------------------------------------------------------------------------

-- Recursion engine


||| Continues a subgraph isomorphism search by selecting a starting
||| node if none is present and checking if the query is empty.
recur : Eq tv => Matchers qe qv te tv
            -> NextMatches
            -> Graph qe qv
            -> Graph te tv
            -> Maybe Mapping

||| Finds a matching mapping target for a specific query node.
||| Continues with the next query node mapping if a match for
||| the current one is possible.
||| If the current mapping target is not eligible, continue
||| with the next potential target.
findTargetV : Eq tv => Matchers qe qv te tv
           -> Context qe qv 
           -> List Node
           -> NextMatches
           -> Graph qe qv
           -> Graph te tv
           -> Maybe Mapping
findTargetV m _ []         _  _ _ = Nothing
findTargetV m cq (x :: xs) ns q t = 
  let Split ct rt := match x t                     | Empty   => findTargetV m cq xs ns q t -- Should not occur if properly merged
      Just nsPot  := neighbourTargets m q rt cq ct | Nothing => findTargetV m cq xs ns q t
      Just nsNew  := reduce (node ct) ns nsPot     | Nothing => findTargetV m cq xs ns q t
      Just ms     := recur m nsNew q rt              | Nothing => findTargetV m cq xs ns q t
  in pure $ (node cq, node ct) :: ms
  


recur m [] q t = 
  if isEmpty q then Just [] 
  else let Just x := newQryNode m q t | Nothing => Nothing -- Should not occur as node extracted from query
       in recur m [x] q t

recur m ((MkElTrg n nts) :: ns) q t = 
    let Split c rq := match n q | Empty => Nothing -- Should not occur as proper merging prevents this (exceptions are invalid graphs)
    in findTargetV m c nts ns rq t

||| Function to invoke the substructure search
export
inductiveSearch : Eq tv
               => Matchers qe qv te tv 
               -> Graph qe qv 
               -> Graph te tv 
               -> Maybe Mapping
inductiveSearch m = recur m []

