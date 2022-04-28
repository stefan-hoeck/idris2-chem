module Data.SubGraph.InductiveSearch

import Text.Smiles
import Data.Graph
import Data.IntMap
import Data.List


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

-- Functions 

||| Evaluates whether a query context can be mapped on a specific target
||| context. This includes a matching node label and the presence of
||| enough edges with a matching label.
contextMatch : Matchers qe qv te tv 
            -> Context qe qv 
            -> Context te tv 
            -> Bool
contextMatch m q t = 
  let vm = vertexMatcher m (label q) (label t) 
      em = isNil $ deleteFirstsBy (flip $ edgeMatcher m)
           (values $ neighbours q) (values $ neighbours t)
  in vm && em


-- Setup

-- TODO: Optimize
-- Searches node in the query graph that can be matched to a target
-- by comparing its vertex label and degree with the vertexClasses list
newQueryNode : Matchers qe qv te tv 
            -> Graph qe qv 
            -> Graph te tv 
            -> Maybe EligibleTarget
newQueryNode m q t = 
 let Just c := head' $ contexts q | Nothing => Nothing
     nts = map node $ filter (contextMatch m c) 
                    $ contexts t
 in Just (MkElTrg (node c) nts)




-- Find mapping target

||| Sort a list of tuples based on their first value
sortFirst : Ord a => List (a, b) -> List (a, b)
sortFirst = sortBy (\a => compare (fst a) . fst) 

||| Wrap non-empty lists in a Maybe
notEmpty : List a -> Maybe (List a)
notEmpty [] = Nothing
notEmpty as = Just as

||| Constructs the list of possible mapping targets for adjacent query
||| nodes to the one currently selected (cq). Uses the adjacent nodes of
||| the current mapping target to evaluate possible mappings. Removes
||| those with an incorrect bond label.
||| Sorted in ascending order.
neighbourTargets : Matchers qe qv te tv
                -> Context qe qv 
                -> Context te tv 
                -> Maybe NextMatches
neighbourTargets m cq ct = 
  let neighsQ  = sortFirst $ pairs $ neighbours cq
      neighsT  = pairs $ neighbours ct
  in traverse (\(n,e) => map (MkElTrg n) $ filterByEdge e neighsT) neighsQ
    where
     filterByEdge : qe -> List (Node, te) -> Maybe (List Node)
     filterByEdge l = notEmpty . map fst . filter (edgeMatcher m l . snd)



-- New -----------------------------------------------------------------------

||| Intended to remove the instantiated node from all potential target nodes
rmNode : Node -> List Node -> Maybe (List Node)
rmNode n = notEmpty . filter (/= n)

||| Intended to remove the instantiated node from all potential target nodes
||| TODO: Replace the traverse with a subsequent check for empty lists
|||       to evaluate the performance differences
rmNodeET : Node -> EligibleTarget -> Maybe EligibleTarget
rmNodeET n (MkElTrg qryN trgs) = MkElTrg qryN <$> rmNode n trgs

||| xs represents the new possible matches for vertices adjacent
||| to the last set node. If one of the new nodes is already in
||| the list (first argument), then it would be merged here by
||| taking the the intersection of the potential targets.
||| Note: The list of xs must be in ascending order of the 
|||       first tuple elemen)
merge : EligibleTarget -> List EligibleTarget
     -> Maybe (List Node, List EligibleTarget)
merge (MkElTrg _ es) [] = Just (es, [])
merge (MkElTrg ne es) (MkElTrg n ns :: xs) = case compare n ne of
        LT => map (mapSnd ((::) (MkElTrg n ns))) $ merge (MkElTrg ne es) xs
        EQ => map (,xs) $ notEmpty $ intersect es ns
        GT => pure (es, MkElTrg n ns :: xs)


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


||| Initiates a subgraph isomorphism search by selecting a starting
||| node and checking if the query is empty.
bfs : Matchers qe qv te tv
            -> NextMatches
            -> Graph qe qv
            -> Graph te tv
            -> Maybe Mapping

||| Finds a matching mapping target for a specific query node.
||| Continues with the next query node mapping if a match for
||| the current one is possible.
||| If the current mapping target is not eligible, continue
||| with the next potential target.
findTargetV : Matchers qe qv te tv
           -> Context qe qv 
           -> List Node
           -> NextMatches
           -> Graph qe qv
           -> Graph te tv
           -> Maybe Mapping
findTargetV m _ []         _  _ _ = Nothing
findTargetV m cq (x :: xs) ns q t = 
  let Split ct rt := match x t | Empty => findTargetV m cq xs ns q t -- Should not occur if properly merged
  in if contextMatch m cq ct 
     then 
      let Just nsPot := neighbourTargets m cq ct  | Nothing => findTargetV m cq xs ns q t
          Just nsNew := reduce (node ct) ns nsPot | Nothing => findTargetV m cq xs ns q t
          Just ms := bfs m nsNew q rt | Nothing => findTargetV m cq xs ns q t
      in pure $ (node cq, node ct) :: ms
     else findTargetV m cq xs ns q t
  


bfs m [] q t = 
  if isEmpty q then Just [] 
  else let Just x := newQueryNode m q t | Nothing => Nothing -- Should not occur as node extracted from query
       in bfs m [x] q t

bfs m ((MkElTrg n nts) :: ns) q t = 
    let Split c rq := match n q | Empty => Nothing -- Should not occur as proper merging prevents this (exceptions are invalid graphs)
    in findTargetV m c nts ns rq t

export
inductiveSearch : Matchers qe qv te tv 
               -> Graph qe qv 
               -> Graph te tv 
               -> Maybe Mapping
inductiveSearch m = bfs m []

