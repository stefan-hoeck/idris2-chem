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


||| A list that describes which target nodes are potential
||| mapping targets for a specific query.
NextMatches : Type
NextMatches = List (Node, List Node)

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
            -> Maybe (Node, List Node)
newQueryNode m q t = 
 let Just c := head' $ contexts q | Nothing => Nothing
     nts = map node $ filter (contextMatch m c) 
                    $ contexts t
 in Just (node c, nts)




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
  in traverse (\(n,e) => map (n,) $ filterByEdge e neighsT) neighsQ
    where
     filterByEdge : qe -> List (Node, te) -> Maybe (List Node)
     filterByEdge l = notEmpty . map fst . filter (edgeMatcher m l . snd)



-- New -----------------------------------------------------------------------

||| Intended to remove the instantiated node from all potential target nodes
rmNode : Node -> List Node -> Maybe (List Node)
rmNode n = notEmpty . filter (/= n)


||| xs represents the new possible matches for vertices adjacent
||| to the last set node. If one of the new nodes is already in
||| the list (first argument), then it would be merged here by
||| taking the the intersection of the potential targets.
||| Note: The list of xs must be in ascending order of the 
|||       first tuple elemen)
merge : (Node, List Node) -> List (Node, List Node) 
     -> Maybe (List Node, List (Node, List Node))
merge (_, es) [] = Just (es, [])
merge (ne, es) ((n,ns) :: xs) = case compare n ne of
        LT => map (mapSnd ((::) (n,ns))) $ merge (ne,es) xs
        EQ => map (,xs) $ notEmpty $ intersect es ns
        GT => pure (es, (n,ns) :: xs)


||| Merges and reduces the exiting list of potential mappings for 
||| previously adjacent nodes, with the new set of them. It also removes
||| a specified node from all lists describing potential mapping targets.
||| Note: As in merge, ys must be sorted in ascending order of the 
|||       first tuple element.
reduce : Node 
      -> List (Node, List Node) 
      -> List (Node, List Node) 
      -> Maybe NextMatches

reduce  _ [] []             = Just []

reduce  n [] ((q,ts) :: ys) = 
  let Just ts' := rmNode n ts | Nothing => Nothing
  in map ((::) (q,ts')) $ reduce n [] ys

reduce n (x :: xs) ys =
  let Just (ts, ys') := merge x ys  | Nothing => Nothing
      Just ts'       := rmNode n ts | Nothing => Nothing
  in map ((::) (fst x, ts')) $ reduce n xs ys'



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
      let Just nsPot := neighbourTargets m cq ct  | Nothing => Nothing
          Just nsNew := reduce (node ct) ns nsPot | Nothing => Nothing
          Just ms := bfs m nsNew q rt | Nothing => findTargetV m cq xs ns q t
      in pure $ (node cq, node ct) :: ms
     else findTargetV m cq xs ns q t
  


bfs m [] q t = 
  if isEmpty q then Just [] 
  else let Just x := newQueryNode m q t | Nothing => Nothing
       in bfs m [x] q t

bfs m ((n,nts) :: ns) q t = 
    let Split c rq := match n q | Empty => bfs m ns q t
    in findTargetV m c nts ns rq t

export
inductiveSearch : Matchers qe qv te tv 
               -> Graph qe qv 
               -> Graph te tv 
               -> Maybe Mapping
inductiveSearch m = bfs m []

