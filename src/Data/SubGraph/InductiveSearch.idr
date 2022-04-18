module Data.SubGraph.InductiveSearch

import Text.Smiles
import Data.Graph

public export
record Matchers (qe,qv,te,tv : Type) where
  constructor MkMatchers
  edgeMatcher   : qe -> te -> Bool
  vertexMatcher : qv -> tv -> Bool


-- Context qe qv |-> Current context to match.
--
-- Graph qe qv |-> Remainder of the query graph.
--
-- Graph te tv |-> Target graph to map.
--
-- Maybe (Graph te tv) |-> The subgraph of the target that has been matched.
select : Context qe qv 
       -> Graph qe qv 
       -> Graph te tv 
       -> Maybe (Graph te tv)
select qc q t = ?select_rhs

-- List Node |-> Nodes in the query to match next.
--               Initial node selected by searchIsomorphism,
--               then continue with neighbours.
--               If the list would be empty, but the query isn't, add the
--               remaining nodes to the list of nodes.
--               If a node is not present in the query, skip it.
--               If the selection procedure fails, then it is not possible
--               to map that given query node to any remaining target.
--
-- Graph qe qv |-> The remainder of the query that must still be matched.
--
-- Graph te tv |-> The remainder of the target that has not been matched.
--
-- Maybe (Graph te tv) |-> The subgraph of the target that has been matched.
step : List Node -> Graph qe qv -> Graph te tv -> Maybe (Graph te tv)









step []        q t = if isEmpty q then Just empty else step (nodes q) q t
step (x :: xs) q t = 
   let Split qc q' := match x q   | Empty   => step xs q t
       Just m      := select qc q' t | Nothing => Nothing
   in Just m




export
searchIsomorphism : Matchers qe qv te tv -> Maybe (Graph te tv)
-- TODO: Add the first step





-- choose :  SearchState qe qv te tv 
--        -> (Context qe qv, List (Context te tv))
--        -> SearchState qe qv te tv








-------------------------------------


-- Types 


-- Encodes the Resulting isomorphism (subgraph of the target) in case of a
-- match. Failure, if there is no subgraph present. Or while the search is
-- still ongoing, return the remaining query, the remaining target and the
-- currently mapped to target.  
-- And eventually, a list of which query vertices have been matched to which target vertices
data SearchState qe qv te tv = 
    Isomorphism   (Graph te tv)
  | Intermediate  (Graph qe qv) (Graph te tv) (Graph te tv)
  | Failure


record VertexClass where
  constructor MkVertexClass
  count  : Nat
  label  : SmilesElem
  degree : Nat
  keys   : List Node

record Settings qe qv te tv where
  constructor MkSettings
  matchers       : Matchers qe qv te tv
  targetVClasses : List VertexClass
  queryVClasses  : List VertexClass

-- A list of the (query node, to possible target nodes)
-- The first entry is built from the vertexClasses,
-- subsequent ones will be appended by using the neighbours
-- of both the query and the target.
NextMatches : Type
NextMatches = List (Node, List Node)

-- Functions 

-- Setup

-- Creates a list ordered by the information content of a vertex.
-- Should serve as the lookup in case no node is given for a match.
vertexClasses : Graph e v 
             -> List VertexClass

-- Searches node in the query graph that can be matched to a target
-- by comparing its vertex label and degree with the vertexClasses list
newQueryNode : Settings qe qv te tv -> Graph qe qv -> (Node, List Node)




-- Find mapping target

-- Matches a context based on the vertex label and the number and types of 
-- the edges.
compare : Matchers qe qv te tv -> Context qe qv -> Context te tv -> Bool

-- Finds a matching target for a specific query context
-- Returns the matched context, the remaining graph, and the not yet
-- tried target nodes in case further search would fail.
findTargetV : Settings qe qv te tv
           -> Context qe qv
           -> Graph te tv
           -> List Node
           -> Maybe (Context te tv, Graph te tv, List Node)
findTargetV _ _ _ []        = Nothing
findTargetV s cq t (x :: xs) = 
  let Split ct rt := match x t | Empty => findTargetV s cq t xs
  in if compare (matchers s) cq ct then Just (ct, rt, xs) 
                                   else findTargetV s cq t xs


-- Recursion engine

zipToEach : List a -> List b -> List (a, List b)
zipToEach (x :: xs) ys = (x, ys) :: zipToEach xs ys
zipToEach []        _  = []

-- Sets up the bfs by appending the neighbours of the current node to the
-- list of vertices to visit (List Node).
-- TODO: This function is very complex, abstract it further (after writing Matlab...)
bfsRecursion : Settings qe qv te tv
            -> NextMatches
            -> SearchState qe qv te tv
            -> SearchState qe qv te tv

bfsRecursion s (q :: qs) (Intermediate rq rt mt) = 
  if isEmpty rq then Isomorphism mt 
  else 
   let (Split cq rq')       := match (fst q) rq            -- Get query context
           | Empty             => bfsRecursion s qs (Intermediate rq rt mt) -- Already mapped 
       Just (ct', rt', tns) := findTargetV s cq rt (snd q) -- Get target context
           | Nothing           => Failure                  -- No valid mapping
           -- target found, continue
           -- if fails -> try next possible target mapping
   in case bfsRecursion s (qs ++ zipToEach ?asdf ?ou) (Intermediate rq' rt' $ add ct' mt) of
           Failure => ?tryNextxsOfFindTargetV
           x => x

-- If the map next list is empty
bfsRecursion s [] (Intermediate rq rt mt) = 
    if isEmpty rq then Isomorphism mt
    else bfsRecursion s [newQueryNode s rq] (Intermediate rq rt mt) -- nonempty get next node to map
-- Failure or Isomorphism case for x
bfsRecursion _ _ x = x


-- Search start (breath first setup)
bfs : Matchers qe qv te tv 
    -> Graph qe qv 
    -> Graph te tv 
    -> Maybe (Graph te tv)
bfs m q t =
  let tvc = vertexClasses t
      qvc = vertexClasses q
      s  = MkSettings m tvc qvc
      nq = newQueryNode s q
  in ?StateToMaybe $ bfsRecursion s [nq] (Intermediate q t empty)
