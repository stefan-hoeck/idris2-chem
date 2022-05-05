module Data.SubGraph.InductiveSearch

import Text.Smiles
import Data.Graph
import Data.IntMap
import Data.List
import Data.Vect


-- Utility Functions 

||| Degree of a node. Not present in Graph.Util.
deg : Context e v -> Nat
deg = length . toList . neighbours

||| Sort a list of tuples based on their first value
sortFirst : Ord a => List (a, b) -> List (a, b)
sortFirst = sortBy (\a => compare (fst a) . fst) 

||| Wrap non-empty lists in a Maybe
notEmpty : List a -> Maybe (List a)
notEmpty [] = Nothing
notEmpty as = Just as

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


||| A record that lists the possible mapping targets (vertices)
||| for a specific query vertex.
record EligibleTarget where
  constructor MkElTrg
  qryN : Node
  trgs : List Node
  {auto 0 prf : NonEmpty trgs}

||| Alternate constructor to build the record from a list
mkElTrg : Node -> List Node -> Maybe EligibleTarget
mkElTrg _ [] = Nothing
mkElTrg n (x :: xs) = Just $ MkElTrg n (x :: xs)
||| Record to goup up the vertices by their label
||| and degree. Counts the number of occurences and
||| stores the nodes belonging to that group.
record NodeClass lv where
  constructor MkNodeCls
  lbl   : lv
  deg   : Nat
  size  : Nat
  nodes : Vect size Node 
  {auto 0 prf : IsSucc size} 

||| A list that describes which target nodes are potential
||| mapping targets for each corresponding query.
NextMatches : Type
NextMatches = List EligibleTarget

||| Alternative constructor to build the NodeClass 
||| from a list of nodes
mkNodeCls : lv -> Nat -> List Node -> Maybe (NodeClass lv)
mkNodeCls _ _ []        = Nothing
mkNodeCls l d (x :: xs) = Just $ MkNodeCls l d (length $ x :: xs)
                                               (fromList $ x :: xs)

||| Inserts a node into the list of a NodeClass
nodeIntoCls : Node -> NodeClass lv -> NodeClass lv
nodeIntoCls n (MkNodeCls l d k nodes) = MkNodeCls l d (S k) (n :: nodes)

||| Empty EligibleTarget are not valid. Instead, 
||| this function can be used to creaet an initial
||| EligibleTarget from a NodeClass.
elTrgFromCls : Node -> NodeClass lv -> EligibleTarget
elTrgFromCls n (MkNodeCls _ _ (S k) (x :: xs)) = MkElTrg n $ [x] ++ toList xs


||| Inserts the nodes of a NodeClass into the vector of
||| eligible targets. Indended usage: Accumulation of
||| the nodes from all NodeClasses which correspond with
||| the current Context (node in EligibleTarget).
||| TODO: How to adjust the proof to the longer list???
insertTargets : EligibleTarget -> NodeClass lv -> EligibleTarget
insertTargets (MkElTrg n (t :: ts)) (MkNodeCls _ _ m xs) =
  MkElTrg n (t :: ts ++ toList xs)


-- Build node classs

||| Used for building a list of the node classes from
||| a list of contexts. This function evaluates whether
||| the accumulator list contains a NodeClass corresponding
||| to the context argument. If there is one, then the node
||| is inserted and the count increased. If ther is none,
||| then a new class is added to the list.
|||
||| This function needs to accumulates the labels of one
||| graph and requires an Eq instance (or a comparison function).
insertNC : Eq lv 
        => List (NodeClass lv) 
        -> Context le lv 
        -> List (NodeClass lv) 
insertNC xs c = case go xs of
  Just ls => ls
  Nothing => MkNodeCls (label c) (deg c) 1 [node c] :: xs
 where go : List (NodeClass lv) -> Maybe (List (NodeClass lv))
       go []        = Nothing
       go (cls :: xs) = 
         if (label c) == lbl cls && deg cls == (deg c)
         then pure $ (nodeIntoCls (node c) cls) :: xs
         else map ((::) cls) $ go xs


||| Generates a list of nodes grouped with their label
||| and their degree.
nodeClasses : Eq tv => Graph te tv -> List (NodeClass tv)
nodeClasses = foldl insertNC [] . contexts


-- Build list of the number of mapping targets

||| Sorts the list of nodes, grouped with the number of valid
||| targets by that number
sortNo : List EligibleTarget -> List EligibleTarget
sortNo = sortBy (\a => compare (length $ trgs a) . length . trgs)

||| Accumulates the possible mapping targets of a specific query
||| context. For subgraph isomorphism, it is necessary to combine
||| the targets from all NodeClasses with a degree equal or greater
||| than the degree of the context.
mapTargets : (qv -> tv -> Bool) 
          -> List (NodeClass tv) 
          -> Context qe qv 
          -> Maybe EligibleTarget
mapTargets p cls c = case filter pred cls of
     [] => Nothing
     (x :: xs) => Just $ foldl insertTargets (elTrgFromCls (node c) x) xs
  where pred : NodeClass tv -> Bool
        pred (MkNodeCls l d _ _) = p (label c) l && d >= (deg c)

||| Generates the mapping targets for every vertex in
||| the query. If any vertex does not have a viable
||| target, then it will return a Nothing to indicate
||| the impossibility of an isomorphism.
mappingNumbers : Eq tv => (qv -> tv -> Bool) 
              -> Graph qe qv 
              -> Graph te tv
              -> Maybe (List EligibleTarget)
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
                   in map sortNo mn >>= head'



-- Construction of new next matches -------------------------------------------

||| Node label lookup
qlbl : Graph qe qv -> (Node, qe) -> Maybe (Node, qe, qv)
qlbl q (n,e) = (n,e,) <$> lab q n 
       
||| Target label lookup
tlbl : Graph te tv -> List (Node, te) -> List (Node, te, tv)
tlbl t = mapMaybe (\(n,e) => (n,e,) <$> lab t n) 

||| Filter node and edge label
filt : Matchers qe qv te tv -> List (Node,te,tv) 
    -> (Node,qe,qv)-> Maybe EligibleTarget
filt m xs (nq,eq,vq) = mkElTrg nq $ mapMaybe 
  (\(n,e,v) => if (edgeMatcher m) eq e && (vertexMatcher m) vq v 
               then Just n 
               else Nothing) xs

||| Converts list of contexts to list of node & labels
||| Local traverse replacement
neighQ : Graph qe qv -> Context qe qv -> Maybe (List (Node, qe, qv))
neighQ q (MkContext n l ns) = go $ pairs ns
  where go : List (Node, qe) -> Maybe (List (Node, qe, qv))
        go []        = Just []
        go (x :: xs) = [| (::) (qlbl q x) (go xs) |]



||| Filter possible target nodes to match for a query node.
||| TODO: The neighbours should be present, otherwise their invalid graphs.
|||       Will fail for an invalid query. Ignores invalid target nodes.
||| Local traverse replacement
neighbourTargets : Matchers qe qv te tv -> Graph qe qv    -> Graph te tv
                -> Context qe qv        -> Context te tv  -> Maybe NextMatches
neighbourTargets m q t cq ct = 
  let Just neighsQ := neighQ q cq | Nothing => Nothing
      neighsT = tlbl t $ pairs $ neighbours ct
  in go neighsT neighsQ
  where go : List (Node,te,tv) -> List (Node, qe, qv) -> Maybe NextMatches
        go nT []        = Just []
        go nT (x :: xs) = [| (::) (filt m nT x) (go nT xs) |]



-- Reduction of next matches --------------------------------------------------

||| Intended to remove the instantiated node from all potential target nodes
||| TODO: Replace the traverse with a subsequent check for empty lists
|||       to evaluate the performance differences
rmNodeET : Node -> EligibleTarget -> Maybe EligibleTarget
rmNodeET n (MkElTrg qryN trgs) = mkElTrg qryN $ filter (/= n) trgs

||| Merges two eligible target records to one. If the resulting list
||| of possible targets is empty, then no record is returned. The
||| same is the case, if two records should be combined of different
||| query nodes.
merge : EligibleTarget -> EligibleTarget -> Maybe EligibleTarget
merge (MkElTrg n1 trgs1) (MkElTrg n2 trgs2) = if n1 == n2
         then mkElTrg n1 $ intersect (toList trgs1) (toList trgs2)
         else Nothing

mergeV2 : EligibleTarget -> EligibleTarget -> Maybe EligibleTarget
mergeV2 (MkElTrg n1 trgs1) (MkElTrg n2 trgs2) = if n1 == n2
        then mkElTrg n1 $ intersect (toList trgs1) (toList trgs2)
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
       EQ => prepend (mergeV2 et1 et2 >>= rmNodeET n) $ reduce n os ns
  where prepend : Maybe EligibleTarget -> Maybe NextMatches -> Maybe NextMatches
        prepend e l = (::) <$> e <*> l





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
      Just ms     := recur m nsNew q rt            | Nothing => findTargetV m cq xs ns q t
  in pure $ (node cq, node ct) :: ms
  

recur m (MkElTrg n nts :: ns) q t = 
    let Split c rq := match n q | Empty => Nothing -- Should not occur as proper merging prevents this (exceptions are invalid graphs)
    in findTargetV m c nts ns rq t

recur m [] q t = 
  if isEmpty q then Just [] 
  else let Just x := newQryNode m q t | Nothing => Nothing -- Should not occur as node extracted from query
       in recur m [x] q t

||| Function to invoke the substructure search
export
inductiveSearch : Eq tv
               => Matchers qe qv te tv 
               -> Graph qe qv 
               -> Graph te tv 
               -> Maybe Mapping
inductiveSearch m = recur m []

