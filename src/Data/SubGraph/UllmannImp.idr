-- Naming Convention
--
-- The following abbreviations and definitions will be used througout the 
-- module to describe the functionality of the subgraph isomorphism search.
--
-- Mathematic symbols
--
-- 'in' : Set membership
--
-- Some concepts will be described using a mathematical representation of
-- functions. To clearly differentiate these from Idris syntax, they follow
-- the convention as seen here: f(x,y) |-> result 
-- (Loosely inspired by the arrow notation)
--
--
-- Abbreviations
--
-- Vq      : Set of vertices present in the query
-- Vt      : Set of vertices present in the target
-- Eq      : Set of edges present in the query.
-- Et      : Set of edges present in the target.
--
-- G(Vq,Eq): Graph of vertices Vq and edges Eq, representing the query.
--           Target analogously.
--
-- q       : An instance or value of Vq.       (q 'in' Vq)
-- t       : An instance or value of Vt.       (t 'in' Vt)
--
-- Dq      : Domain that describes the indices of the vertices in a query
-- 
-- Cq      : Codomain that describes feasible mappings of a query vertex q
--           onto the vertices of the target Vt.  Cq |-> List t
--
-- P(q,t)  : Predicate describing constraints for matching a query vertex
--           with a target vertex. This includes the following:
--             - Matching vertex attributes
--             - feasibility of the number and type of edges of a vertex
--             - same conditions extended to adjacent vertices
--               (depending on definition)
--
-- m(q)    : Maping of a vertice q in the query to a vertex t in the
--           target graph m(q) |-> t

module Data.SubGraph.UllmannImp

import Data.Graph
import Data.List
import Data.Vect
import Data.IntMap

%default total


-- TODO: Handle Partial

-- Data types and their functins ----------------------------------------------


||| A mapping is used to determine, wether a query is a subgraph
||| of a target. For a query to be a subgraph, each of its vertices must
||| be matched with one vertex in the target. Each row thus requires exactly
||| one matching vertex t (single-valued domain). Furthermore, a subgraph 
||| does not allow mapping of different query vertices (e.g., q1 and q2) onto
||| the same target vertex, meaning that each vertex t cannot appear (or 
||| be matched) multiple times in the mapping. The mapping must therefore
||| be an injective, non-surjective function.
|||
||| If the above conditions are fulfilled, then the mapping represents a
||| SubGraphIsomorphism. If a query vertex q does not have any feasible
||| matching target, then its codomain is empty and no isomorphism is
||| possible.
|||
||| During the substructure seach, it is possible, that multiple query 
||| vertices are matched on the same target vertex or on multiple target
||| vertices. In this case, the mapping is classified as 'Intermediate'
||| as it can yield in an 'EmptyCodomain' or 'SubGraphIsomorphism' upon
||| continuation of the search algorithm.
public export
data MappingHealth = SubGraphIsomorphism
                   | EmptyCodomain
                   | Intermediate



||| The query is the subgraph to be matched with a target.
public export
Query : (qEdge : Type) -> (qVertex : Type) -> Type
Query e v = Graph e v

||| Molecule matched against the query.
public export
Target : (tEdge : Type) -> (tVertex : Type) -> Type
Target e v = Graph e v

||| Definition of the matching function type
public export
Match : Type -> Type -> Type
Match a b = a -> b -> Bool 

||| The subgra isomorphism algorithm requires information on
||| how to match or compare the vertices and edges that are
||| provided. To make sure that all functionality is available,
||| the 'Settings' record type groups all necessary functionality
||| and input data in one value.
public export
record Settings qe qv te tv where
  constructor MkSettings
  query         : Query qe qv
  target        : Target te tv
  edgeMatcher   : Match qe te
  vertexMatcher : Match qv tv


-- Mapping of the query to the target

||| Representation of the query vertice indice used to access
||| a specific vertex in the graph or a row in the mapping.
public export
record Vq qe qv where
  constructor MkVq
  vq : Context qe qv

Eq (Vq qe qv) where
  MkVq a == MkVq b = node a == node b

||| Representation of the target vertice indice used to access
||| a specific vertex in the target graph or a value mapped to
||| in a domain of the mapping.
record Vt te tv where
  constructor MkVt
  vt : Context te tv 

Eq (Vt te tv) where
  MkVt a == MkVt b = node a == node b

||| Retreive all indices of the vertices in the query graph
getQueryVertices : (s : Settings qe qv te tv) => List (Vq qe qv)
getQueryVertices = map MkVq $ contexts $ query s
||| Retreive all indices of the vertices in the target graph
getTargetVertices : (s : Settings qe qv te tv) => List (Vt te tv)
getTargetVertices = map MkVt $ contexts $ target s


-- Mapping

||| Represents a collection of values that correspond to the domain V Vq.
|||
||| TODO: Something other than a list might be more beneficial for a mapping row
||| TODO: Sorting might be beneficial for elective instantiation (e.g. degree).
Domain : Type -> Type -> Type
Domain qe qv = List (Vq qe qv)

||| This domain type should represent a collection of values
||| that correspond to a codomain.
|||
||| Its primary use in this algorithm is to store the vertice indices
||| for elective instantiation and advance of the row search. 
||| TODO: Need a way to make sure that only Vts can be used for the construction
|||       Or is the constructor for codomains enough?
public export
record Codomain te tv where
  constructor MkCodomain
  value : List (Vt te tv)

Eq (Codomain te tv) where
  (==) = (==) `on` value 

emptyDomain : Domain _ _ 
emptyDomain = []
emptyCodomain : (Codomain te tv)
emptyCodomain = MkCodomain empty

||| Returns the size of a domain
domainCardinality : Domain _ _ -> Nat
domainCardinality = length
codomainCardinality : (Codomain te tv) -> Nat
codomainCardinality (MkCodomain c) = foldl (\acc,_ => acc + 1) Z c
||| Mapping : A construct describing the correspondence of a vertex in the query 
|||           and a vertex in the target. A mapping of a vertex in the query
|||           can yield multiple feasible vertices in the target. These feasible
|||            M(q) |-> Dq
public export
record Mapping qe qv te tv where
  constructor MkMapping
  -- domain  : Domain qe qv
  mapping : List (Vq qe qv, Codomain te tv)

emptyMapping : Mapping qe qv te tv
emptyMapping = MkMapping []

||| Retrieve the values that are being mapped to the codomain
||| equivalent to getQueryVertices
getDomain : Mapping qe qv te tv -> Domain qe qv
getDomain (MkMapping cs) = map fst cs

||| Retreive the values mapped to by a vertice in the query
||| TODO: Not an optimal implementation. A proof that ensures the presence of
|||       every element in the list being present in the IntMap would be beneficial
|||       to remove the Maybe context
getCodomain : (row : Vq qe qv) -> Mapping qe qv te tv -> Codomain te tv
getCodomain q = go . mapping
  where go : List (Vq qe qv, Codomain te tv) -> Codomain te tv   -- TODO: Proof!
        go [] = emptyCodomain
        go ((q',c) :: xs) = if q == q' then c
                                       else go xs

||| Used to represent that a type needs to meet certain
||| restrictions to be used. In the case of a mapping,
||| this restriction is the prematching of mapping
||| feasibilities which makes sure, that only vertices
||| which fulfill the required predicates (t) are present in
||| the codomains for m(q) |-> t.
data Prematched a = MkPrematched a


-- Algorithm utility functions ------------------------------------------------

-- Prematching



||| Compares a target vertex with a query vertex using their Node
||| indices
vertexInvar : (s : Settings qe qv te tv) => Vq qe qv -> Vt te tv -> Bool
vertexInvar (MkVq q') (MkVt t') = vertexMatcher s (label q') (label t')

||| TODO: Move utility module
||| Works like deletyBy in Data.List but is forced to delete
||| an occurence. If it fails, then it wont return the shortened list.
forcedDelete : (a -> b -> Bool) -> a -> List b -> Maybe (List b)
forcedDelete _ _ [] = Nothing
forcedDelete f a (b :: bs) = 
     if f a b then Just bs else map ((::) b) $ forcedDelete f a bs 


||| Evaluates whether vertex q can be mapped to t by comparing their edges.
||| To yield a positive result, the following criteria must be fulfilled:
|||   - degree:  A subgraph isomorphism requires that a target vertex t has
|||              equal or more edges to adjacent vertices than vertex q.
|||   - label:   For labeled graphs, as the ones here, it is also necessary
|||              compare the availability of enough edges with matching labels
|||              in the target graph. This is done using the provided function
|||              in the settings. To make sure, that no edge is mapped to
|||              multiple times (ensure injective mapping), a list of edges
|||              is used where the ones already being mapped to are removed.
edgeCoverage : (s : Settings qe qv te tv) => Vq qe qv -> Vt te tv -> Bool
edgeCoverage (MkVq q) (MkVt t) = 
       -- List of edge labels to compare
   let qEL  = map snd $ pairs $ neighbours q
       tEL  = map snd $ pairs $ neighbours t
   in matchEdges (edgeMatcher s) qEL tEL
   where 
     -- Searches a matching edge of List 2 for each edge in List 1
     -- Does not match the same edge twice (removes it)
     matchEdges : Match e1 e2 -> List e1 -> List e2 -> Bool
     matchEdges _ []         _  = True
     matchEdges _ _          [] = False
     matchEdges f (qe :: qes) tes = 
       case forcedDelete f qe tes of
          Nothing => False
          Just tesRem => matchEdges f qes tesRem

||| Adds a vertex t to a codomain
addToCodomain : Vt te tv -> Codomain te tv -> Codomain te tv
addToCodomain t (MkCodomain c) = MkCodomain $ t :: c

||| Removes a Vt from a codomain
removeFromCodomain : Vt te tv -> Codomain te tv -> Codomain te tv
removeFromCodomain t = MkCodomain . go . value
  where go : List (Vt te tv) -> List (Vt te tv)
        go [] = []
        go (x :: xs) = if t == x then xs
                                 else x :: go xs

||| Adds a codomain to a mapping for a specific Vq
addToMapping : Mapping qe qv te tv -> Vq qe qv -> Codomain te tv
             -> Mapping qe qv te tv
addToMapping (MkMapping cs) q c = MkMapping ((q,c) :: cs)

||| The initial mapping is build by comparing all vertices in the query (Vq)
||| with the available vertices in the target (Vt). For a vertice t in Vt
||| to be allowed in the codomain of the mapping of m(q) |-> t, it has to
||| fulfill the following predicates:
|||  - Vertex invariance : Meaning that the attributes of a vertex 
|||                        are compatible, verified by the 'edgeMatcher' in
|||                        the 'Settings'
|||  - Edge coverage :     Implies that enough edges with compatible attributes
|||                        to cover all edges of an atom in the query are
|||                        present for matching a target vertex.
|||                        For subgraph isomorphism, the degree (number of
|||                        edges) of a query can be smaller than the one of
|||                        a vertex in the target graph.
|||
||| Further verification is possible, by also applying the predicates above
||| to adjacent vertices
contextMatch : (s : Settings qe qv te tv) => Mapping qe qv te tv
contextMatch =
 let dom   = getQueryVertices {s = s}
     codom = getTargetVertices {s = s}
 in foldl (\m,q => addToMapping m q $
       foldl (\c,t => if vertexInvar {s = s} q t && edgeCoverage {s = s} q t
                      then addToCodomain t c
                      else c 
             ) emptyCodomain codom
          ) emptyMapping dom


    -- let dom   = getQueryVertices {s = s}
    --    codom = getTargetVertices {s = s}
    -- in foldl (\m, q => addToMapping q {m = m} $
    --           foldl (\cd,t => if vertexInvar {s = s} q t && edgeCoverage {s = s} q t 
    --                           then addToCodomain t cd 
    --                           else cd)
    --            emptyCodomain codom)
    --         emptyMapping dom 
    

||| Function which applies all necessary predicates for
||| building the mapping
prematch : (s : Settings qe qv te tv) => Prematched (Mapping qe qv te tv)
prematch = MkPrematched $ contextMatch {s = s}

-- Instantiation

||| Selects a value from a domain to set as vertex t for m(q) |-> t.
||| To make sure that each value is only chosen once (all different 
||| constraint), the remainder of the codomain is returned.
|||
||| Different methods can be applied, currently, a simple enumeration
||| is performed.
electiveInst : Codomain te tv -> Maybe (Vt te tv, Codomain te tv)
electiveInst (MkCodomain c) = case c of
                                []        => Nothing
                                (t :: ts) => Just (t, MkCodomain ts)

||| Removes all target vertices t mapped to by query vertex q from 
||| the codimain Cq, except for the instantiated vertex 'inst'
setInst : (row : Vq qe qv) -> (inst : Vt te tv) -> Mapping qe qv te tv -> Mapping qe qv te tv
setInst q t (MkMapping ms) =  MkMapping $ gp q ms
 where
   gp : (Vq qe qv) -> List (Vq qe qv, Codomain te tv) -> List (Vq qe qv, Codomain te tv)
   gp _  [] = []
   gp qi ((q',ci) :: cs) =   -- qi represents the query vertex with the instantiated value t
       if q' == qi then (q', addToCodomain t emptyCodomain) :: cs
                   else (q',ci) :: gp qi cs

-- Domain reduction


||| Removes all ocurences from subsequent rows or codomains of the
||| not yet singly mapped query vertices.
allDifferentInst : (inst : Vt te tv) -> (rows : Domain qe qv) 
                -> Mapping qe qv te tv -> Mapping qe qv te tv
allDifferentInst inst rm (MkMapping ms) = MkMapping  $ go rm ms
  where go : (remDom : Domain qe qv) 
           -> (codoms : List (Vq qe qv, Codomain te tv)) 
           -> List (Vq qe qv, Codomain te tv)
        go [] cs = cs
        go _  [] = []
        go (r :: rs) ((q,c) :: cs) = 
          if r == q
          then (q,removeFromCodomain inst c) :: go rs cs -- remove the specified key from the codomain c
          else (q,c) :: go (r :: rs) cs -- No change as before stated rows

||| Reduction of the domains of neighboring (or adjacent) codomains
||| TODO: Description
||| Direct -> immediately removes the values which can't map the target
||| Starts with the just instantiated domain and continues there...
directReduction : Mapping qe qv te tv -> Mapping qe qv te tv

||| Removes the instantiated value (inst : Vt) from all rows
||| specified by the input argument. These rows correspond to
||| all subsequent rows from the one the instantiation took place.
||| By removing the instantiated value, it won't be instantiated
||| again when continuing with subsequent rows of the mapping. 
||| Therfore pruning the search tree by enforcing the all different constraint.
||| 
||| This process can lead to empty codomains of m(q) |-> t, it is therefore
||| necessary to check the mapping after each domainReduction.
||| It is also possible to reach SubGraphIsomorphism if all codomains are
||| Single valued after domainReduction (if a codomain becomes single valued
||| due to the domain reduction, then this is called implied instantiation).
domainReduction : (inst : Vt te tv) -> (rows : Domain qe qv) 
                -> Mapping qe qv te tv -> Mapping qe qv te tv
domainReduction inst rows x = directReduction $ allDifferentInst inst rows x




-- Neighbor propagation
-- start at row A
--        - get context (neighbors B, C)
--        - codomain -> 1 (1 has adj, 4,7)
-- go through every query adj
--    B: bond(A,B) == bond(1,4) :> keep otherwise remove
--          , then the same for 7
--          if a value was removed, then add the neighbors of B to the list of neighbors to check
                                    -- this should work as a breath first search




-- Isomorphism test

||| This function evaluates what the current mapping represents.
||| The describtion of the MappingHealth lists all possible states
||| and the criteria for its selection.
|||
||| The evaluation works as followed:
||| 1. Each row (q) is checked whether its codomain Cq is empty.
|||    If it isn't, then it's values are added to an accumulator.
|||    The recursion is not interrupted to return 'Intermediate'
|||    upon finding multiple values in one codomain, since a
|||    domain reduction could have yielded an empty domain in a
|||    later q (or row).
||| 2. Once all rows were iterated, the accumulator is searched
|||    for a codomain value t with multiple occurences in the
|||    mapping. Since subgraph isomorphism is injective, no t
|||    is allowed to be present twice in a mapping. If all
|||    values of the codomain are only present once, the sum
|||    of their occurences is compared to the cardinality of
|||    the domain. If both are equal, then each value q of the
|||    domain is mapped to one value in the codomain, thus
|||    representing a valid subgraph isomophism (actually a graph
|||    isomorphism if the codomain cardinality is the same as 
|||    the domains cardinality).
|||    
|||    The previously described two steps are currently combined
|||    to one. By accumulating the numbers, if the number of
|||    occurences is not equal to the domain cardinality, then it
|||    is no isomorphism and therefore an Intermediate.
|||
|||    TODO: Is there a data type that would be quicker to check
|||          the number of occurences as a map? I think of a
|||          sorted tree or map which is ordered by descending
|||          number of occurences. This would allow us to 
|||          check the first element for its value. However,
|||          since we have to check the whole number anyway, it
|||          might not really be more efficient anyway.
|||
|||    TODO: Should I draw the domain cardinality from the settings?
|||          Not sure if Idris realises, that it stays the same
|||          over the whole process (altough it seems to be smarter
|||          than I am (very specialized tough)).
isIsomorphism : Mapping qe qv te tv -> MappingHealth
isIsomorphism m = go empty m (mapping m)
  where
   go : IntMap Nat -> Mapping qe qv te tv -> List (Vq qe qv, Codomain te tv) -> MappingHealth
   go acc m []        = if domainCardinality (getDomain m) == foldl plus Z acc
                        then SubGraphIsomorphism else Intermediate
   go acc m ((_,c) :: cs) = if c == emptyCodomain
    then EmptyCodomain
    else go (foldl (\a,(MkVt t) => insertWith plus (node t) 1 a) acc (value c))
            m cs 


-- Search algorithm

||| Tries to electively instantiate a target vertex t for a
||| query vertex q (first element in rows) and evaluate whether
||| it is possible to find a subgraph isomorphism from it.
||| A domain reduction of subsequent codomains is performed to
||| prune the search tree before evaluation.
||| 
||| If an elective instantiation yields an empty codomain for any
||| mapping m(q) |-> t, then there is no isomorphism possible and
||| the next value is elected for trial.
||| If all values of the codomain have been elected once and none
||| of them yielded a 'SubGraphIsomorphism', then Nothing is returned.
||| 
||| When retrieving the return value of the next q (next row), then
||| it must be matched to make sure that the next value in the codomain
||| is tried.
covering
rowSearch : (rows : List (Vq qe qv)) -> Codomain te tv 
          -> Mapping qe qv te tv -> Maybe (Mapping qe qv te tv)

||| Retreives the codomain Cq for the current vertex q
||| and initiates the elective search for a mapping 
||| target vertex t by invoking rowSearch.
|||
||| If this function is called without any remaining
||| vertices to map, then the algorithm returns nothing,
||| since an 'Intermediate' mapping should not be encountered
||| at this stage.
||| TODO: Different return type to represent this error
covering
initRow : (rows : List (Vq qe qv)) -> (Mapping qe qv te tv) -> Maybe (Mapping qe qv te tv)
initRow []        _ = Nothing
initRow (r :: rs) m = rowSearch (r :: rs) (getCodomain r m) m

rowSearch Nil _ _ = Nothing
rowSearch (r :: rs) dom m = do
  (vj, domRem) <- electiveInst dom
  mReduced     <- pure $ domainReduction vj rs $ setInst r vj m
  healthRM     <- pure $ isIsomorphism mReduced
  case healthRM of
       Intermediate        => case initRow rs m of
                                Nothing => rowSearch (r :: rs) domRem m
                                Just m  => Just m
       EmptyCodomain       => rowSearch (r :: rs) domRem m 
       SubGraphIsomorphism => Just mReduced
 

-- Accessor function ----------------------------------------------------------

||| Ulmann algorithm derived implementation to match a query 
||| with a target. After initializing the mapping of query vertices
||| to the possible target vertices. It initially checks the
||| whether a SubGraphIsomorphism is possible. If not, no search is
||| initiated.
covering public export
ullmannImp : (s : Settings qe qv te tv) -> Maybe (Mapping qe qv te tv)
ullmannImp s = let (MkPrematched m) := prematch {s = s}
               in case isIsomorphism m of
                       Intermediate => initRow (getQueryVertices {s = s}) m
                       EmptyCodomain => Nothing
                       SubGraphIsomorphism => Just m

