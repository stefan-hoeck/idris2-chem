module Data.SubGraph.UllmannImp

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


import Data.Graph
import Data.Vect
import Data.IntMap

%default total


-- TODO: Handle Partial
-- TODO: Change to 'Settings =>'

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
data MappingHealth = SubGraphIsomorphism
                   | EmptyCodomain
                   | Intermediate



||| The query is the subgraph to be matched with a target.
Query : (qEdge : Type) -> (qVertex : Type) -> Type
Query e v = Graph e v

||| Molecule matched against the query.
Target : (tEdge : Type) -> (tVertex : Type) -> Type
Target e v = Graph e v

||| Definition of the matching function type
Match : Type -> Type -> Type
Match a b = a -> b -> Bool 

||| The subgra isomorphism algorithm requires information on
||| how to match or compare the vertices and edges that are
||| provided. To make sure that all functionality is available,
||| the 'Settings' record type groups all necessary functionality
||| and input data in one value.
record Settings where
  constructor MkSettings
  query         : Query qe qv
  target        : Target te tv
  edgeMatcher   : Match qe te
  vertexMatcher : Match qv tv


-- Mapping of the query to the target

||| Representation of the query vertice indice used to access
||| a specific vertex in the graph or a row in the mapping.
Vq : Type
Vq = Node
||| Representation of the target vertice indice used to access
||| a specific vertex in the target graph or a value mapped to
||| in a domain of the mapping.
Vt : Type
Vt = Node


||| Retreive all indices of the vertices in the query graph
getQueryVertices : Settings -> List Vq
getQueryVertices s = nodes $ query s -- keys $ graph $ query s
||| Retreive all indices of the vertices in the target graph
getTargetVertices : Settings -> List Vt
getTargetVertices s = nodes $ query s -- keys $ graph $ target s


-- Mapping

||| Mapping : A construct describing the correspondence of a vertex in the query 
|||           and a vertex in the target. A mapping of a vertex in the query
|||           can yield multiple feasible vertices in the target. These feasible
|||            M(q) |-> Dq
Mapping : Type
-- TODO

||| Represents a collection of values that correspond to the domain V Vq.
|||
||| TODO: Something other than a list might be more beneficial for a mapping row
||| TODO: Sorting might be beneficial for elective instantiation (e.g. degree).
Domain : Type
Domain = List Vq

||| This domain type should represent a collection of values
||| that correspond to a codomain.
|||
||| Its primary use in this algorithm is to store the vertice indices
||| for elective instantiation and advance of the row search. 
Codomain : Type
Codomain = List Vt

||| Retrieve the values that are being mapped to the codomain
||| equivalent to getQueryVertices
getDomain : Mapping -> Domain
-- TODO
||| Retreive the values mapped to by a vertice in the query
getCodomain : (row : Vq) -> Mapping -> Codomain
-- TODO

||| Returns the size of a domain
-- TODO: Unnecessary alias. But useful for my comprehension for now (remove?)
domainCardinality : Domain -> Nat
domainCardinality = length
codomainCardinality : Codomain -> Nat
codomainCardinality = length

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
vertexInvar : Settings -> Vq -> Vt -> Bool
vertexInvar s q' t' = fromMaybe False $ 
    (vertexMatcher s) <$> (lab (query s) q') <*> (lab (target s) t')

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
edgeCoverage : Settings -> Vq -> Vt -> Bool
edgeCoverage s q t = 
   let qry  = query s
       trg  = target s
       -- List of edge labels to compare
       qEL  = traverse (\n => elab qry q n) $ neighbours qry q
       tEL  = traverse (\n => elab trg t n) $ neighbours trg t
   in fromMaybe False $ matchEdges (edgeMatcher s) <$> qEL <*> tEL
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
|||
||| -> TODO: I need Vq to be the type of the querys vertices
contextMatch : Settings -> Mapping
contextMatch s = 
    let dom   = nodes $ query s
        codom = nodes $ target s
    in foldl (\m,q => ?insertCodomainToDomainMappingContainer $ 
               foldl (\cd,t => if vertexInvar s q t
                               then ?ifTrueAddToCodomain $ edgeCoverage s q t
                               else ?doNotAddToCodomain
                     )
               ?emptycodom codom) 
       ?emptyMapping dom
    
-- 1. Match vertices
-- 2. Match edge type coverage with numbers present

||| Function which applies all necessary predicates for
||| building the mapping
prematch : Settings -> Prematched Mapping
prematch = MkPrematched . contextMatch

-- Instantiation & reduction

||| Selects a value from a domain to set as vertex t for m(q) |-> t.
||| To make sure that each value is only chosen once (all different 
||| constraint), the remainder of the codomain is returned.
|||
||| Different methods can be applied, currently, a simple enumeration
||| is performed.
electiveInst : Codomain -> Maybe (Vt, Codomain)
electiveInst []        = Nothing
electiveInst (x :: xs) = Just (x, xs)


||| Removes all target vertices t mapped to by query vertex q from 
||| the codimain Cq, except for the instantiated vertex 'inst'
setInst : (row : Vq) -> (inst : Vt) -> Mapping -> Mapping
-- TODO

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
domainReduction : (inst : Vt) -> (rows : Domain) -> Mapping -> Mapping
domainReduction _ []        m = m
domainReduction v (r :: rs) m = domainReduction v rs (removeKey v r m)
  where removeKey : (inst : Vt) -> (row : Vq) -> Mapping -> Mapping

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
isIsomorphism : Mapping -> MappingHealth
isIsomorphism m = go empty (getDomain m) m
   where
     go : IntMap Nat -> (rows : Domain) -> Mapping -> MappingHealth
     go acc []        m = if (==) (domainCardinality (getDomain m)) 
                             $ foldl plus Z acc 
                          then SubGraphIsomorphism else Intermediate
     go acc (r :: rs) m = case getCodomain r m of
            [] => EmptyCodomain
            cd => go (foldl (\a,t => insertWith plus t 1 a) acc cd) rs m


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
partial
rowSearch : (rows : List Vq) -> Codomain -> Mapping -> Maybe Mapping

||| Retreives the codomain Cq for the current vertex q
||| and initiates the elective search for a mapping 
||| target vertex t by invoking rowSearch.
|||
||| If this function is called without any remaining
||| vertices to map, then the algorithm returns nothing,
||| since an 'Intermediate' mapping should not be encountered
||| at this stage.
||| TODO: Different return type to represent this error
partial
initRow : (rows : List Vq) -> Mapping -> Maybe Mapping
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
partial
ullmannImp : (s : Settings) -> Maybe Mapping
ullmannImp s = let (MkPrematched m) := prematch s
               in case isIsomorphism m of
                       Intermediate => initRow (getQueryVertices s) m
                       EmptyCodomain => Nothing
                       SubGraphIsomorphism => Just m

