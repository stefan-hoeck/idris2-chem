module Data.SubGraph.Ullmann

-------------------------------------------------------------------------------
-- References
-- Ullmann [2010]: Bit-Vector Algorithms for Binary Constraint Satisfaction
--                 and Subgraph Isomorphism
--                 Julian R. Ullmann, King's College London, 2010
--
-- Lecoutre [200]: 


import Data.Vect
import Data.Graph
import Data.SubGraph.Comparison
import Data.SubGraph.CompatibilityMatrix

%default total

-- Fundamental types ----------------------------------------------------------


-- Query and target explicit different names that to point out the
-- differences and addition of potential functionality

||| The query is the subgraph to be searched in the
||| Target. -> Subgraph isomorphism
Query : (qEdge : Type) -> (qVertex : Type) -> Type
Query e v = Graph e v

||| Molecule matched against the query. A target is
||| a molecule taken from the database.
Target : (tEdge : Type) -> (tVertex : Type) -> Type
Target e v = Graph e v

Match : Type -> Type -> Type
Match a b = a -> b -> Bool 


-- Data / Functionality for the algorithm -------------------------------------

record Settings where
  constructor MkSettings
  query         : Query qe qv
  target        : Target te tv
  edgeMatcher   : Match qe te
  vertexMatcher : Match qv tv
  -- Query & target to adjacency list 
  -- Vect n (Vect m qv or tv)

-- TODO: NOTE:
--  E.g. Edge matching: exact, only connectivity, ...


-- Algorithm helper functions -------------------------------------------------



||| Applies the following predicates to the initial compatibility matrix
||| to reduce the domains before entering the search algorithm
||| 
||| Definitions:
|||    Vi: Vertex of query,          u: Value of Vi
|||    Vj: Vertex of target,         v: Value of Vj
|||    Vk: Adjacent vertices of Vi
|||
||| Predicates:
|||   - Vertex matching:    Do the vertex attributes match
|||                         Apply vertexMatcher on  u = v
|||                         Unary predicate
|||   - Edge type matching: Are there enough feasible edge types (Apply edge matcher) 
|||                         Binary predicate Pij(u,v)
|||   - Degree matching:    Do the degrees of Vi must be feasible for ispmprphism
|||                           Subgraph deg(Vi) <= deg(Vj)
|||                           Graph    deg(Vi)  = deg(Vj)
|||                         The degrees of the adjacent vertices Vk of Vi
|||                         are also matched to further refine the matrix
|||                   TODO: Sorted lists of the adjacency lists by degrees can
|||                         be used to improve performance of the coparison
||| Refer to Ullmann [2010]
prematch : Settings -> CompatibilityMatrix rows cols 
         -> CompatibilityMatrix rows cols
-- TODO: At-Hoeck
--       Should the prematched compatibility matrix type be changed?
--       This would enforce the use of properly prepared conmpatibility
--       matrices. Altough this is not really necessary for the backtrackSearch
--       as it will just not find a match if the CompatibilityMatrix is
--       already invalid

-- Search procedure  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .   
-- TODO: Depends on choose procedure ...
||| Backtrack search algorithm (depth-first)
||| Uses a 
backtrackSearch : Settings -> CompatibilityMatrix rs cs 
                -> (n ** Vect n (CompatibilityMatrix rs cs))
-- Recursion over rows of CM
--  1. Elective instantiation (v (of Vj)) (choose method)
--  2. Domain reduction
--   if consistent then
--       if terminal (depth = rs && valid CM (TODO: Validation wrapper type?)) -> add CM to result
--       else eval next row
--   if any row no 1 -> empty domain -> Backtrack (depth = 1 -> terminate)
--
--        
-- TODO: How to store available domain values (read them from vector?
--       Or should we keep a separate list where we can read them directly
--       allowing us to maintain short lists -> less lookup time


-- Elective instantiation  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .
-- TODO: Input missing -> which values possible
--       Output refinement -> provide proof of valid value
--
-- Options:
--     - Binary branching
--     - dom/wdeg
choose : Settings -> Maybe Nat
-- TODO: Return type should baybe be an own type to represent:
--         - Terminal to check in the search
--         - Just the value to instantiate
-- As described in Ullmann 2010
-- 1. If all domains are single valued -> return & eval terminal
-- 2. Loop over multivalued variables & instantiate next variable
--        If dom/wdeg -> score computations & selection (Lecoutre)
--        otherwise just take this one
--3. eval terminal



-- Dimensionality reduction . .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .

-- TODO: This section needs proper types. However, the representation or
--       handling of domains must first be specified. I did not think about
--       that enough yet.


||| Removal of value u as soon as it becomes unsupported.
|||    Mij[u] * Dj = 0
||| Mij : Predicate result matrix
||| Mij[u] : Row corresponding to Vi = Di
||| u   : Value of domain Di
||| Di  : Domain of variable Vi
|||
||| TODO: This is an incomplete part of the mathematical concept present
|||       in Ullmann and not exactly how it would be represented
|||       here. Note: Needs further work to properly understand it.
|||
||| TODO: I do not understand the Domains correctly. I thought the values
|||       still available in the compatibility matrix woul correspond to the
|||       values still present in the domain Di. But what is Dj then? I guess
|||       those are the values Vi that werent assigned to anything yet so
|||       it corresponds to a column in the compatibility matrix.
|||
||| Ullmann [2010]
directReduction : Int


||| Accumulation of supported values (B) with
||| subsequent assignment to Di
|||
cumulativeReduction : Int


||| "Curtailed" reduction: Only reduces a domain at most once
||| per TODO (iteration? what exactly)
||| Has more elective instantiations and less domain reductions.
forwardChecking : Int



-- Algorithm invocation -------------------------------------------------------

ullmannImp : {s : Settings} -> (n ** Vect n (CompatibilityMatrix rs cs))
-- 1. init CM
-- 2. prematch
-- 3. search procedure



public export
-- TODO: Output types:
--         - Bool (is isomorphism -> terminate as soon as a match is found)
--         - Vect n (Compatibility Map) (which mappings are isomorphic)
--         - Nat (how many isomorphisms)
--         - ?
--        => add other accessor functions
ullmann :  Query qes qvs
        -> Target tes tvs
        -> Match qes tes
        -> Match qvs tvs
        -> Bool
ullmann q t me mv = ?outputCalc $ ullmannImp {s = MkSettings q t me mv}




