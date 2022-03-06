module Data.SubGraph.Ullmann

-------------------------------------------------------------------------------
-- References
-- Ullmann [2010]: Bit-Vector Algorithms for Binary Constraint Satisfaction
--                 and Subgraph Isomorphism
--                 Julian R. Ullmann, King's College London, 2010


import Control.Monad.State
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


-- Search procedure  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .   
-- TODO: Depends on choose procedure too...
search : Int


-- Elective instantiation  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .
-- TODO: Input missing -> which values possible
--       Output refinement -> provide proof of valid value
--
--       chose can just take the next value or it can use something like
--       dom/wdeg (requires some tracking in the search algorithm) Lecoutre [200]
choose : Settings -> Nat


-- Dimensionality reduction . .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .
directReduction : Int
cumulativeReduction : Int
forwardChecking : Int





-- Algorithm invocation -------------------------------------------------------

ullmannImp : {s : Settings} -> Bool

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
ullmann q t me mv = ullmannImp {s = MkSettings q t me mv}




