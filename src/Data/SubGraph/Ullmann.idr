module Data.SubGraph.Ullmann

import Control.Monad.State
import Data.Graph
import Data.SubGraph.Comparison

%default total

-- Fundamental types ----------------------------------------------------------


-- TODO: There might be differences between the query and target.
--       The following might be adjusted:

||| The query is the subgraph to be searched in the
||| Target. -> Subgraph isomorphism
Query : (edge : Type) -> (vertex : Type) -> Type
Query e v = Graph e v

||| Molecule matched against the query. A target is
||| a molecule taken from the database.
Target : (edge : Type) -> (vertex : Type) -> Type
Target e v = Graph e v


-- TODO: Currently just a placeholder
CompatibilityMatrix : Type
CompatibilityMatrix = String


-- Functions to access substructure search ------------------------------------

||| Matches a query with its target and evaluates
||| whether there is a graph isomorphism with a
||| subgraph of the target.
match :  Matcher edges        -> Matcher vertices
      -> Query edges vertices -> Target edges vertices 
      -> Bool


-- Matches a list of targets and returns the matches
matchTargets : Foldable t => Matcher e -> Matcher v -> Query e v -> t (Target e v)
                          -> List (Target e v)
matchTargets em vm q l =  
  foldl (\acc, t => if match em vm q t then t :: acc else acc) [] l


-- Ullmann required data ------------------------------------------------------
record UllmannData edge vertex where
  constructor MkUllmannData
  query         : Query edge vertex
  vertexMatcher : Matcher vertex
  edgeMatcher   : Matcher edge


record UllmannStateData edge vertex where
  constructor MkUllmannStateData
  query               : Query edge vertex
  target              : Target edge vertex
  vertexMatcher       : Matcher vertex
  edgeMatcher         : Matcher edge
  compatibilityMatrix : CompatibilityMatrix







-- The following is a first draft

-- Mapping --------------------------------------------------------------------


-- ||| Mapping of a query to a target (vertice indices)
-- TODO: Not perfectly understood, need to check it again
Mapping : Type
Mapping = String -- Actually some kind of array or list

-- Further functions such as:
-- Limit
-- Filter
-- ,,,

-- They use streams, would lazyness be enough for limit?




-- State ----------------------------------------------------------------------

-- ||| Ullmann State
-- ||| Incorporates the backtrack algorithm with the lookup
-- ||| rules for the determination of matches
-- |||
-- |||
-- ||| Properties:
-- ||| - Container / Molecule: Query (Q) & Target (T)
-- ||| - Adj list:             Query & Target
-- ||| - Bond maps:            Query & Target
-- ||| - Compatibility matrix
-- ||| - Bond matcher
-- ||| - mapping size counter
-- |||
ullmannState : State (UllmannStateData e v) Mapping


-- Progression of the ullmann state:
-- 1. Initialize the compatibility matrix (CM) to size:
--    (query adj list len, target adj list len)
-- 2. Set the values in the CM to 1 if the atoms match (between Q & T)
--
-- 3. PENDING
--
--
--
--
--

-- ||| Query vertex -> target vertex -> Feasible
-- ||| Checks that for every adjacent vertex to n in the query,
-- ||| there is a feasible ajacent vertex to m in the target
-- |||
-- ||| Feasible is when CM match && bonds match
verifyEdges : (UllmannStateData e v) -> Int -> Int -> Bool

-- ||| Scan the CM for values > 0
-- ||| If value > 0 (false) then return true
hasCandidate : (UllmannStateData e v) -> Int -> Bool

-- CompatibilityMatrix functionality ------------------------------------------

-- TODO: Own namespace?

-- ||| Refines the mapping, if it becomes invalid
-- ||| Then it is reversed again
-- ||| See: cdk/base/isomorphism/.../UllmannState
add : Int -> Int -> CompatibilityMatrix -> CompatibilityMatrix

-- ||| Remove change an entry to unmapped and reset the row
remove : Int -> Int -> CompatibilityMatrix -> CompatibilityMatrix

-- ||| Refines from the row (Int) after the current (compatibility matrix)
-- ||| 1. Check each feasible mappig whether it's still valid
-- |||    If a mapping has been removed, then check whether there are
-- |||   any candidates left and update a flag
-- ||| Returns a flag whether it has candidates left
refine : Int -> CompatibilityMatrix -> (Bool, CompatibilityMatrix)


