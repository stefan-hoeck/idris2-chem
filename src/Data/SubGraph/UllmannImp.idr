module Data.SubGraph.UllmannImp


import Data.Graph
import Data.Vect

%default total


-- TODO:
-- NOTE:
-- The current version of the implementation is heavily dependent on
-- prematch. 'prematch' validates the vertex invariance (vertexMatcher),
-- the binary constraints (edgeMatcher, all necessary bonds present
-- (type and number)). Other implementations are not necessarily performing
-- such an extensive prematching (require edge matching in the search algorithm).
-- The search algorithms only goal, is to find a mapping which corresponds to an
-- isomorphism. In this version the feasibility of (Vi's value u -> Vj's value v)
-- should have already been verified.

-- TODO: Handle Partial

-- Data types and their functins ----------------------------------------------


-- Describes wether the Mapping represents an isomorphism (m : Vi -> Vj).
-- An intermediate mapping (multiple ones per row / column)
-- or if an isomorphism is impossible (has an empty domain Di)
data MappingHealth = SubGraphIsomorphism
                   | EmptyDomain
                   | Intermediate



||| The query is the subgraph to be searched in the
||| Target.
Query : (qEdge : Type) -> (qVertex : Type) -> Type
Query e v = Graph e v

||| Molecule matched against the query.
Target : (tEdge : Type) -> (tVertex : Type) -> Type
Target e v = Graph e v

Match : Type -> Type -> Type
Match a b = a -> b -> Bool 

record Settings where
  constructor MkSettings
  query         : Query qe qv
  target        : Target te tv
  edgeMatcher   : Match qe te
  vertexMatcher : Match qv tv


-- Mapping of the query to the target

Key : Type -- Val and key actually the same underlying type
Val : Type -- as they both represent vertice indices

Mapping : Type -- Key (Vi) -> row, Val (Vj) -> column indices

-- Retreive all atom indices/keys from the query and target graphs
getQueryAtomKeys : Settings -> List Key
getTargetAtomKeys : Settings -> List Val

-- Build mapping Vi (query) -> Vj (target) vertices
-- only determines size (values -> ones)
initMapping : Settings -> Mapping

-- Represents the values that are a feasible
-- mapping target vertex Vj for query vertey Vi
Domain : Type
Domain = List Val  -- I would like to represent domain size somehow (likely Sigma type or vector)

-- Retreive the domain from a row in the mapping
getDomain : (row : Key) -> Mapping -> Domain



-- Representing checked matrices
data Prematched a = MkPrematched a



-- Algorithm utility functions ------------------------------------------------

-- Prematching

-- Functions for eliminating obvious mismatches pre-search
-- (apply to relevant values in the mapping)
vertexAttributeMatch : Settings -> Mapping -> Mapping -- vertex invariance

edgeMatch : Settings -> Mapping -> Mapping   -- enough edges of required attribute (acc. to edgeMatcher)
  -- Multiple steps possible for (maybe) reducing computations (degree, types, number of types)

prematch : Settings -> Mapping -> Prematched Mapping
prematch s = MkPrematched . edgeMatch s . vertexAttributeMatch s
--                              |                 |-> checks every value in mapping
--                              |-> checks only remaining 1s

-- Search algorithm

-- Extracts a value from a domain which will be instantiated next.
-- Currently it just works as in the case of simple enumeration.
--
-- Needs to make sure that every item in the dimension is only selected once
-- (thus the whole domain is passed and the remainder returned)
-- Takes the values of dimension Di and returns one of them with the remaining list
-- Different implementations depending on the method used
--
-- TODO: The type for handling empty domains is not very useful
electiveInst : Domain -> Maybe (Val, Domain)
electiveInst []        = Nothing
electiveInst (x :: xs) = Just (x, xs)


-- Currently, removes the just instantiated value v (of Vj) from the 
-- domains of all subsequent mappings (rows) (changes the ones in col to 0)
-- col corresponds to the value v of Vj (column index of the mapping)
domainReduction : (col : Val) -> (rows : List Key) -> Mapping -> Mapping
domainReduction _ []        m = m
domainReduction v (r :: rs) m = domainReduction v rs (removeKey v r m)
  where removeKey : (col : Val) -> (row : Key) -> Mapping -> Mapping



isIsomorphism : Mapping -> MappingHealth
-- Only considers the Mapping matrix for evaluation
-- One per row & 0-1 per col -> SubIsomorph
-- Row none                  -> EmptyDomain
-- Row or col more than one  -> Intermediate


-- Search algorithm

-- initRow to initialize new rows
-- rowSearch to continue with next domain value
--           or next row depending on matching result
partial
rowSearch : (rows : List Key) -> Domain -> Mapping -> Maybe Mapping

partial
initRow : (rows : List Key) -> Mapping -> Maybe Mapping
initRow []        _ = Nothing
initRow (r :: rs) m = rowSearch (r :: rs) (getDomain r m) m

-- TODO: What is this? (see error when replacing with (=<<) in rowSearch)
--       Gotta investigate later
-- https://github.com/idris-lang/Idris2/issues/65
typeScrutinee : (Mapping -> Maybe Mapping) -> Maybe Mapping -> Maybe Mapping
typeScrutinee  = (=<<)


rowSearch Nil _ _ = Nothing
rowSearch (r :: rs) dom m = do
  (vj, domRem) <- electiveInst dom
  mReduced     <- pure $ domainReduction vj rs m
  healthRM     <- pure $ isIsomorphism mReduced
  case healthRM of
       Intermediate        => initRow rs m
       EmptyDomain         => rowSearch (r :: rs) domRem m 
       SubGraphIsomorphism => Just mReduced
 
-- Test and evaluate a row
partial
backtrackSearch : Settings -> Prematched Mapping -> Maybe Mapping
backtrackSearch s (MkPrematched m) = case isIsomorphism m of
        SubGraphIsomorphism => Just m
        EmptyDomain         => Nothing
        Intermediate        => initRow (getQueryAtomKeys s) m



-- Accessor function ----------------------------------------------------------
partial
ullmannImp : {s : Settings} -> Maybe Mapping
ullmannImp = backtrackSearch s $ prematch s $ initMapping s

