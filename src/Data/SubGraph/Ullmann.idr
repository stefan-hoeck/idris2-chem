module Data.SubGraph.Ullmann

import Data.AssocList
import Data.Graph
import Data.List
import Data.Vect

%default total

-- Types ----------------------------------------------------------------------

public export
record Task (n : Nat)  (qe,qv,te,tv : Type)  where
  constructor MkTask
  edgeMatcher   : qe -> te -> Bool
  vertexMatcher : qv -> tv -> Bool
  query         : Vect n (Context qe qv)
  target        : Graph te tv


record Row qe qv te tv where
  constructor MkRow
  ctxt : Context qe qv        -- Query verticex
  trgs : List (Context te tv) -- Target vertices that can match to the query vertex
  0 prf : NonEmpty trgs


0 Matrix : (n : Nat) -> (qe,qv,te,tv : Type) -> Type
Matrix n qe qv te tv = Vect n (Row qe qv te tv)


-- Construct the matrix -------------------------------------------------------

||| Construction of Row with possibility of failure
||| O(1)
makeRow : Context qe qv -> List (Context te tv) -> Maybe (Row qe qv te tv)
makeRow q []          = Nothing
makeRow q ts@(_ :: _) = pure $ MkRow q ts IsNonEmpty


||| Matches vertice labels & the type and number of the required edges
||| O(n * m)     n: Length of the adjacency list of the query context
|||              m: Length of the adjacency list of the target context
match : Task n qe qv te tv -> Context qe qv -> Context te tv -> Bool
match ta q t =
  let vm = (vertexMatcher ta) (label q) (label t)
      em = isNil $ deleteFirstsBy (flip $ edgeMatcher ta)
           (values $ neighbours q) (values $ neighbours t)
  in vm && em


||| Build initial mapping with all possible mapping targets
||| O(n * m)     n: Length of query context list
|||              m: Size of target graph
||| O(match) assumed constant by an average node degree
init : Task n qe qv te tv -> Maybe (Matrix n qe qv te tv)
init ta = let trgs     = contexts $ target ta
         in traverse (\q => makeRow q $ filter (match ta q) trgs) (query ta)

-- Domain Reduction -----------------------------------------------------------

||| Enforces two things.
||| 1. For rows which are not adjaent to the one with the set target value.
|||    Removes the set target value if present in the possible
|||    mapping targets (ts).
|||
||| 2. For rows which are  adjaent to the one with the set target value.
|||    Filters the possible mapping targets (ts) for values which are:
|||      I.  Adjacent to the set target (tn).
|||      II. Have a matching bond to the set target (tn).
|||
||| O(n * m)    n,m: Number of rows & average number of columns
reduce :  (qe -> te -> Bool)
       -> Context qe qv
       -> Context te tv
       -> Matrix n qe qv te tv
       -> Maybe (Matrix n qe qv te tv)
reduce em (MkContext _ _ qns) (MkContext tn _ tns) = traverse red
  where red : Row qe qv te tv -> Maybe (Row qe qv te tv)
        red (MkRow c ts _) = case lookup c.node qns of
          -- Non adjacent: Remove initialzed node
          Nothing  => makeRow c $ filter ((tn /=) . node) ts
          -- Adjacent: Retains only edges with correct label and adjacent to current target tn
          Just bnd => makeRow c $ filter (\t => maybe False (em bnd) $ lookup t.node tns) ts


-- Ullmann core procedure -----------------------------------------------------

||| Selects a value to instantiate
||| O(n^3) best case without backtracking
||| O(n! * n^2) otherwise
select :  Task n qe qv te tv
       -> Context qe qv
       -> List (Context te tv)
       -> Matrix m qe qv te tv
       -> Maybe (Vect (S m) (Node, Node))

||| Progresses to select a value for the next query vertex or row
||| O(n^3) best case without backtracking
||| O(n! * n^2) otherwise
step :  Task n qe qv te tv
     -> Matrix k qe qv te tv
     -> Maybe (Vect k (Node, Node))

select _  _ []        _ = Nothing
select ta q (t :: ts) m =
  let Just m1 := reduce (edgeMatcher ta) q t m | Nothing => select ta q ts m
      Just m2 := step ta m1                    | Nothing => select ta q ts m
  in  Just $ (node q, node t) :: m2

step _ [] = Just []
step ta (r :: rs) = select ta (ctxt r) (trgs r) rs


-- Accessor function ----------------------------------------------------------

||| Isomorphism search
||| O(n^3) best case without backtracking
||| O(n! * n^2) otherwise
export
ullmann : Task n qe qv te tv -> Maybe (Vect n (Node,Node))
ullmann ta = init ta >>= step ta

||| Alternative accessor function
export
ullmann' : (qe -> te -> Bool) -> (qv -> tv -> Bool)
        -> (q : Graph qe qv) -> Graph te tv
        -> Maybe (Vect (length $ contexts q) (Node,Node))
ullmann' em vm q t = ullmann $ MkTask em vm (fromList $ contexts q) t
