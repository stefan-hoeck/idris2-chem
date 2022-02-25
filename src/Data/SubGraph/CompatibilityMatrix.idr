module Data.SubGraph.CompatibilityMatrix


import Data.Vect
import Control.Monad.State

%default total

-------------------------------------------------------------------------------
-- Notes:
-- This implementation is influenced by CDK's Ullmann algorithm's 
-- use of the CompatibilityMatrix (base/isomorphism/.../CompatibilityMatrix.java

-- TODO: Description of functionaliy / concept of 
--       how this works ('full support' principle)
-------------------------------------------------------------------------------



-- TODO:  Placeholder for Refined Int < 0 (& maximum depth of search tree?)
--
-- To be used as a marking of the compatibility matrix
-- usually equal to the negative of the row number.
--
-- The absolute number denotes the  
Marking : Type
Marking = Int



-- Matrix to store wether the mapping of two atoms
-- (row -> query atom of given index, column -> target ...)
-- TODO: Better container?
-- TODO: Refine int -> 0,1 & negative markings
record CompatibilityMatrix (rows : Nat) (cols : Nat) where
  constructor MkCM
  value : Vect (rows * cols) Int

-- Building a compatibility matrix of a specific size
-- with zero values
-- NW: The ullmann algorithm will then initialize the
--     values individually using the adjacency matrices
--     and the atom matcher
zero : (rows : Nat) -> (cols : Nat) 
     -> CompatibilityMatrix rows cols


-- Get a value from a specific index
-- TODO: Input proof oder Maybe
get : (row : Fin rows) -> (col : Fin cols)
    -> State (CompatibilityMatrix rows cols) Int

-- Set a value at a certain index to 1
-- TODO: If I tend to use state, should I use it everywhere?
set : (row : Fin rows) -> (col : Fin cols)
    -> State (CompatibilityMatrix rows cols) ()

-- Mark a certain index with a negative number
mark : (row : Fin rows) -> (col : Fin cols) -> Marking 
    -> State (CompatibilityMatrix rows cols) ()

-- mark a row with a negative number
markrow : (row : Fin rows) -> Marking 
    -> State (CompatibilityMatrix rows cols) ()

-- Reset all values of the given Mariking for all rows from 
-- 'row' to the end of the matrix.
-- TODO: The publication (need to look up which one again) states,
--       that the initial rows are fixed down to the one which
--       corresponds to the current atom (?) that is evaluated.
resetrows : (row : Fin rows) -> Marking 
    -> State (CompatibilityMatrix rows cols) ()



