module Data.SubGraph.CompatibilityMatrix


import Data.Vect
import Control.Monad.State

%default total

-------------------------------------------------------------------------------
-- TODO: Description of functionaliy / concept of 
--       how this works ('full support' principle)
-------------------------------------------------------------------------------






-- Matrix to store wether the mapping of two atoms
-- (row -> query atom of given index, column -> target ...)
-- TODO: For optimization use bit vectors
||| Matrix representing the mapping of a query to a target.
||| Rows represent Vi (query vertices)
||| Columns represent Vj (target vertices)
|||
||| The ones in a row represent the possible mappings of
||| L : Vi -> Vj
||| thus represents the domain cardinality
||| TODO: Statement about domain cardinality correct?
public export
record CompatibilityMatrix (rows : Nat) (cols : Nat) where
  constructor MkCM
  value : Vect rows (Vect cols Bool)

-- Building a compatibility matrix of a specific size
-- with ones (1) values
export
init : (rows : Nat) -> (cols : Nat) 
     -> CompatibilityMatrix rows cols


export
get : (row : Fin rows) -> (col : Fin cols)
    -> CompatibilityMatrix rows cols -> Bool

-- Set a value at a certain index to 
export
set : (row : Fin rows) -> (col : Fin cols) -> Bool
    -> CompatibilityMatrix rows cols -> CompatibilityMatrix rows cols




