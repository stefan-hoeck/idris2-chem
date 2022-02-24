module Data.SubGraph.CompatibilityMatrix


import Data.Vect
import Control.Monad.State

%default total

-- Notes:
-- This implementation is influenced by CDK's Ullmann algorithm's 
-- use of the CompatibilityMatrix (base/isomorphism/.../CompatibilityMatrix.java


record CompatibilityMatrix where
  constructor MkCM
  value : List Int
  rows  : Int
  cols  : Int

f : State CompatibilityMatrix Int

g : Vect 3 Int
