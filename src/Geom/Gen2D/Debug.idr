module Geom.Gen2D.Debug

import Chem
import Data.String
import Geom.Gen2D.Types

%default total

||| Pretty prints a tree generated from a graph.
|||
||| Used mainly for debugging.
export
prettyTree : (a -> String) -> RTree k a -> String
prettyTree f = fastUnlines . goRT 0
  where
    goRT : Nat -> RTree k a -> List String

    trees : Nat -> Trees k a -> List String
    trees k []        = []
    trees k (x :: xs) = goRT k x ++ trees k xs

    rings : Nat -> Rings k a -> List String
    rings k []               = []
    rings k ((x,y,ys) :: xs) =
      indent k "Ring node \{show x}: \{f y}" :: trees (2*k) ys ++ rings k xs

    goRT k (Node x y xs) = indent k "Node \{show x}: \{f y}" :: trees (2+k) xs
    goRT k (Ring xs)     = indent k "Rings" :: rings (2+k) xs

