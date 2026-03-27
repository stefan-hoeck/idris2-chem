module Geom.Gen2D.Generate

import Data.Linear.Traverse1
import Geom
import Geom.Gen2D.State
import Geom.Gen2D.Place
import Geom.Gen2D.Types
import Syntax.T1

%default total

VECT_INI : Vector Id
VECT_INI = rotate (fromDegree 30) (V 1 0)

parameters {k : _}
           {0 e, n  : Type}
           {auto ce : Cast n Elem}
           {auto ch : Cast n Hybridization}
           (g : IGraph k e n)

  pchain : PlaceST s k => AttachPoint k -> List (Fin k) -> F1' s
  pchain _            []      = pure () -- will not happen
  pchain None         (x::xs) = place x origin >> placeChain g x xs VECT_INI
  pchain (Attach p _) (x::xs) = bondVector p x >>= placeChain g p (x::xs)

  pring : PlaceST s k => AttachPoint k -> Subgraph k e n -> F1' s

  placeComp : PlaceST s k => Component k e n -> F1' s
  placeComp (C a ns False _)  = pchain a ns
  placeComp (C a ns True  sg) = pring a sg

  export
  coordinates : IGraph k e (Point Id, n)
  coordinates =
    run1 $ T1.do
      st <- placeST k
      for1_ (components g) $ \c =>
        placeComp c >> for1_ c.nodes (placeNeighbours g)
      ps <- getPoints st
      pure $ {graph $= mapWithIndex $ \x => map (ps `at` x,)} g
