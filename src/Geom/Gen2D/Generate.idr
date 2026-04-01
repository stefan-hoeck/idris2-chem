module Geom.Gen2D.Generate

import Geom.Gen2D.Rings
import Geom.Gen2D.State
import Geom.Gen2D.Place
import Geom.Gen2D.Types

%default total

VECT_INI : MolVector
VECT_INI = rotate (fromDegree 30) (V BOND_LEN 0)

parameters {k : _}
           {0 e, n  : Type}
           {auto ce : Cast n Elem}
           {auto ch : Cast n Hybridization}
           (g : IGraph k e n)

  pchain : PlaceST s k => AttachPoint k -> List (Fin k) -> F1' s
  pchain _            []      = pure () -- will not happen
  pchain None         (x::xs) = place x origin >> placeChain g x xs VECT_INI
  pchain (Attach p _) (x::xs) = bondVector p x >>= placeChain g p (x::xs)

  placeComp : PlaceST s k => Component k e n -> F1' s
  placeComp (C a ns False _)  = pchain a ns >> for1_ ns (ignore1 . placeNeighbours g)
  placeComp (C a ns True  sg) = placeRing g a ns sg

  export
  coordinates : IGraph k e (MolPoint, n)
  coordinates =
    run1 $ T1.do
      st <- placeST k
      for1_ (components g) placeComp
      ps <- getPoints st
      pure $ {graph $= mapWithIndex $ \x => map (ps `at` x,)} g
