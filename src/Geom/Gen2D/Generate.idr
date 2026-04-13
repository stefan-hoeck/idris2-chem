module Geom.Gen2D.Generate

import Data.Graph.Indexed.Subgraph
import Data.Linear.Traverse1
import Syntax.T1

import Geom.Gen2D.Rings
import Geom.Gen2D.State
import Geom.Gen2D.Place
import Geom.Gen2D.Types

%default total

VECT_INI : MolVector
VECT_INI = rotate (fromDegree 30) (V BOND_LEN 0)

parameters {k : _}
           {0 e, n  : Type}
           {auto dg : DebugFlag}
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

  coords : IGraph k e (MolPoint, n)
  coords =
    run1 $ T1.do
      st <- placeST k
      for1_ (components g) placeComp
      ps <- getPoints st
      pure $ {graph $= mapWithIndex $ \x => map (ps `at` x,)} g

0 CGraph : Nat -> Type -> Type -> Type
CGraph k e n = Graph e (MolPoint,Fin k, n)

coordArray : {k : _} -> List (CGraph k e n) -> IArray k MolPoint
coordArray gs =
  alloc k origin $ \m => T1.do
    for1_ (gs >>= \(G _ h) => labels h) $ \(p,x,_) => set m x p
    unsafeFreeze m

adjust : {k : _} -> IGraph k e n -> List (CGraph k e n) -> IGraph k e (MolPoint,n)
adjust g gs =
 let cs := coordArray gs
  in mapWithCtxt (\x => (at cs x,) . label) g

Cast n e => Cast (a,n) e where cast = cast . snd

ModPoint (MolPoint,a) where
  mtrans = Mol
  modPoint f (p,v) = (modPoint f p, v)

GetPoint (MolPoint,a) where
  gtrans = Mol
  point = fst

export
coordinates :
     {k : _}
  -> {0 e, n  : Type}
  -> {auto dg : DebugFlag}
  -> {auto ce : Cast n Elem}
  -> {auto ch : Cast n Hybridization}
  -> (g : IGraph k e n)
  -> IGraph k e (MolPoint, n)
coordinates g =
     connectedComponents g            -- split into components
  |> map (\(G _ y) => G _ $ coords y) -- place them individually
  |> align                            -- align them in a grid
  |> adjust g                         -- write coords to original graph
