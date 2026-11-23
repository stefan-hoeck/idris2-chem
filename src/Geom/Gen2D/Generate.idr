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

parameters {0 e, n  : Type}
           {auto dg : DebugFlag}
           {auto ce : Cast n Elem}
           {auto ch : Cast n Hybridization}
           {g  : Graph e n}
           (sg : Subgraph g)

  pchain : PlaceST s g => AttachPoint g -> Nodes g -> F1' s
  pchain _            []      = pure () -- will not happen
  pchain None         (x::xs) = place x origin >> placeChain g x xs VECT_INI
  pchain (Attach p _) (x::xs) = bondVector p x >>= placeChain g p (x::xs)

  placeComp : PlaceST s g => Component g -> F1' s
  placeComp (C a ns False _)  = pchain a ns >> for1_ ns (ignore1 . placeNeighbours g)
  placeComp (C a ns True  sg) = placeRing g a ns sg

  coords : Graph e (MolPoint, Node g)
  coords =
    run1 $ T1.do
      st <- placeST g
      for1_ (components g) placeComp
      ps <- getPoints st
      pure $ map (\x => (ps `atN` x, x)) sg

0 CGraph : (g : Graph e n) -> Type
CGraph g = Graph e (MolPoint,Node g)

coordArray : {g : Graph e n} -> List (CGraph g) -> IArray g.order MolPoint
coordArray gs =
  alloc g.order origin $ \m => T1.do
    for1_ (gs >>= \h => labels h) $ \(p,x) => set m x.node p
    unsafeFreeze m

adjust : (g : Graph e n) -> List (CGraph g) -> Graph e (MolPoint,n)
adjust g gs =
 let cs := coordArray gs
  in mapWithCtxt g (\x => (at cs x,) . label)

Cast n e => Cast (a,n) e where cast = cast . snd

ModPoint (MolPoint,a) where
  mtrans = Mol
  modPoint f (p,v) = (modPoint f p, v)

GetPoint (MolPoint,a) where
  gtrans = Mol
  point = fst

export
coordinates :
     {0 e, n  : Type}
  -> {auto dg : DebugFlag}
  -> {auto ce : Cast n Elem}
  -> {auto ch : Cast n Hybridization}
  -> (g : Graph e n)
  -> Graph e (MolPoint, n)
coordinates g =
     connectedComponents g  -- split into components
  |> map (\y => coords y)   -- place them individually
  |> align                  -- align them in a grid
  |> (\x => adjust g x)     -- write coords to original graph
