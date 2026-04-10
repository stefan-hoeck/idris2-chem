module Test.Geom.Bounds

import Derive.Prelude
import Data.Refined
import Geom
import Hedgehog
import Test.Geom.Similarity

%default total
%language ElabReflection

dim : Gen Double
dim = double $ exponentialDouble 5 1.0e3

coord : Gen Double
coord = double $ exponentialDoubleFrom 0 (-1.0e3) 1.0e3

record Pack where
  constructor P
  x : Double
  y : Double
  w : Double
  h : Double

%runElab derive "Pack" [Show,Eq]

export
Similar Pack where
  isSimilar (P x1 y1 w1 h1) (P x2 y2 w2 h2) =
    isSimilar x1 x2 &&
    isSimilar y1 y2 &&
    isSimilar w1 w2 &&
    isSimilar h1 h2

ModPoint Pack where
  mtrans = Id
  modPoint f p = let P nx ny := f (P p.x p.y) in {x := nx, y := ny} p

Bounded Pack where
  btrans = Id
  bounds p = BS (range p.x (p.x + p.w)) (range p.y (p.y + p.h))

packs : Gen Pack
packs = [| P coord coord dim dim |]

squares : Gen Pack
squares = [| square coord coord dim |]
  where
    square : (x,y,l : Double) -> Pack
    square x y l = P x y l l

prop_pack1 : Property
prop_pack1 =
  property $ Prelude.do
    let e := E 0.00001
    p <- forAll packs
    align [p] =~= [p]

prop_pack2 : Property
prop_pack2 =
  property $ Prelude.do
    let e := E 0.00001
    p <- forAll squares
    align [p,p] =~= [{x := 0, y := 0} p, {x := p.w + 5, y := 0} p]

export
props : Group
props =
  MkGroup "Geom.Bounds"
    [ ("prop_pack1", prop_pack1)
    , ("prop_pack2", prop_pack2)
    ]

