module Test.Geom.Vector

import Data.List.Quantifiers
import Data.Refined
import Geom
import Hedgehog
import Test.Geom.Similarity

%default total

dbl : Gen Double
dbl = double $ exponentialDoubleFrom 0.0 (-1.0e3) 1.0e3

vid : Gen (Vector Id)
vid = [| V dbl dbl |]

prop_dotSelf : Property
prop_dotSelf =
  property $ do
    v <- forAll vid
    dot v v =~= pow (length v) 2

prop_dotPerpendicular : Property
prop_dotPerpendicular =
  property $ do
    v <- forAll vid
    dot v (perpendicular v) =~= 0.0

prop_dotAnyPerpendicular : Property
prop_dotAnyPerpendicular =
  property $ do
    [v,s] <- forAll $ hlist [vid,dbl]
    dot v (scale s $ perpendicular v) =~= 0.0

export
props : Group
props =
  MkGroup "Geom.Vector"
    [("prop_dotSelf", prop_dotSelf)
    ,("prop_dotPerpendicular", prop_dotPerpendicular)
    ,("prop_dotAnyPerpendicular", prop_dotAnyPerpendicular)
    ]
