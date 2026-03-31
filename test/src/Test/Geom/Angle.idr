module Test.Geom.Angle

import Data.List.Quantifiers
import Geom
import Hedgehog
import Test.Geom.Similarity

%default total

len : Gen Double
len = double $ exponentialDouble 0.0 1.0e3

corners : Gen Nat
corners = nat $ linear 3 100

prop_enclosingAngles : Property
prop_enclosingAngles =
  property1 $ Prelude.do
    enclosingAngles (fromDegree 30) (map fromDegree [100,60,45,10,270]) =~=
      Just (fromDegree 10, fromDegree 45)
    enclosingAngles (fromDegree 30) (map fromDegree [100,60,45,270]) =~=
      Just (fromDegree 270, fromDegree 45)

prop_ngonAngle : Property
prop_ngonAngle =
  property $ Prelude.do
    n@(S (S (S _))) <- forAll corners | _ => pure ()
    let nd := cast {to = Double} n
    ngonAngle n =~= angle ((nd-2) * pi / nd)

prop_ngonRadius : Property
prop_ngonRadius =
  property1 $ Prelude.do
  let e := E 0.0001
  ngonRadius 1 3 =~= 0.57735
  ngonRadius 1 4 =~= 0.707107
  ngonRadius 1 5 =~= 0.850651
  ngonRadius 1 6 =~= 1
  ngonRadius 1 10 =~= 1.61803

prop_ScaleNgonRadius : Property
prop_ScaleNgonRadius =
  property $ Prelude.do
    [n@(S (S (S _))),l] <- forAll $ hlist [corners,len] | _ => pure ()
    ngonRadius l n =~= l * ngonRadius 1 n


prop_ngonDistance : Property
prop_ngonDistance =
  property1 $ Prelude.do
  let e := E 0.0001
  ngonDistance 1 3 =~= 0.288675
  ngonDistance 1 4 =~= 0.5
  ngonDistance 1 5 =~= 0.688191
  ngonDistance 1 6 =~= 0.866025
  ngonDistance 1 10 =~= 1.53884

prop_ScaleNgonDistance : Property
prop_ScaleNgonDistance =
  property $ Prelude.do
    [n@(S (S (S _))),l] <- forAll $ hlist [corners,len] | _ => pure ()
    ngonDistance l n =~= l * ngonDistance 1 n

export
props : Group
props =
  MkGroup "Geom.Angle"
    [ ("prop_enclosingAngles", prop_enclosingAngles)
    , ("prop_ngonAngle", prop_ngonAngle)
    , ("prop_ngonRadius", prop_ngonRadius)
    , ("prop_ScaleNgonRadius", prop_ScaleNgonRadius)
    , ("prop_ngonDistance", prop_ngonDistance)
    , ("prop_ScaleNgonDistance", prop_ScaleNgonDistance)
    ]
