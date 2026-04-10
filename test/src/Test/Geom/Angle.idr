module Test.Geom.Angle

import Debug.Trace
import Data.List.Quantifiers
import Geom
import Hedgehog
import Test.Geom.Similarity

%default total

len : Gen Double
len = double $ exponentialDouble 0.0 1.0e3

arcLen : Gen Double
arcLen = double $ exponentialDouble 1.0 1.0e3

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

prop_arcSame : Property
prop_arcSame =
  property $ Prelude.do
    [n@(S (S (S k))),l] <- forAll $ hlist [corners,len] | _ => pure ()
    let e := E 0.0001
        a := fullSteps n
    arc (S k) l l =~= MkArc (negate a) a (ngonRadius l n) (ngonDistance l n)

prop_arc : Property
prop_arc =
  property1 $ Prelude.do
    let e := E 0.0001
    arc 1 1 1.5 =~= MkArc (angle 2.89093699) (angle 1.4454684) 0.7559289 0.09449112

walk : Double -> (n : Nat) -> (0 p : IsSucc n) => Point Id
walk d n =
 let MkArc t phi r dc := arc n (d/1.5) d
     c                := if t < pi then P (negate dc) (d/2) else P dc (d/2)
  in go (S n) phi c (origin - c)
  where
    go : Nat -> Angle -> Point Id -> Vector Id -> Point Id
    go 0     phi c v = translate v c
    go (S k) phi c v = go k phi c (rotate phi v)

prop_arcDist : Property
prop_arcDist =
  property $ Prelude.do
    [(S (S (S k))),d] <- forAll $ hlist [corners,arcLen] | _ => pure ()
    let e := E 0.0001
        a := arc (S k) (d/1.5) d
    a.radius =~= distance (origin {t = Id}) (P a.distance (d/2))

prop_arcLen : Property
prop_arcLen =
  property $ Prelude.do
    [(S (S (S k))),d] <- forAll $ hlist [corners,arcLen] | _ => pure ()
    let e := E 0.0001
        a := arc (S k) (d/1.5) d
    (d/1.5) =~= (2*a.radius * sin (a.step.value/2))

prop_arcWalk : Property
prop_arcWalk =
  property $ Prelude.do
    let e := E 0.0001
    [n@(S (S (S k))),d] <- forAll $ hlist [corners,arcLen] | _ => pure ()
    walk d (S k) =~= P 0 d


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
    , ("prop_arcSame", prop_arcSame)
    , ("prop_arc", prop_arc)
    , ("prop_arcDist", prop_arcDist)
    , ("prop_arcLen", prop_arcLen)
    , ("prop_arcWalk", prop_arcWalk)
    ]
