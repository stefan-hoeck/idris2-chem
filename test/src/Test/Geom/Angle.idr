module Test.Geom.Angle

import Geom
import Hedgehog

%default total

prop_enclosingAngles : Property
prop_enclosingAngles =
  property1 $ Prelude.do
    enclosingAngles (fromDegree 30) (map fromDegree [100,60,45,10,270]) ===
      Just (fromDegree 10, fromDegree 45)
    enclosingAngles (fromDegree 30) (map fromDegree [100,60,45,270]) ===
      Just (fromDegree 270, fromDegree 45)

export
props : Group
props =
  MkGroup "Geom.Angle"
    [ ("prop_enclosingAngles", prop_enclosingAngles)
    ]
