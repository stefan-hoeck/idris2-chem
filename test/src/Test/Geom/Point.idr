module Test.Geom.Point

import Geom
import Hedgehog

%default total

prop_circularFreeSweep : Property
prop_circularFreeSweep =
  property1 $ Prelude.do
    circularFreeSweep {t = Id} 3 (P 0 0) [] === (zero, fromDegree 120)
    circularFreeSweep {t = Id} 3 (P 0 0) [P 0 1] === (fromDegree 90, fromDegree 90)
    circularFreeSweep {t = Id} 3 (P 0 0) [P 1 0, P 0 1]
      === (fromDegree 90, fromDegree 67.5)
    circularFreeSweep {t = Id} 3 (P 0 0) [P 1 1, P 1 2, P 2 0, P 0 1]
      === (fromDegree 90, fromDegree 67.5)
    circularFreeSweep {t = Id} 3 (P 0 0) [P 1 (-1), P 1 (-2), P 2 0, P 0 (-1)]
      === (fromDegree 0, fromDegree 67.5)
    circularFreeSweep {t = Id} 3 (P 0 0) [P (-1) (-1), P (-1) (-2), P (-2) 0, P 0 (-1)]
      === (fromDegree 270, fromDegree 67.5)

export
props : Group
props =
  MkGroup "Geom.Point"
    [("prop_circularFreeSweep", prop_circularFreeSweep)
    ]
