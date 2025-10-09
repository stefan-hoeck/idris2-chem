module Geom.Gen2D.OverlapScore

import Chem
import Data.SortedMap
import Geom
import Geom.Gen2D.Types

%inline
MARGIN : Double
MARGIN = -0.0001

-- Determines the weight if two atoms are overlapping.
-- Assuming that the bonds in the molecule have the standard length set in
-- the DrawSettings
weight : (s : Gen2DSettings) => (dist : Double) -> Double
weight dis =
 let d := dis - s.bondLength
  in if d < MARGIN then abs d / s.bondLength else 0.0

addSC : ScoreMap k -> (Fin k,Fin k,Double) -> ScoreMap k
addSC m (x,y,sc) = insertWith (+) x sc (insertWith (+) y sc m)

parameters {auto s   : Gen2DSettings}
           {auto cst : Cast n (Point Mol)}
           {k        : Nat}
           (g        : IGraph k e n)

  overlapPairs : List (Fin k, Fin k, Double)
  overlapPairs = do
    (x,px) <- map (cast @{cst}) <$> labNodes g
    (y,py) <- map (cast @{cst}) <$> labNodes g
    let score = weight $ distance px py
    guard (x < y && score > 0.0)
    pure (x, y, score)

  export
  toScore : OScore k
  toScore =
    let pairs := overlapPairs
        atomS := foldl addSC empty pairs
        tot   := sum $ map (\(_,_,s) => s) pairs
     in OS tot atomS pairs
