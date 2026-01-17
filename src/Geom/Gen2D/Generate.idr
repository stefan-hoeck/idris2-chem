module Geom.Gen2D.Generate

import Data.Array.Mutable
import Geom
import Geom.Gen2D.Types

%default total

-- parameters (g : IGraph k e n)
--            (m : MArray t k (Point Id))
--
--   chain : (this,next : Angle) -> Fin k -> List (Fin k) -> F1' t
--   chain this next c []        t = t # ()
--   chain this next c (x :: xs) t =
--    let p := get m

