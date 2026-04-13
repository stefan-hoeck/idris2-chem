module Geom.Interpolate

import Geom
import Data.Fin

%default total

export
round : Nat -> Double -> Double
round n d =
 let f := pow 10 (cast n)
     dd := f*d
     df := floor dd
     dc := ceiling dd
  in if dd - df < dc - dd then df/f else dc/f

export
Interpolation Angle where
  interpolate a = "\{show $ round 1 $ toDegree a}°"

export
Interpolation Double where
  interpolate = show . round 3

export
Interpolation (Point t) where
  interpolate (P x y) = "x: \{x}, y: \{y}"

export
Interpolation (Vector t) where
  interpolate (V x y) = "vx: \{x}, vy: \{y}"

export
Interpolation (Fin k) where
  interpolate = show

export
Interpolation (List $ Fin k) where
  interpolate = show

export
Interpolation Bounds where
  interpolate = maybe "[]" (\p => "[\{fst p}, \{snd p}]") . getBounds

export
Interpolation (Bounds2D t) where
  interpolate (BS x y) = "x: \{x}, y: \{y}"
