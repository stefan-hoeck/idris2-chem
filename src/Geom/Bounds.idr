module Geom.Bounds

import Geom.Point
import Geom.Vector
import Text.Molfile.Types

%default total

||| Bounds along one axis in an affine space
export
data Bounds : Type where
  ||| Bounds without extent. Contains no points.
  Empty    : Bounds

  ||| Concrete bounds.
  Rng      : (min, max : Double) -> Bounds

||| The empty bounds.
export %inline
empty : Bounds
empty = Empty

||| A single point on an axis.
export
val : Double -> Bounds
val v = Rng v v

||| the range between two points on a line
export
range : (min,max : Double) -> Bounds
range l u = if l <= u then Rng l u else Empty

||| Return the smallest `Bounds` containing all points in both
||| argument bounds.
export
expand : Bounds -> Bounds -> Bounds
expand (Rng mi1 ma1) (Rng mi2 ma2) = Rng (min mi1 mi2) (max ma1 ma2)
expand Empty         v             = v
expand v             Empty         = v

||| Checks if a value is within the given bounds.
export
inBounds1D : {default 0.0 margin : Double} -> Double -> Bounds -> Bool
inBounds1D x (Rng min max) = (min - margin) <= x && x <= (max + margin)
inBounds1D x Empty         = False

||| Computes the middle (center) of a range. Returns `Nothing` if the `Bounds`
||| are empty.
export
middle : Bounds -> Maybe Double
middle (Rng min max) = Just $ (max + min) / 2
middle Empty         = Nothing

||| Computes the width of some bounds. Returns `0` if the `Bounds` are empty
export
width : Bounds -> Double
width (Rng min max) = max - min
width Empty         = 0.0

||| Computes half of the width of some bounds.
||| Returns `0` if the `Bounds` are empty
export
halfWidth : Bounds -> Double
halfWidth bs = width bs / 2.0

export %inline
Semigroup Bounds where (<+>) = expand

export %inline
Monoid Bounds where neutral = Empty

||| Compounds the overlapping region between two bounds in
||| one direction.
export
overlap : {default 0.0 margin : Double} -> Bounds -> Bounds -> Bounds
overlap (Rng mi1 ma1) (Rng mi2 ma2) =
  range (max mi1 mi2 - margin) (min ma1 ma2 + margin)
overlap _             _             = Empty

--------------------------------------------------------------------------------
--          Bounds 2D
--------------------------------------------------------------------------------

||| Bounds in two dimensions.
public export
record Bounds2D (t : AffineTransformation) where
  constructor BS
  x : Bounds
  y : Bounds

export
Semigroup (Bounds2D t) where
  BS x1 y1 <+> BS x2 y2 = BS (x1 <+> x2) (y1 <+> y2)

export
Monoid (Bounds2D t) where neutral = BS empty empty

namespace Bounds2D
  export
  width : Bounds2D t -> Double
  width = width . x

  export
  height : Bounds2D t -> Double
  height = width . y

  ||| Computes the overlapping rectangle between 2D bounds.
  export
  overlap : {default 0.0 margin : Double} -> Bounds2D t -> Bounds2D t -> Bounds2D t
  overlap (BS x1 y1) (BS x2 y2) = BS (overlap {margin} x1 x2) (overlap {margin} y1 y2)

||| Checks, if the point is in within some bounds in its affine space
||| by two points.
export
inBounds : {default 0.0 margin : Double} -> (p : Point t) -> Bounds2D t -> Bool
inBounds p (BS x y) = inBounds1D {margin} p.x x && inBounds1D {margin} p.y y

||| Return the corners of a bounding rectangle (if any)
export
corners : Bounds2D t -> Maybe (Point t, Point t)
corners (BS (Rng xmin xmax) (Rng ymin ymax)) = Just (P xmin ymin, P xmax ymax)
corners _                                    = Nothing

--------------------------------------------------------------------------------
--          Bounded
--------------------------------------------------------------------------------

public export
interface Bounded (0 a : Type) where
  constructor BD
  btrans : AffineTransformation
  bounds : a -> Bounds2D btrans

public export %inline
{t : _} -> Bounded (Bounds2D t) where
  btrans = t
  bounds = id

public export
Foldable f => (b : Bounded a) => Bounded (f a) where
  btrans = btrans @{b}
  bounds = foldMap bounds

public export %inline
(g : GetPoint a) => Bounded a where
  btrans   = gtrans @{g}
  bounds v = let P x y := point v in BS (val x) (val y)

export
convertBounds : {s,t : _} -> Bounds2D s -> Bounds2D t
convertBounds bs =
  case corners bs of
    Just (x,y) => bounds (convert {s,t} x) <+> bounds (convert {s,t} y)
    Nothing    => neutral

||| Calculates the center in a collection of bounded values.
|||
||| Returns the origin in case of an object with empty bounds.
export
center : (b : Bounded a) => a -> Point (btrans @{b})
center ts = case bounds ts of
  BS x y => fromMaybe origin [| P (middle x) (middle y) |]

||| Checks, if the point is in or on the line of a rectangel defined
||| by two points.
export
inRectangle : {t : _} -> (p, edge1, edge2 : Point t) -> Bool
inRectangle p e1 e2 = inBounds p (bounds $ the (List _) [e1,e2])

||| Translates a bounded value so that the lower-left corner of its
||| bound will come to lie at the origin.
export
translatePositive : ModPoint a => Bounded a => a -> a
translatePositive v =
  case corners $ bounds v of
    Nothing         => v
    Just (P x y, _) => translate (V (-x) (-y)) v

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

||| Computes the distance of a point `p` from the line segment
||| between points `pl1` and `pl2`.
export
distanceToLineSegment : {t : _} -> (p, pl1, pl2 : Point t) -> Double
distanceToLineSegment p pl1 pl2 =
  let pp   := perpendicularPoint p (translate (pl1 - pl2) p) 1 True
      dflt := min (distance p pl1) (distance p pl2)
   in case intersect pl1 pl2 p pp of
        Just i  => if inRectangle i pl1 pl2 then distance p i else dflt
        Nothing => dflt
