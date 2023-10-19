module Geom.Bounds

import Geom.Point
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
inBounds1D : Double -> Bounds -> Bool
inBounds1D x (Rng min max) = min <= x && x <= max
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

namespace Boudns2D
  export
  width : Bounds2D t -> Double
  width = width . x

  export
  height : Bounds2D t -> Double
  height = width . y

||| Checks, if the point is in within some bounds in its affine space
||| by two points.
export
inBounds : (p : Point t) -> Bounds2D t -> Bool
inBounds p (BS x y) = inBounds1D p.x x && inBounds1D p.y y

||| Return the corners of a bounding rectangle (if any)
export
corners : Bounds2D t -> Maybe (Point t, Point t)
corners (BS (Rng xmin xmax) (Rng ymin ymax)) = Just (P xmin ymin, P xmax ymax)
corners _                                    = Nothing

--------------------------------------------------------------------------------
--          Bounded
--------------------------------------------------------------------------------

public export
interface Bounded (0 a : Type) (0 t : AffineTransformation) | a where
  constructor BD
  bounds : a -> Bounds2D t

public export %inline
Foldable f => Bounded a t => Bounded (f a) t where
  bounds = foldMap bounds

export %inline
GetPoint a t => Bounded a t where
  bounds v = let P x y := point v in BS (val x) (val y)

||| Calculates the center in a collection of bounded values.
|||
||| Returns the origin in case of an object with empty bounds.
export
center : Bounded a t => a -> Point t
center ts = case bounds ts of
  BS x y => fromMaybe origin [| P (middle x) (middle y) |]

||| Checks, if the point is in or on the line of a rectangel defined
||| by two points.
export
inRectangle : (p, edge1, edge2 : Point t) -> Bool
inRectangle p e1 e2 = inBounds p (bounds $ the (List _) [e1,e2])
