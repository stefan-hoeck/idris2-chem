module Geom.Point

import Data.Refined
import Geom.Angle
import Geom.Matrix
import Geom.Scale
import Geom.Vector
import Derive.Prelude

%language ElabReflection
%default total

--------------------------------------------------------------------------------
--          Affine Transformations
--------------------------------------------------------------------------------

||| An affine transformation is linear transformation (currently, a rotation
||| or scaling) followed by a translation in the new coordinate system.
|||
||| We use affine transformations to keep track of the coordinate system
||| we are currently in. In the UI, if a user zooms in or moves the canvas,
||| the coordinates we get from the UI must be adjusted by reversing these
||| transformations in order to get the correct canvas coordinates. These
||| need then again be adjusted (by a scaling factor) to get the coordinates
||| of the molecule.
|||
||| In order to make sure these transformations and adjustments are not
||| forgotten, we index all `Point`s we work with the the affine transformation
||| of the coordinate system they come from. Via function `convert`, points
||| from one coordinate system can be converted to the corresponding points in
||| another one.
public export
record AffineTransformation where
  constructor AT
  transform : LinearTransformation
  translate : Vector

||| The identity transformation
public export
Id : AffineTransformation
Id = AT Id vzero

||| An affine transformation consisting only of a scaling by the given factor.
export
scaling : Scale -> AffineTransformation
scaling sc = AT (scaling sc) vzero

export
Semigroup AffineTransformation where
  AT tl vl <+> AT tr vr =
    let vr2 := transform tl vr in AT (tl <+> tr) (vr2 + vl)

export
Monoid AffineTransformation where neutral = Id

||| Computes the inverse of an affine transformation so that
||| `t <+> inverse t` is the identity (`Id`; modulo rounding errors)
export
inverse : AffineTransformation -> AffineTransformation
inverse (AT tr v) = let i := inverse tr in  AT i $ negate (transform i v)

namespace Affine

  ||| Creates an affine transformation corresponding to a translation
  ||| by the given vector.
  export %inline
  translate : Vector -> AffineTransformation
  translate v = AT Id v

--------------------------------------------------------------------------------
--          Point
--------------------------------------------------------------------------------

||| A point in an affine space such as the user interface or the
||| coordinate system of the molecule.
|||
||| Unlike `Vector`, a `Point` is somewhat of an abstract entity.
||| We can compute a vector for connecting two points, but we cannot
||| add two points together (that does not make sense). Likewise, the
||| difference between two points results in the vector connecting
||| the two.
|||
||| A point is indexed by the `AffineTransformation` corresponding to its
||| coordinate system. See @AffineTransformation for some more details.
public export
record Point (t : AffineTransformation) where
  constructor P
  x : Double
  y : Double

%runElab derive "Point" [Show]

||| The origin at `(0,0)`.
export
origin : Point t
origin = P 0 0

||| The difference between two points is the vector connecting
||| the points.
export
(-) : Point t -> Point t -> Vector
(-) (P x1 y1) (P x2 y2) = V (x1 - x2) (y1 - y2)

||| Convert a point from one affine space to its image in another
||| affine space.
export
convert : {s,t : _} -> Point s -> Point t
convert (P x y) =
  let AT l (V dx dy) := t <+> inverse s
      V x2 y2 := transform l (V x y)
   in P (x2 + dx) (y2 + dy)

export %inline
{s,t : _} -> Cast (Point s) (Point t) where cast = convert

--------------------------------------------------------------------------------
--          Interface
--------------------------------------------------------------------------------

||| Interface for converting a value to a point in the affine space
||| represented by transformation `t`.
public export
interface GetPoint (0 a : Type) (0 t : AffineTransformation) | a where
  point : a -> Point t

export %inline
GetPoint (Point t) t where point = id

||| Interface for modification of a value `a` by modifying its points in the
||| affine space.
public export
interface ModPoint (0 a : Type) (0 t : AffineTransformation) | a where
  modPoint : (Point t -> Point t) -> a -> a

export %inline
ModPoint (Point t) t where modPoint f p = f p

||| Places an object at a new point in space.
export %inline
setPoint : ModPoint a t => Point t -> a -> a
setPoint = modPoint . const

||| Return the coordinates of a point in the reference affine space.
export %inline
pointId : {t : _} -> GetPoint a t => a -> Point Id
pointId = convert . point

||| Translate an object in 2D space by the given vector.
export
translate : ModPoint a t => Vector -> a -> a
translate (V dx dy) = modPoint (\(P x y) => P (x + dx) (y + dy))

||| Scale an object in 2D space by the given factor.
export
scale : ModPoint a t => Scale -> a -> a
scale v = modPoint (\(P x y) => P (x * v.value) (y * v.value))

||| Calculate the distance between two objects.
export %inline
distance : GetPoint a t => a -> a -> Double
distance x y = length (point x - point y)

||| Calculate the distance of an object from zero.
export %inline
distanceFromZero : GetPoint a t => a -> Double
distanceFromZero = distance origin . point

||| Checks, if two objects are no further apart than `delta`.
export %inline
near : GetPoint a t => (x,y : a) -> (delta : Double) -> Bool
near x y = (distance x y <=)

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

||| Transform a point by applying a transformation patrix.
export
apply : Matrix -> Point t -> Point t
apply (M a b c d) (P x y) = P (a * x + b * y) (c * x + d * y)

||| Calculates a perpendicual point to the line from the first line point
||| with a certain distance. The `positive` flag is to choose the direction
||| from the line (positive -> right top, negative -> left bottom).
export
perpendicularPoint :
     (p1,p2 : Point k)
  -> (distance : Double)
  -> (positive : Bool)
  -> Point k
perpendicularPoint p1 p2 d flag =
  let v   := scale d . normalize $ p2 - p1
      phi := if flag then halfPi else negate halfPi
   in translate (rotate phi v) p1

||| Tries to compute the intersection of two lines
||| from points p11 to p12 and p21 to p22.
|||
||| This tries to solve the following system of equations:
|||
|||   (I)  : `x11 + r * (x12 - x11) = x21 + s * (x22 - x21)`
|||   (II) : `y11 + r * (y12 - y11) = y21 + s * (y22 - y21)`
export
intersect : (p11,p12,p21,p22 : Point t) -> Maybe (Point t)
intersect (P x11 y11) (P x12 y12) (P x21 y21) (P x22 y22) =
  let p       := P {t} (x21 - x11) (y21 - y11)
      m       := M (x12 - x11) (x21 - x22) (y12 - y11) (y21 - y22)
      Just m' := inverse m | Nothing => Nothing
      P r s   := apply m' p
   in Just $ P (x11 + r * (x12 - x11)) (y11 + r * (y12 - y11))

||| Computes the distance of a point `p` from a line defined
||| by two of its points (`pl1` and `pl2`).
export
distanceToLine : (p, pl1, pl2 : Point t) -> Maybe Double
distanceToLine p pl1 pl2 =
  let pp := perpendicularPoint p (translate (pl1 - pl2) p) 1 True
   in distance p <$> intersect pl1 pl2 p pp
