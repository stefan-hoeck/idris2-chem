module Geom.Vector

import Data.Refined
import Geom.Angle
import Geom.Scale

%default total

--------------------------------------------------------------------------------
--          Linear Transformations
--------------------------------------------------------------------------------

||| A linear transformation in a two-dimensional vector space
||| is a sequence of scalings and rotations.
|||
||| By not using a matrix here we make sure that a transformation
||| is invertible, without the risk of a division by zero.
||| This might be a performance issue, but only if we create large
||| trees of wild mixtures of linear transformations. However,
||| in a UI we often work with sequences of the same type of
||| transformations such as a sequence of scalings or a sequence of
||| rotations. These are merged automatically in the `Semigroup`
||| implementation.
public export
record LinearTransformation where
  constructor LT
  scale  : Scale
  rotate : Angle

||| The identity transformation
public export
Id : LinearTransformation
Id = LT 1.0 zero

||| A clockwise rotation by the given angle.
public export
rotation : Angle -> LinearTransformation
rotation = LT 1.0

||| A scaling by the given factor.
public export
scaling : Scale -> LinearTransformation
scaling = (`LT` zero)

export
Semigroup LinearTransformation where
  LT s1 r1 <+> LT s2 r2 = LT (s1 * s2) (r1 + r2)

export
Monoid LinearTransformation where neutral = Id

||| Computes the inverse of a linear transformation, so
||| `x <+> inverse x` corresponse to the identity (modulo rounding
||| errors).
export %inline
inverse : LinearTransformation -> LinearTransformation
inverse (LT s r) = LT (inverse s) (negate r)

--------------------------------------------------------------------------------
--          Vectors and VectorSpaces
--------------------------------------------------------------------------------

||| A two-dimensional vector.
public export
record Vector where
  constructor V
  x : Double
  y : Double

||| The zero vector.
export
vzero : Vector
vzero = V 0 0

||| Unity vector along the x axis
export
vone : Vector
vone = V 1 0

||| Computes the length of a vector.
export
length : Vector -> Double
length (V x y) = sqrt (x * x + y * y)

||| Vector addition.
export
(+) : Vector -> Vector -> Vector
V x1 y1 + V x2 y2 = V (x1+x2) (y1+y2)

||| Vector subtraction.
export
(-) : Vector -> Vector -> Vector
V x1 y1 - V x2 y2 = V (x1-x2) (y1-y2)

||| Inverts the given vector by negating its coordinates.
export
negate : Vector -> Vector
negate (V x y) = V (-x) (-y)

||| Multiply a vector with a scalar.
export
scale : Double -> Vector -> Vector
scale v (V x y) = V (v*x) (v*y)

||| Normalize a vector to length 1.
export
normalize : Vector -> Vector
normalize v =
  let l := length v in if l == 0.0 then v else scale (1/l) v

||| Apply a linear transformation to a vector
export
transform : LinearTransformation -> Vector -> Vector
transform (LT s r) (V x y) =
  let co := s.value * cos r.value
      si := s.value * sin r.value
   in V (co * x - si * y) (si * x + co * y)

||| Define a vector by giving its length and its angle
export
polar : Scale -> Angle -> Vector
polar s a = transform (LT s a) vone

||| Rotate a vector by the specified number of degrees
export
rotate : Angle -> Vector -> Vector
rotate = transform . rotation

||| Tries to calculate the angle of the given vector.
||| Fails in case this is the zero vector.
export
angle : Vector -> Maybe Angle
angle (V x y) =
  if x == 0 && y == 0 then Nothing
  else if x == 0 then Just $ if y > 0 then halfPi else negate halfPi
  else
    let phi := atan (y / x)
     in Just $ if x > 0 then angle phi else angle (phi + pi)
