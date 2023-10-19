module Geom.Angle

import Chem.Util
import Derive.Prelude

%language ElabReflection
%default total

--------------------------------------------------------------------------------
--          Angle
--------------------------------------------------------------------------------

export
TwoPi : Double
TwoPi = 2 * pi

||| Convert a floating point number to an angle
||| in the interval [0, 2 * pi).
export
normalize : Double -> Double
normalize x =
  if x < 0 then
    let f := ceiling (abs x / TwoPi) in x + f * TwoPi
  else if x >= TwoPi then
    let f := floor (x / TwoPi) in x - f * TwoPi
  else x

||| A normalized angle in the range [0,2 * pi).
public export
record Angle where
  constructor A
  ||| The normalized value
  value : Double

  ||| The original floating point number from which the angle
  ||| was created.
  0 org : Double

  ||| Proof that we did not forget the normalization step.
  {auto 0 prf : value === normalize org}

%runElab derive "Angle" [Show,Eq,Ord]

||| Convenience constructor for angles.
|||
||| It is safe to invoke `A` directly, but one has to deal
||| with the proofing stuff.
export %inline
angle : Double -> Angle
angle v = A (normalize v) v

export
halfPi : Angle
halfPi = angle (pi / 2)

export
twoThirdPi : Angle
twoThirdPi = angle (TwoPi / 3)

export
threeHalfPi : Angle
threeHalfPi = angle (3 * pi / 2)

export
pi : Angle
pi = angle pi

export
zero : Angle
zero = angle 0

||| Returns the absolute distance between two angles
export
delta : Angle -> Angle -> Angle
delta (A x _) (A y _) = angle (abs $ x - y)

||| From a list of angles, returns the one closest to the given angle
-- TODO: remove this
export %inline
closestAngle : Angle -> List Angle -> Maybe Angle
closestAngle = minBy . delta

||| Addition of two angles
export %inline
(+) : Angle -> Angle -> Angle
A x _ + A y _ = angle $ x + y

||| Difference between two angles
export %inline
(-) : Angle -> Angle -> Angle
A x _ - A y _ = angle $ x - y

||| The inverse of an angle so that `x + negate x == 0`
||| (modulo rounding errors).
export %inline
negate : Angle -> Angle
negate (A x _) = angle $ TwoPi - x

||| Multiplication of an angle with a constant factor
export %inline
(*) : Double -> Angle -> Angle
v * A x _ = angle $ v * x

||| Convert and angle to centigrees
export %inline
toDegree : Angle -> Double
toDegree a = a.value * 180 / pi

||| Convert an angle in centigrees to one in radians
export %inline
fromDegree : Double -> Angle
fromDegree = angle .  (*) (pi/180)

||| Angle bisector counterclockwise
export
bisector : Angle -> Angle -> Angle
bisector x y = x + 0.5 * (y - x)

export
largestBisector : List Angle -> Angle
largestBisector xs =
  fromMaybe zero . map (uncurry bisector) . maxBy diff . pairs $ sort xs
  where
    pairs : List a -> List (a,a)
    pairs [] = []
    pairs (h::t) = zip (h::t) (t ++ [h])

    diff : (Angle, Angle) -> Angle
    diff (x,y) = y - x

    maxBy : Ord b => (a -> b) -> List a -> Maybe a
    maxBy f []     = Nothing
    maxBy f (h::t) = Just $ foldl (\x,y => if f x >= f y then x else y) h t

--------------------------------------------------------------------------------
--          Tests and proofs
--------------------------------------------------------------------------------

0 PI : Double
PI = pi

0 DoubleEq : Double -> Double -> Type
DoubleEq x y = (abs (x - y) < 0.0000000001) === True

0 Norm : Double -> Double
Norm x = normalize x

0 normalize0 : DoubleEq (Norm 0) 0.0
normalize0 = Refl

0 normalize2pi : DoubleEq (Norm $ 2 * PI) 0
normalize2pi = Refl

0 normalizeAny : DoubleEq (Norm $ 21.54 * PI) (1.54 * PI)
normalizeAny = Refl

0 normalizeNeg : DoubleEq (Norm $ negate PI) PI
normalizeNeg = Refl

0 normalizeAnyNeg : DoubleEq (Norm $ (-21.54) * PI) ((2 - 1.54) * PI)
normalizeAnyNeg = Refl
