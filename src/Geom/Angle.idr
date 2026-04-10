module Geom.Angle

import Chem.Util
import Derive.Prelude

%language ElabReflection
%default total

public export
Epsilon : Double
Epsilon = 1.0e-12

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

export
fullSteps : Nat -> Angle
fullSteps 0 = zero
fullSteps n = angle (TwoPi / cast n)

||| Returns the absolute distance between two angles
|||
||| Unlike `minDelta`, this just subtracts the smaller angle
||| from the larger one. Therefore, `delta zero halfPi = halfPi`
||| and `delta zero threeHalfPi = threeHalfPi`.
export
delta : Angle -> Angle -> Angle
delta (A x _) (A y _) = angle (abs $ x - y)

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

||| Divides an angle into `n` equal part.
|||
||| Returns the angle unmodified in case `n` equals zero.
export
divide : Nat -> Angle -> Angle
divide 0 a       = a
divide n (A x _) = angle (x / cast n)

||| Returns the shortest distance between two angles.
||| (either clockwise or counterclockwise.)
|||
||| Unlike `delta`, this computes the *smaller* angle
||| between the two input values.
||| Therefore, `minDelta zero halfPi = minDelta zero threeHalfPi = halfPi`.
export
minDelta : Angle -> Angle -> Angle
minDelta x y = min (delta x y) (negate (delta x y))

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

||| From a list of angles, returns the one closest to the given angle
export %inline
closestAngle : Angle -> List Angle -> Maybe Angle
closestAngle = minBy . delta

shiftZip : List a -> List (a,a)
shiftZip []        = []
shiftZip (x :: xs) = zip (x::xs) (xs++[x])

||| Given an angle `phi` plus a list of angles, returns from the
||| list two angles `a` and `b`, so that `phi` lies between `a` and `b`
||| with no other angle closer to `phi`.
|||
||| Note: In case of this being successful, `phi` will always lie counter
|||       clockwise of the first returned angle and the second returned
|||       angle will lie counter-clockwise of `phi`.
export
enclosingAngles : Angle -> List Angle -> Maybe (Angle,Angle)
enclosingAngles x xs =
  case sort xs of
    []    => Nothing
    a::as => case find (\(y,z) => y <= x && x <= z) (zip (a::as) as) of
      Nothing => Just (last $ a::as,a)
      Just p  => Just p

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
--          Regular n-gons and regular arcs
--------------------------------------------------------------------------------

||| An arc of `segs` segments connecting two existing nodes.
|||
||| Used for creating rings and bridges when placing molecules.
public export
record Arc where
  constructor MkArc
  ||| Total angle of the arc
  angle    : Angle

  ||| Angle of a single segment of the arc
  step     : Angle

  ||| Radius of the arc
  radius   : Double

  ||| Distance between the center of the arc and the middle
  ||| of a segment.
  distance : Double

%runElab derive "Arc" [Show,Eq]

||| Angle at the corner of a regular n-gon
export %inline
ngonAngle : (n : Nat) -> (0 prf : LTE 3 n) => Angle
ngonAngle n = pi - fullSteps n

||| Radius of a regular n-gon with side length `side`.
|||
||| This is the distance from the center of the n-gon to one of its
||| corners.
export %inline
ngonRadius : (side : Double) -> (n : Nat) -> (0 prf : LTE 3 n) => Double
ngonRadius side n = 0.5 * side / cos ((ngonAngle n).value / 2)

segDist : Double -> Double -> Double
segDist side rad = sqrt (pow rad 2 - pow (side / 2) 2)

||| Distance from the center of a regular n-gon with side length `side`
||| to the middle of one of its sides.
export %inline
ngonDistance : (side : Double) -> (n : Nat) -> (0 prf : LTE 3 n) => Double
ngonDistance side n = segDist side (ngonRadius side n)

-- radius of an arc of angle `phi` connecting two points
-- with a distance of `d`
arcRadius : (d,phi : Double) -> Double
arcRadius d phi = d / (2 * sin (phi / 2))

-- length of a single line segment, out of `n`
-- segments approximating an arc of angle `phi` and connecting two
-- points `x` and `y`, with a distance of `d` between `x` and `y`.
segmentLength : Nat -> (d,phi : Double) -> Double
segmentLength n d phi = 2 * (arcRadius d phi) * sin (phi / (2 * cast (S n)))

mkArc : Nat -> (d,phi : Double) -> Arc
mkArc n d phi =
 let r := arcRadius d phi
     a := angle phi
  in MkArc a (divide (S n) a) r (segDist d r)

export
ngon : (side : Double) -> (n : Nat) -> (0 prf : LTE 3 n) => Arc
ngon side n =
 let a := fullSteps n
  in MkArc (negate a) a (ngonRadius side n) (ngonDistance side n)

||| Computes the dimensions of an arc that connects two
||| existing nodes (with a distance of `d` between the nodes)
||| by inserting `n` additional nodes between them.
|||
||| The arc is optimized in such a way that the distance between two
||| adjacent nodes is as close to `len` as possible.
|||
||| Note: If `len` is too short, that is `(n+1) * len < d`, this returns
|||       close to - but not exactly - a straight line. Client code is
|||       responsible to choose `len` in such a manner, that an arc
|||       with a reasonable minimal curvature is constructed,
|||       for instance by setting the minimal `len`
|||       at `(1+delta)*d / (n+1)` with `delta > 0`.
export
arc : (n : Nat) -> (0 prf : IsSucc n) => (len,d : Double) -> Arc
arc n@(S k) len d =
  case abs (len-d) < Epsilon of
    -- this is just (or close to) a regular n-gon
    True  => ngon len (S $ S $ S k)
    -- run a binary search to find the ideal arc
    False => find 64 Epsilon (2*pi - Epsilon)
  where
    best : (l,u : Double) -> Arc
    best l u =
     let ll := segmentLength n d l
         lu := segmentLength n d u
      in if abs (lu-len) <= abs (ll-len) then mkArc n d u else mkArc n d l

    -- a binary search of at most `iter` iterations to find the
    -- ideal arc angle `phi` (with current lower and upper bounds `l` and `u`)
    find : (iter : Nat) -> (l,u : Double) -> Arc
    find 0     l u = best l u
    find (S k) l u =
      case abs (u-l) <= Epsilon of
        True  => best l u
        False => case segmentLength n d ((l+u)/2.0) >= len of
          True  => find k l ((l+u)/2.0)
          False => find k ((l+u)/2.0) u

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
