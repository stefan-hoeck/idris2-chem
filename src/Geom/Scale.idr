module Geom.Scale

import Derive.Prelude
import Derive.Refined

%language ElabReflection
%default total

||| Scaling factor in the range [1.0e-6,1.0e6].
public export
ValidScale : Double -> Bool
ValidScale x = 1.0e-6 <= x && x <= 1.0e6

||| A scaling factor
public export
record Scale where
  constructor S
  value       : Double
  {auto 0 prf : Holds ValidScale value}

%runElab derive "Scale" [Show,Eq,Ord,RefinedDouble]

||| Safely convert a floating point number to a `Scale`
export
scale : Double -> Scale
scale x = case refineScale x of
  Just s  => s
  Nothing => if x < 1.0e-6 then S 1.0e-6 else S 1.0e6

||| Invert the scaling factor so that `x * inverse x == 1`
||| (modulo rounding errors).
export %inline
inverse : Scale -> Scale
inverse (S v) = scale $ 1 / v

||| Multiply two scaling factors.
export %inline
(*) : Scale -> Scale -> Scale
S x * S y = scale $ x * y

||| Divide a scaling factor by another one
export %inline
(/) : Scale -> Scale -> Scale
S x / S y = scale $ x / y
