module Geom.Matrix

||| A 2x2 matrix of floating point numbers
public export
record Matrix where
  constructor M
  x11 : Double
  x12 : Double
  x21 : Double
  x22 : Double

||| Matrix addition
export
(+) : Matrix -> Matrix -> Matrix
M a1 b1 c1 d1 + M a2 b2 c2 d2 = M (a1 + a2) (b1 + b2) (c1 + c2) (d1 + d2)

||| Matrix multiplication
export
(*) : Matrix -> Matrix -> Matrix
M x11 x12 x21 x22 * M y11 y12 y21 y22 =
  M (x11 * y11 + x12 * y21)
    (x11 * y21 + x12 * y22)
    (x21 * y11 + x22 * y21)
    (x21 * y21 + x22 * y22)

||| Tries to compute the inverse of a matrix
|||
||| This fails if the determinant of the matrix equals zero.
export
inverse : Matrix -> Maybe Matrix
inverse (M a b c d) =
  let det := a * d - b * c
   in if abs det < 1.0e-12 then Nothing
      else Just $ M (d / det) (negate b / det) (negate c / det) (a / det)
