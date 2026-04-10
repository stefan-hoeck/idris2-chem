-- TODO: If this works out nicely, it should be moved to hedgehog.
module Test.Geom.Similarity

import Hedgehog
import Geom

%default total

||| A lower bound for differences between values in
||| similarity tests.
public export
record Epsilon where
  [noHints]
  constructor E
  eps : Double

||| An interface for comparing values that are *almost*
||| identical, the most basic of these being `Double`, of course.
|||
||| Unlike the equality tested in `Eq`, similarity is not
||| an equivalence relation. In particular, it is not transitive
||| in the general case.
public export
interface Similar a where
  isSimilar : Epsilon => a -> a -> Bool

export
Similar Double where
  isSimilar @{E eps} x y = abs (x-y) <= eps

export
Similar a => Similar (Maybe a) where
  isSimilar (Just x) (Just y) = isSimilar x y
  isSimilar Nothing  Nothing  = True
  isSimilar _        _        = False

export
Similar a => Similar b => Similar (Either a b) where
  isSimilar (Right x) (Right y) = isSimilar x y
  isSimilar (Left x)  (Left y)  = isSimilar x y
  isSimilar _         _         = False

export
Similar a => Similar b => Similar (a,b) where
  isSimilar (x1,y1) (x2,y2) = isSimilar x1 x2 && isSimilar y1 y2

export
Similar a => Similar (List a) where
  isSimilar (x::xs) (y::ys) = isSimilar x y && isSimilar xs ys
  isSimilar []      []      = True
  isSimilar _       _       = False

export
Similar a => Similar (SnocList a) where
  isSimilar (sx:<x) (sy:<y) = isSimilar x y && isSimilar sx sy
  isSimilar [<]     [<]     = True
  isSimilar _       _       = False

export
Similar (Point t) where
  isSimilar (P x1 y1) (P x2 y2) = isSimilar x1 x2 && isSimilar y1 y2

export
Similar (Vector t) where
  isSimilar (V x1 y1) (V x2 y2) = isSimilar x1 x2 && isSimilar y1 y2

||| Angles can be similar even if their absolute values are
||| drastically different.
|||
||| For instances, `angle (TwoPi - 0.0000000001)` is similar to `zero`.
export
Similar Angle where
  isSimilar x y = isSimilar 0.0 (value $ minDelta x y)

export
Similar Arc where
  isSimilar (MkArc t1 a1 r1 d1) (MkArc t2 a2 r2 d2) =
    isSimilar t1 t2 &&
    isSimilar a1 a2 &&
    isSimilar r1 r2 &&
    isSimilar d1 d2

export infix 6 =~=

||| Fails the test if the two arguments provided are not similar.
export %inline
(=~=) : Epsilon => Similar a => Show a => Monad m => a -> a -> TestT m ()
(=~=) x y = diff x isSimilar y

export %hint
epsilon : Epsilon
epsilon = E 1.0e-6
