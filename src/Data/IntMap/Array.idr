||| Internal module for `Data.IntMap`
|||
||| This provides a fixed width array (right
||| now of size 8). Use `Ix` for safe indexing
||| without bounds checking.
|||
||| TODO: If this works out nicely, we should consider
|||       putting this in its own library of fixed size
|||       arrays.
module Data.IntMap.Array

import Data.Refined
import Data.IOArray.Prims
import Data.Vect
import Language.Reflection.Refined
import Text.RW

%default total
%language ElabReflection

--------------------------------------------------------------------------------
--          Ix
--------------------------------------------------------------------------------

||| First five bits set
public export %inline
mask : Bits8
mask = 7

||| Safe index into the arrays provided by this module.
public export
record Ix where
  constructor MkIx
  value : Bits8
  0 prf : So (value <= Array.mask)

%runElab refinedBits8 "Ix"

public export %inline
mkIx : Bits8 -> Ix
mkIx v = MkIx (prim__and_Bits8 v mask) (believe_me Oh)

||| Increment an `Ix` by 1 without checking the bounds.
||| Callers must be certain that `Ix` is less than 7.
export %inline %tcinline
unsafeInc : Ix -> Ix
unsafeInc ix = assert_smaller ix $ MkIx (ix.value + 1) (believe_me Oh)

||| Decrement an `Ix` by 1 without checking the bounds.
||| Callers must be certain that `Ix` is greater than 0.
export %inline %tcinline
unsafeDec : Ix -> Ix
unsafeDec ix = assert_smaller ix $ MkIx (ix.value - 1) (believe_me Oh)

--------------------------------------------------------------------------------
--          Primitive Utilities
--------------------------------------------------------------------------------

private %inline
read_ : Ix -> ArrayData a -> a
read_ (MkIx i _) arr =
  unsafePerformIO (fromPrim $ prim__arrayGet arr $ prim__cast_Bits8Int i)

private
write_ : Ix -> ArrayData a -> a -> ()
write_ (MkIx i _) arr va =
  unsafePerformIO (fromPrim $ prim__arraySet arr (prim__cast_Bits8Int i) va)

private
new_ : a -> ArrayData a
new_ va = unsafePerformIO (fromPrim $ prim__newArray 8 va)

--------------------------------------------------------------------------------
--          Mutable Arrays
--------------------------------------------------------------------------------

||| Safe, mutable fixed-size array.
|||
||| All operations on `MArr` provided by this module
||| are linear in the array argument. As such, they
||| guarantee that the array is not accessed several
||| times in an unsafe way.
export
record MArr a where
  constructor MkMArr
  values : ArrayData a

||| Read the value at the given position
export %inline
mread : Ix -> (1 _ : MArr a) -> Res a (const $ MArr a)
mread ix (MkMArr vs) = read_ ix vs # MkMArr vs

||| Update the value at the given position
export
mwrite : Ix -> (1 _ : MArr a) -> a -> Res () (const $ MArr a)
mwrite ix (MkMArr vs) va = write_ ix vs va # MkMArr vs

||| Update the value at the given position
export
mmod : Ix -> (1 _ : MArr a) -> (f : a -> a) -> Res () (const $ MArr a)
mmod ix (MkMArr vs) f = write_ ix vs (f $ read_ ix vs) # MkMArr vs

||| Create a new mutable array and use it in the
||| given function.
export
new : (val : a) -> (f : (1 _ : MArr a) -> b) -> b
new va f = f (MkMArr $ new_ va)

--------------------------------------------------------------------------------
--          Immutable Arrays
--------------------------------------------------------------------------------

export
record Arr a where
  constructor MkArr
  values : ArrayData a

||| Convert a mutable to an immutable array
export %inline
freeze : (1 _ : MArr a) -> Arr a
freeze (MkMArr values) = MkArr values

||| Read the value at the given position
export %inline
read : Ix -> Arr a -> a
read ix (MkArr vs) = read_ ix vs

||| Creates a mutable copy of the given array and
||| pass it to the provided linear function.
export
copy : (vs : Arr a) -> (f : (1 _ : MArr a) -> b) -> b
copy as f = new (read 0 as) (go 7)
  where go : Ix -> (1 _ : MArr a) -> b
        go n ma1 =
          if n == 0 then f ma1
          else let (_ # ma2) = mwrite n ma1 (read n as)
                in go (unsafeDec n) ma2

||| Insert `va` at position `ix` into a copy of
||| `arr`.
export
set : (ix : Ix) -> (arr : Arr a) -> (va : a) -> Arr a
set ix arr va =
  copy arr $ \ma1 =>
    let (_ # ma2) = mwrite ix ma1 va
     in freeze ma2

||| Update the value at position `ix` in a copy of
||| `arr`.
export
mod : (ix : Ix) -> (arr : Arr a) -> (f : a -> a) -> Arr a
mod ix arr f =
  copy arr $ \ma1 =>
    let (_ # ma2) = mwrite ix ma1 (f $ read ix arr)
     in freeze ma2

--------------------------------------------------------------------------------
--          Creating Arrays
--------------------------------------------------------------------------------

||| Filles an array by mapping its indices to values
||| using the given function.
export
mapping : (Ix -> a) -> Arr a
mapping f = new (f 0) (go 7)
  where go : Ix -> (1 _ : MArr a) -> Arr a
        go n ma1 =
          if n == 0 then freeze ma1
          else let (_ # ma2) = mwrite n ma1 (f n)
                in go (unsafeDec n) ma2

||| Fills an immutable array with the given values
export
fill : a -> Arr a
fill va = new va freeze

||| Iteratively fills an array using the given
||| generating function
export
unfoldr : (f : b -> (b,a)) -> b -> Arr a
unfoldr f ini =
  let (b2,va) = f ini
   in new va (go 1 b2)
  where go : Ix -> b -> (1 _ : MArr a) -> Arr a
        go n vb ma1 =
          let (vb2,va) = f vb
              (_ # ma2) = mwrite n ma1 va
           in if n == 7 then freeze ma2
              else go (unsafeInc n) vb2 ma2

||| Iteratively fills an array by repeatedly applying
||| `f` to `ini
export
iterate : (f : a -> a) -> (ini : a) -> Arr a
iterate f = unfoldr (\s => (f s, s))

||| Converts a `Vect` of the correct size into an array.
export
fromVect : Vect 8 a -> Arr a
fromVect (h :: t) =
  new h (go t 1)
  where go : Vect k a -> Ix -> (1 _ : MArr a) -> Arr a
        go []        _  arr  = freeze arr
        go (v :: vs) ix arr1 =
          let (_ # arr2) = mwrite ix arr1 v
           in go vs (unsafeInc ix) arr2

||| Converts an `Array` to a `Vect 8`.
export
toVect : Arr a -> Vect 8 a
toVect arr =
  [ read  0 arr, read  1 arr, read  2 arr, read 3  arr
  , read  4 arr, read  5 arr, read  6 arr, read 7  arr
  ]

--------------------------------------------------------------------------------
--          Comparing Arrays
--------------------------------------------------------------------------------

arrEq : Eq a => Arr a -> Arr a -> Bool
arrEq a1 a2 = go 0
  where go : Ix -> Bool
        go n = 
          let res = read n a1 == read n a2
           in if n == 7 then res
              else if res then go (unsafeInc n) else False

arrComp : Ord a => Arr a -> Arr a -> Ordering
arrComp a1 a2 = go 0
  where go : Ix -> Ordering
        go n = 
          let res = read n a1 `compare` read n a2
           in if n == 7 then res
              else case res of
                EQ => go (unsafeInc n)
                _  => res

--------------------------------------------------------------------------------
--          Interfaces
--------------------------------------------------------------------------------

------------------------------
-- Eq and Ord

export %inline
Eq a => Eq (Arr a) where
  (==) = arrEq

export %inline
Ord a => Ord (Arr a) where
  compare = arrComp

------------------------------
-- Functor, Applicative, Monad

export
Functor Arr where
  map f arr = mapping (\ix => f $ read ix arr)

export
Applicative Arr where
  pure = fill
  fa <*> va = mapping (\ix => read ix fa (read ix va))

export
Monad Arr where
  va >>= f = mapping (\ix => read ix (f $ read ix va))

------------------------------
-- Semigroup, Monoid

export
Semigroup a => Semigroup (Arr a) where
  a1 <+> a2 = [| a1 <+> a2 |]

export
Monoid a => Monoid (Arr a) where
  neutral = fill neutral

------------------------------
-- Foldable, Traversable

foldlImpl : (a -> e -> a) -> a -> Arr e -> a
foldlImpl f x arr = go 0 x
  where go : Ix -> a -> a
        go ix va =
          let va2 = f va (read ix arr)
           in if ix == 7 then va2 else go (unsafeInc ix) va2

foldrImpl : (e -> a -> a) -> a -> Arr e -> a
foldrImpl f x arr = go 7 x
  where go : Ix -> a -> a
        go ix va =
          let va2 = f (read ix arr) va
           in if ix == 0 then va2 else go (unsafeDec ix) va2

foldMapImpl : Monoid m => (e -> m) -> Arr e -> m
foldMapImpl f arr = go 1 (f $ read 0 arr)
  where go : Ix -> m -> m
        go ix v =
          let v2 = v <+> f (read ix arr)
           in if ix == 7 then v2 else go (unsafeInc ix) v2

toListImpl : Arr a -> List a
toListImpl arr = go 7 Nil
  where go : Ix -> List a -> List a
        go ix as =
          let as2 = read ix arr :: as
           in if ix == 0 then as2 else go (unsafeDec ix) as2

foldlMImpl : Monad m => (a -> e -> m a) -> a -> Arr e -> m a
foldlMImpl f x arr = go 0 x
  where go : Ix -> a -> m a
        go ix va = do
          va2 <- f va $ read ix arr
          if ix == 7 then pure va2 else go (unsafeInc ix) va2

export %inline
Foldable Arr where
  foldl   = foldlImpl
  foldr   = foldrImpl
  foldMap = foldMapImpl
  foldlM  = foldlMImpl
  toList  = toListImpl
  null _  = False

export
Traversable Arr where
  traverse f = map fromVect . traverse f . toVect

------------------------------
-- Show

export
Show a => Show (Arr a) where
  showPrec p arr = showCon p "fromVect" $ showArg (toVect arr)
