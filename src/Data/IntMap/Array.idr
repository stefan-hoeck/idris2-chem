||| Internal module for `Data.IntMap`
module Data.IntMap.Array

import Data.Refined
import Data.IOArray.Prims
import Text.RW
import Language.Reflection.Refined

%default total
%language ElabReflection

||| First five bits set
public export %inline
mask : Int
mask = 0x1f

public export
record Index32 where
  constructor MkIndex32
  value : Int
  0 prf : So (0 <= value && value < 31)

%runElab rwInt "Index32" `(Int)

export
unsafeIndex : Int -> Index32
unsafeIndex n = MkIndex32 n (believe_me Oh)

export
withMask : Int -> Index32
withMask n = unsafeIndex $ prim__and_Int mask n

private %inline
unsafeRead_ : Int -> ArrayData a -> a
unsafeRead_ ix arr = unsafePerformIO (fromPrim $ prim__arrayGet arr ix)

private
unsafeWrite_ : Int -> ArrayData a -> a -> ()
unsafeWrite_ ix arr va = unsafePerformIO (fromPrim $ prim__arraySet arr ix va)

private
unsafeNew : a -> ArrayData a
unsafeNew va = unsafePerformIO (fromPrim $ prim__newArray 32 va)


export
record MArray32 a where
  constructor MkMArray32
  values : ArrayData a

export %inline
mread : Index32 -> (1 _ : MArray32 a) -> Res a (const $ MArray32 a)
mread ix (MkMArray32 vs) = unsafeRead_ ix.value vs # MkMArray32 vs

export
mwrite : Index32 -> (1 _ : MArray32 a) -> a -> Res () (const $ MArray32 a)
mwrite ix (MkMArray32 vs) va = unsafeWrite_ ix.value vs va # MkMArray32 vs

export
record Array32 a where
  constructor MkArray32
  values : ArrayData a

export %inline
freeze : (1 _ : MArray32 a) -> Array32 a
freeze (MkMArray32 values) = MkArray32 values

export
read : Index32 -> Array32 a -> a
read ix (MkArray32 vs) = unsafePerformIO (fromPrim $ prim__arrayGet vs ix.value)

export
new : (val : a) -> (1 _ : (1 _ : MArray32 a) -> b) -> b
new va f = f (MkMArray32 $ unsafeNew va)

export
mapping : (Index32 -> a) -> Array32 a
mapping f = new (f 0) (go 31)
  where
    go : Int -> (1 _ : MArray32 a) -> Array32 a
    go n arr =
       if n < 0 
          then freeze arr
          else let (_ # arr2) = mwrite (unsafeIndex n) arr (f $ unsafeIndex n)
               in go (assert_smaller n (n-1)) arr2

export
set : Index32 -> Array32 a -> a -> Array32 a
set ix arr va =
  mapping (\x => if ix == x then va else read x arr)

export
mod : Index32 -> Array32 a -> (a -> a) -> Array32 a
mod ix arr f =
  mapping (\x => if ix == x then f (read x arr) else read x arr)
