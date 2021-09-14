module Data.IntMap

import Data.Refined
import Data.IntMap.Array

%default total

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

private %inline %tcinline
shift : Bits32 -> Bits32
shift n = assert_smaller n $ prim__shr_Bits32 n 5

private %inline %tcinline
shiftl : Bits32 -> Bits32
shiftl n = prim__shl_Bits32 n 5

private %inline
index : Bits32 -> Index32
index n = MkIndex32 (cast $ prim__and_Bits32 n 0x1f) (believe_me Oh)

private %inline
get : Bits32 -> Array32 a -> a
get = read . index

private %inline
set : Bits32 -> Array32 a -> a -> Array32 a
set n arr v = set (index n) arr v

private %inline
mod : Bits32 -> Array32 a -> (a -> a) -> Array32 a
mod n arr f = mod (index n) arr f

--------------------------------------------------------------------------------
--          IntMap
--------------------------------------------------------------------------------

public export
data IntMap : (a : Type) -> Type where
  Empty : IntMap a
  Leaf  : (v : a) -> IntMap a
  Node  : (children : Array32 $ IntMap a) -> IntMap a


public export %inline
empty : IntMap a
empty = Empty

export
singleton : (key : Bits32) -> (v : a) -> IntMap a
singleton 0 v = Leaf v
singleton k v =
  Node $ new Empty $
    \marr =>
      let (_ # marr2) = mwrite (index k) marr (singleton (shift k) v)
       in freeze marr2

-- create a node containing the two given values
-- at the given keys. we already verified that k1 /= k2
node2 : (k1,k2 : Bits32) -> (v1,v2 : a) -> IntMap a
node2 k1 k2 v1 v2 =
  let i1 = index k1
      i2 = index k2
   in if i1 == i2
         -- the two subtrees must go into the same bucket
         then Node $ new Empty $
                \marr1 =>
                  let kn1 = shift k1
                      kn2 = shift k2
                      (_ # marr2) = mwrite i1 marr1 (node2 kn1 kn2 v1 v2)
                   in freeze marr2
         -- the two subtrees go into distinct buckets
         else Node $ new Empty $
                \marr1 =>
                  let kn1 = shift k1
                      kn2 = shift k2
                      (_ # marr2) = mwrite i1 marr1 (singleton kn1 v1)
                      (_ # marr3) = mwrite i2 marr2 (singleton kn2 v2)
                   in freeze marr3

export
insert : (key : Bits32) -> (v : a) -> IntMap a -> IntMap a
insert k v Empty           = singleton k v
insert k v (Node children) = Node $ mod k children (insert (shift k) v)
insert 0 v _               = Leaf v
insert k v (Leaf v2)       = node2 k 0 v v2

export
insertWith :  (f : a -> a -> a)
           -> (key : Bits32)
           -> (v : a)
           -> IntMap a
           -> IntMap a
insertWith _ k v Empty     = singleton k v
insertWith f k v (Node cs) = Node $ mod k cs (insertWith f (shift k) v)
insertWith f 0 v (Leaf v2) = Leaf $ f v v2
insertWith f k v (Leaf v2) = node2 k 0 v v2

export
fromList : List (Bits32,a) -> IntMap a
fromList = go Empty
  where go : IntMap a -> List (Bits32,a) -> IntMap a
        go m []           = m
        go m ((k,v) :: t) = go (insert k v m) t

export
fromListWith : (f : a -> a -> a) -> List (Bits32,a) -> IntMap a
fromListWith f = go Empty
  where go : IntMap a -> List (Bits32,a) -> IntMap a
        go m []           = m
        go m ((k,v) :: t) = go (insertWith f k v m) t

export
toList : IntMap a -> List (Bits32, a)
toList Empty     = []
toList (Leaf v)  = [(0,v)]
toList (Node cs) = assert_total (go 0)
  where go : Bits32 -> List (Bits32,a)
        go ix =
          if ix >= 32
             then Nil
             else let ps = IntMap.toList $ read (index ix) cs
                   in map (\(k,v) => (prim__or_Bits32 ix (shiftl k), v)) ps ++
                      go (assert_smaller ix $ ix+1)


--------------------------------------------------------------------------------
--          Accessing Values
--------------------------------------------------------------------------------

export
lookup : (key : Bits32) -> (map : IntMap a) -> Maybe a
lookup n (Node cs) = lookup (shift n) (get n cs)
lookup _ Empty     = Nothing
lookup 0 (Leaf v)  = Just v
lookup _ (Leaf _)  = Nothing

--------------------------------------------------------------------------------
--          Interfaces
--------------------------------------------------------------------------------

export
Eq a => Eq (IntMap a) where
  (==) = (==) `on` IntMap.toList

export
Show a => Show (IntMap a) where
  showPrec p m = showCon p "fromList" $ showArg (IntMap.toList m)
