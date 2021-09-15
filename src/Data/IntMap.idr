module Data.IntMap

import Data.Refined
import Data.IntMap.Array

%default total

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

private %inline
bits : Bits32
bits = 3

private %inline
shr : Bits32 -> Bits32 -> Bits32
shr = prim__shr_Bits32

private %inline %tcinline
shrb : Bits32 -> Bits32
shrb n = assert_smaller n $ shr n bits

private %inline
index : Bits32 -> Ix
index n = mkIx (cast n)

private %inline
get : Bits32 -> Arr a -> a
get = read . index

private %inline
set : Bits32 -> Arr a -> a -> Arr a
set n arr v = set (index n) arr v

private %inline
mod : Bits32 -> Arr a -> (a -> a) -> Arr a
mod n arr f = mod (index n) arr f

--------------------------------------------------------------------------------
--          IntMap
--------------------------------------------------------------------------------

public export
data IntMap : (a : Type) -> Type where
  Empty : IntMap a
  Leaf  : (k : Bits32) -> (v : a) -> IntMap a
  Node  : (children : Arr $ IntMap a) -> IntMap a

public export %inline
empty : IntMap a
empty = Empty

public export %inline
singleton : (key : Bits32) -> (v : a) -> IntMap a
singleton = Leaf

-- create a node containing the two given values
-- at the given keys. we already verified that k1 /= k2
-- k1,k2 are the keys
-- s1,s2 are the remaining bit strings
-- v1,v2 are the values to be inserted
node2 : (k1,k2,s1,s2 : Bits32) -> (v1,v2 : a) -> IntMap a
node2 k1 k2 s1 s2 v1 v2 =
  let i1 = index s1
      i2 = index s2
   in if i1 == i2
         -- the two subtrees go into the same bucket
         then Node $ new Empty $
                \marr1 =>
                  let sn1 = shrb s1
                      sn2 = shrb s2
                      (_ # marr2) = mwrite i1 marr1 (node2 k1 k2 sn1 sn2 v1 v2)
                   in freeze marr2
         -- the two subtrees go into distinct buckets
         else Node $ new Empty $
                \marr1 =>
                  let (_ # marr2) = mwrite i1 marr1 (Leaf k1 v1)
                      (_ # marr3) = mwrite i2 marr2 (Leaf k2 v2)
                   in freeze marr3

-- k  : key
-- s  : remaining bit string
-- sh : number of bits shifed so far
-- v  : value
insert' : (k,s,sh : Bits32) -> (v : a) -> IntMap a -> IntMap a
insert' k _ _  v Empty     = Leaf k v
insert' k s sh v (Node cs) =
  Node $ mod s cs (insert' k (shrb s) (sh + bits) v)
insert' k s sh v (Leaf k2 v2)    =
  if k == k2 then Leaf k v else node2 k k2 s (shr k2 sh) v v2

-- k  : key
-- s  : remaining bit string
-- sh : number of bits shifted so far
-- v  : value
insertW' :  (k,s,sh : Bits32)
         -> (f : a -> a -> a)
         -> (v : a)
         -> IntMap a
         -> IntMap a
insertW' k _ _  _ v Empty     = Leaf k v
insertW' k s sh f v (Node cs) =
  Node $ mod s cs (insertW' k (shrb s) (sh + bits) f v)
insertW' k s sh f v (Leaf k2 v2)    =
  if k == k2 then Leaf k (f v v2) else node2 k k2 s (shr k2 sh) v v2

export %inline
insert : (key : Bits32) -> (v : a) -> IntMap a -> IntMap a
insert k = insert' k k 0

export %inline
insertWith :  (f : a -> a -> a)
           -> (key : Bits32)
           -> (v : a)
           -> IntMap a
           -> IntMap a
insertWith f k = insertW' k k 0 f

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
toList Empty      = []
toList (Leaf k v) = [(k,v)]
toList (Node c)   = foldr (\m,l => toList (assert_smaller c m) ++ l) Nil c


--------------------------------------------------------------------------------
--          Accessing Values
--------------------------------------------------------------------------------

-- k : key, s : remaining bit string, v : value
lookup' : (k,s : Bits32) -> (map : IntMap a) -> Maybe a
lookup' _ _ Empty       = Nothing
lookup' k _ (Leaf k2 v) = if k == k2 then Just v else Nothing
lookup' k s (Node cs)   = lookup' k (shrb s) (get s cs)

export %inline
lookup : (key : Bits32) -> (map : IntMap a) -> Maybe a
lookup k = lookup' k k

export
mapWithKey : (f : Bits32 -> a -> b) -> IntMap a -> IntMap b
mapWithKey _ Empty      = Empty
mapWithKey f (Leaf k v) = Leaf k $ f k v
mapWithKey f (Node cs)  = assert_total $ Node $ map (mapWithKey f) cs

--------------------------------------------------------------------------------
--          Interfaces
--------------------------------------------------------------------------------

export
Eq a => Eq (IntMap a) where
  (==) = (==) `on` IntMap.toList

export
Show a => Show (IntMap a) where
  showPrec p m = showCon p "fromList" $ showArg (IntMap.toList m)

export %inline
Functor IntMap where
  map f = mapWithKey (const f)
