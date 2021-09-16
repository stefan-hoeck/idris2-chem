module Data.IntMap

import Data.DPair
import Data.Maybe

%default total

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

private %inline
bits : Bits32
bits = 2

private %inline
mask : Bits32
mask = 3

infixl 8 >>
infixl 7 .&.

private %inline
(.&.) : Bits32 -> Bits32 -> Bits32
(.&.) = prim__and_Bits32

private %inline
(>>) : Bits32 -> Bits32 -> Bits32
(>>) = prim__shr_Bits32

--------------------------------------------------------------------------------
--          Datatype
--------------------------------------------------------------------------------

export
data IntMap : (a : Type) -> Type where
  Empty :  IntMap a
  Leaf  :  (key : Bits32) -> (value : a) -> IntMap a
  Node  :  (c0 : IntMap a)
        -> (c1 : IntMap a)
        -> (c2 : IntMap a)
        -> (c3 : IntMap a)
        -> IntMap a

||| True, if the `IntMap` is empty
export
isEmpty : IntMap a -> Bool
isEmpty Empty = True
isEmpty _     = False

||| True, if the `IntMap` is non-empty
export
nonEmpty : IntMap a -> Bool
nonEmpty = not . isEmpty

--------------------------------------------------------------------------------
--          Updating Nodes
--------------------------------------------------------------------------------

-- View for the `Node` part of a map.
-- This allows us to conveniently update certain positions
-- of a node (see `setNode`).
-- An alternative would be to use a record
-- wrapper, but this would add an additional layer of constructors.
-- Instead, we use an erased proof that the given `IntMap` is
-- actually a `Node`, and - in case we need to write several
-- values as in `node2` - we return an erased proof that
-- the result is again a `Node`, by wrapping the result in
-- a `Subset`
data IsNode : (map : IntMap a) -> Type where
  ItIsNode : IsNode (Node c0 c1 c2 c3)

-- Alias for a `IntMap` that is a `Node`
NonLeaf : (a : Type) -> Type
NonLeaf a = Subset (IntMap a) IsNode

-- Wraps a single `IntMap a` in a `Node` at the given position.
node1 : Bits32 -> IntMap a -> NonLeaf a
node1 0 m = Element (Node m Empty Empty Empty) ItIsNode
node1 1 m = Element (Node Empty m Empty Empty) ItIsNode
node1 2 m = Element (Node Empty Empty m Empty) ItIsNode
node1 _ m = Element (Node Empty Empty Empty m) ItIsNode

-- convenience method for updating a given position
-- in a `Node`.
setNode :  Bits32 -> NonLeaf a -> IntMap a -> NonLeaf a
setNode k (Element (Node c0 c1 c2 c3) _) m = case k of
  0 => Element (Node m c1 c2 c3) ItIsNode
  1 => Element (Node c0 m c2 c3) ItIsNode
  2 => Element (Node c0 c1 m c3) ItIsNode
  _ => Element (Node c0 c1 c2 m) ItIsNode

--------------------------------------------------------------------------------
--          Trivial Constructors
--------------------------------------------------------------------------------

||| Creates a new empty `IntMap`
export %inline
empty : IntMap a
empty = Empty

export %inline
singleton : (key : Bits32) -> (value : a) -> IntMap a
singleton = Leaf

--------------------------------------------------------------------------------
--          Lookup
--------------------------------------------------------------------------------

lookup' : (k,s : Bits32) -> IntMap a -> Maybe a
lookup' k s Empty              = Nothing
lookup' k s (Leaf k2 v)        = if k == k2 then Just v else Nothing
lookup' k s (Node c0 c1 c2 c3) =
  case s .&. mask of
    0 => lookup' k (s >> bits) c0
    1 => lookup' k (s >> bits) c1
    2 => lookup' k (s >> bits) c2
    _ => lookup' k (s >> bits) c3

export %inline
lookup : (key : Bits32) -> (map : IntMap a) -> Maybe a
lookup key = lookup' key key

export %inline
isKey : (key : Bits32) -> IntMap a -> Bool
isKey k = isJust . lookup k

--------------------------------------------------------------------------------
--          Insert
--------------------------------------------------------------------------------

-- In case we delete something from our map, we want to make sure
-- that no nodes with only empty children linger around.
-- We therefore use this as a constructor for `Node` during
-- updates.
node : IntMap a -> IntMap a -> IntMap a -> IntMap a -> IntMap a
node Empty Empty Empty Empty = Empty
node c0 c1 c2 c3 = Node c0 c1 c2 c3

-- create a node containing two key-value pairs.
-- we have already verified that k1 /= k2.
node2 : (k1,k2,s1,s2 : Bits32) -> (v1,v2 : a) -> IntMap a
node2 k1 k2 s1 s2 v1 v2 =
  let m1 = s1 .&. mask
      m2 = s2 .&. mask
   in if m1 == m2
         then
           let s1n = assert_smaller s1 (s1 >> bits)
               s2n = s2 >> bits
            in fst $ node1 m1 (node2 k1 k2 s1n s2n v1 v2)
         else
           let n1 = node1 m1 (Leaf k1 v1)
            in fst $ setNode m2 n1 (Leaf k2 v2)

-- k  : key
-- s  : remaining bit string
-- sh : number of bits shifted so far
--
-- Profiling showed that this performs well enough to make it
-- our Jack of all trades function for inserting, updating,
-- and deleting.
update' :  (k,s,sh : Bits32)
        -> (f : Maybe a -> Maybe a)
        -> IntMap a
        -> IntMap a
update' k _ _  f Empty = maybe Empty (Leaf k) $ f Nothing

update' k s sh f (Leaf k2 v2) =
  if k == k2 then maybe Empty (Leaf k) $ f (Just v2)
  else maybe (Leaf k2 v2) (\v => node2 k k2 s (k2 >> sh) v v2) $ f Nothing

update' k s sh f (Node c0 c1 c2 c3) =
  let s2  = s >> bits
      sh2 = sh + bits
   in case s .&. mask of
        0 => node (update' k s2 sh2 f c0) c1 c2 c3
        1 => node c0 (update' k s2 sh2 f c1) c2 c3
        2 => node c0 c1 (update' k s2 sh2 f c2) c3
        _ => node c0 c1 c2 (update' k s2 sh2 f c3)

||| General function for updating a value at the
||| given position. `insert`, `insertWith`, `delete`, and `update`
||| are all implemented via this function.
export %inline
gupdate : (k : Bits32) -> (f : Maybe a -> Maybe a) -> IntMap a -> IntMap a
gupdate k = update' k k 0

||| Update the value at the given position by passing it to `f`.
||| Leaves the map unchanged if no value at the given key is found.
export %inline
update : (k : Bits32) -> (f : a -> a) -> IntMap a -> IntMap a
update k = gupdate k . map

export %inline
insertOrUpdate :  (k : Bits32)
               -> (v : Lazy a)
               -> (f : Lazy (a -> a))
               -> IntMap a
               -> IntMap a
insertOrUpdate k v f = gupdate k (Just . maybe v f)

||| Insert `v` at the given position. An value already existing
||| at that position is siletly replaces by `v`.
export %inline
insert : (k : Bits32) -> (v : a) -> IntMap a -> IntMap a
insert k v = gupdate k (const $ Just v) 

||| Insert `v` at the given position. An value `v2` already existing
||| at that position replaced by `f v v2`.
export %inline
insertWith :  (f : a -> a -> a)
           -> (k : Bits32)
           -> (v : a)
           -> IntMap a
           -> IntMap a
insertWith f k v = gupdate k (Just . maybe v (f v))

||| Delete the entry at the given position.
export %inline
delete : (k : Bits32) -> IntMap a -> IntMap a
delete k = gupdate k (const Nothing)

export
pairs : IntMap a -> List (Bits32, a)
pairs Empty              = []
pairs (Leaf k v)         = [(k,v)]
pairs (Node c0 c1 c2 c3) = pairs c0 ++ pairs c1 ++ pairs c2 ++ pairs c3

export
fromFoldable : Foldable f => f (Bits32, a) -> IntMap a
fromFoldable = foldl (\m,(k,v) => insert k v m) Empty

export %inline
fromList : List (Bits32, a) -> IntMap a
fromList = fromFoldable

--------------------------------------------------------------------------------
--          Interfaces
--------------------------------------------------------------------------------

export
Eq a => Eq (IntMap a) where
  (==) = (==) `on` pairs

export
Show a => Show (IntMap a) where
  showPrec p m = showCon p "fromList" $ showArg (pairs m)

export
Functor IntMap where
  map f Empty              = Empty
  map f (Leaf k v)         = Leaf k $ f v
  map f (Node c0 c1 c2 c3) = Node (map f c0) (map f c1) (map f c2) (map f c3)

foldlImpl : (a -> e -> a) -> a -> IntMap e -> a
foldlImpl f x Empty              = x
foldlImpl f x (Leaf k v)         = f x v
foldlImpl f x (Node c0 c1 c2 c3) =
  foldlImpl f (foldlImpl f (foldlImpl f (foldlImpl f x c0) c1) c2) c3

foldrImpl : (e -> a -> a) -> a -> IntMap e -> a
foldrImpl f x Empty              = x
foldrImpl f x (Leaf k v)         = f v x
foldrImpl f x (Node c0 c1 c2 c3) =
  foldrImpl f (foldrImpl f (foldrImpl f (foldrImpl f x c3) c2) c1) c0

foldMapImpl : Monoid m => (e -> m) -> IntMap e -> m
foldMapImpl _ Empty              = neutral
foldMapImpl f (Leaf _ v)         = f v
foldMapImpl f (Node c0 c1 c2 c3) =
  foldMapImpl f c0 <+>
  foldMapImpl f c1 <+>
  foldMapImpl f c2 <+>
  foldMapImpl f c3

foldlMImpl : Monad m => (a -> e -> m a) -> a -> IntMap e -> m a
foldlMImpl _ x  Empty      = pure x
foldlMImpl f x  (Leaf _ v) = f x v
foldlMImpl f x0 (Node c0 c1 c2 c3) = do
  x1 <- foldlMImpl f x0 c0
  x2 <- foldlMImpl f x1 c1
  x3 <- foldlMImpl f x2 c2
  foldlMImpl f x3 c3

||| Note: The order of values in the map is an implementation
|||       detail. Keep this in mind, when using the `Foldable`
|||       interface. It is best to use it mostly with commutative
|||       accumulation functions.
export %inline
Foldable IntMap where
  foldr   = foldrImpl
  foldl   = foldlImpl
  foldMap = foldMapImpl
  foldlM  = foldlMImpl
  null m  = isEmpty m

export
Traversable IntMap where
  traverse _ Empty      = pure Empty
  traverse f (Leaf k v) = Leaf k <$> f v
  traverse f (Node c0 c1 c2 c3) =
    [| Node (traverse f c0) (traverse f c1) (traverse f c2) (traverse f c3) |]
