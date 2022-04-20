module Data.BitMap

%default total

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

public export
Key : Type
Key = Bits64

%inline
mask : Bits64 -> Bits64
mask k = prim__and_Bits64 k 3

%inline %tcinline
shr2 : Bits64 -> Bits64
shr2 k = assert_smaller k $ prim__shr_Bits64 k 2

%inline
shl2 : Bits64 -> Bits64
shl2 k = prim__shl_Bits64 k 2

--------------------------------------------------------------------------------
--          BitMap
--------------------------------------------------------------------------------

export
data BitMap : Type -> Type where
  Empty  : BitMap a
  Leaf   : (v : a) -> BitMap a
  Branch : (b0,b1,b2,b3 : BitMap a) -> BitMap a

--------------------------------------------------------------------------------
--          Inspecting IntMaps
--------------------------------------------------------------------------------

export
isEmpty : BitMap v -> Bool
isEmpty Empty = True
isEmpty _     = False

export
nonEmpty : BitMap v -> Bool
nonEmpty Empty = False
nonEmpty _     = True

export
lookup : (k : Key) -> BitMap a -> Maybe a
lookup 0 (Leaf v) = Just v
lookup k (Branch b0 b1 b2 b3) = case mask k of
  0 => lookup (shr2 k) b0
  1 => lookup (shr2 k) b1
  2 => lookup (shr2 k) b2
  _ => lookup (shr2 k) b3
lookup _ _ = Nothing

export
pairs : BitMap v -> List (Key,v)
pairs = go 1 0
  where go : Bits64 -> Key -> BitMap v ->  List (Key,v)
        go p k Empty = []
        go p k (Leaf x) = [(k,x)]
        go p k (Branch b0 b1 b2 b3) =
          let p2 = shl2 p
           in go p2 k           b0 ++
              go p2 (k + p * 1) b1 ++
              go p2 (k + p * 2) b2 ++
              go p2 (k + p * 3) b3

export
foldlKV : (acc -> Key -> v -> acc) -> acc -> BitMap v -> acc
foldlKV f = go 1 0
  where go : Bits64 -> Key -> acc -> BitMap v ->  acc
        go p k x0 (Branch b0 b1 b2 b3) =
          let p2 = shl2 p
              x1 = go p2 k           x0 b0
              x2 = go p2 (k + p * 1) x1 b1
              x3 = go p2 (k + p * 2) x2 b2
           in go p2 (k + p * 3) x3 b3
        go p k x Empty    = x
        go p k x (Leaf y) = f x k y

||| Gets the keys of the map.
export
keys : BitMap v -> List Key
keys = map fst . pairs

export
values : BitMap v -> List v
values = map snd . pairs

--------------------------------------------------------------------------------
--          Creating IntMaps
--------------------------------------------------------------------------------

export
empty : BitMap v
empty = Empty

public export
singleton : (k : Key) -> (v : a) -> BitMap a
singleton 0 v = Leaf v
singleton k v = case mask k of
  0 => Branch (singleton (shr2 k) v) Empty Empty Empty
  1 => Branch Empty (singleton (shr2 k) v) Empty Empty
  2 => Branch Empty Empty (singleton (shr2 k) v) Empty
  _ => Branch Empty Empty Empty (singleton (shr2 k) v)

branch : (t0,t1,t2,t3 : BitMap a) -> BitMap a
branch Empty Empty Empty Empty = Empty
branch t0    t1    t2    t3    = Branch t0 t1 t2 t3

--------------------------------------------------------------------------------
--          Insert and Update
--------------------------------------------------------------------------------

insertAtLeaf : (k : Key) -> (v1,v2 : a) -> BitMap a
insertAtLeaf 0 v1 v2 = Leaf v1
insertAtLeaf k v1 v2 = case mask k of
  0 => Branch (insertAtLeaf (shr2 k) v1 v2) Empty Empty Empty
  1 => Branch (Leaf v2) (singleton (shr2 k) v1) Empty Empty
  2 => Branch (Leaf v2) Empty (singleton (shr2 k) v1) Empty
  _ => Branch (Leaf v2) Empty Empty (singleton (shr2 k) v1)

export
insert : (k : Key) -> (v : a) -> BitMap a -> BitMap a
insert k v (Branch b0 b1 b2 b3) = case mask k of
  0 => Branch (insert (shr2 k) v b0) b1 b2 b3
  1 => Branch b0 (insert (shr2 k) v b1) b2 b3
  2 => Branch b0 b1 (insert (shr2 k) v b2) b3
  _ => Branch b0 b1 b2 (insert (shr2 k) v b3)
insert k v (Leaf v2) = insertAtLeaf k v v2
insert k v Empty     = singleton k v

export
fromList : List (Key,v) -> BitMap v
fromList = foldl (\m,(k,v) => insert k v m) empty

insertAtLeafWith : (f : a -> a -> a) -> (k : Key) -> (v1,v2 : a) -> BitMap a
insertAtLeafWith f 0 v1 v2 = Leaf $ f v1 v2
insertAtLeafWith f k v1 v2 = case mask k of
  0 => Branch (insertAtLeafWith f (shr2 k) v1 v2) Empty Empty Empty
  1 => Branch (Leaf v2) (singleton (shr2 k) v1) Empty Empty
  2 => Branch (Leaf v2) Empty (singleton (shr2 k) v1) Empty
  _ => Branch (Leaf v2) Empty Empty (singleton (shr2 k) v1)

export
insertWith : (a -> a -> a) -> (k : Key) -> (v : a) -> BitMap a -> BitMap a
insertWith f k v (Branch b0 b1 b2 b3) = case mask k of
  0 => Branch (insertWith f (shr2 k) v b0) b1 b2 b3
  1 => Branch b0 (insertWith f (shr2 k) v b1) b2 b3
  2 => Branch b0 b1 (insertWith f (shr2 k) v b2) b3
  _ => Branch b0 b1 b2 (insertWith f (shr2 k) v b3)
insertWith f k v (Leaf v2) = insertAtLeafWith f k v v2
insertWith f k v Empty     = singleton k v

export
update : (k : Key) -> (f : a -> a) -> BitMap a -> BitMap a
update 0 f (Leaf v) = Leaf $ f v
update k f (Branch b0 b1 b2 b3) = case mask k of
  0 => Branch (update (shr2 k) f b0) b1 b2 b3
  1 => Branch b0 (update (shr2 k) f b1) b2 b3
  2 => Branch b0 b1 (update (shr2 k) f b2) b3
  _ => Branch b0 b1 b2 (update (shr2 k) f b3)
update _ _ t = t

union0 : a -> BitMap a -> BitMap a
union0 x Empty = Leaf x
union0 x (Leaf v) = Leaf x
union0 x (Branch b0 b1 b2 b3) = Branch (union0 x b0) b1 b2 b3

export
union : BitMap a -> BitMap a -> BitMap a
union (Branch b0 b1 b2 b3) (Branch c0 c1 c2 c3) =
  Branch (union b0 c0) (union b1 c1) (union b2 c2) (union b3 c3)
union (Branch b0 b1 b2 b3) (Leaf v) = Branch (union0 v b0) b1 b2 b3
union (Leaf v) (Branch b0 b1 b2 b3) = Branch (union0 v b0) b1 b2 b3
union (Leaf v) (Leaf _)             = Leaf v
union Empty y = y
union x Empty = x

export
delete : (k : Key) -> BitMap a -> BitMap a
delete 0 (Leaf v) = Empty
delete k (Branch b0 b1 b2 b3) = case mask k of
  0 => branch (delete (shr2 k) b0) b1 b2 b3
  1 => branch b0 (delete (shr2 k) b1) b2 b3
  2 => branch b0 b1 (delete (shr2 k) b2) b3
  _ => branch b0 b1 b2 (delete (shr2 k) b3)
delete k m = m

--------------------------------------------------------------------------------
--          Decomposing IntMaps
--------------------------------------------------------------------------------

public export
data DecompAt : Type -> Type where
  NoMatchAt : DecompAt a
  MatchAt   : (v : a) -> (rem : BitMap a) -> DecompAt a

export
decompAt : (k : Key) -> BitMap a -> DecompAt a
decompAt 0 (Leaf v) = MatchAt v Empty
decompAt k (Branch b0 b1 b2 b3) = case mask k of
  0 => case decompAt (shr2 k) b0 of
    MatchAt v rem => MatchAt v (branch rem b1 b2 b3)
    NoMatchAt     => NoMatchAt
  1 => case decompAt (shr2 k) b1 of
    MatchAt v rem => MatchAt v (branch b0 rem b2 b3)
    NoMatchAt     => NoMatchAt
  2 => case decompAt (shr2 k) b2 of
    MatchAt v rem => MatchAt v (branch b0 b1 rem b3)
    NoMatchAt     => NoMatchAt
  _ => case decompAt (shr2 k) b3 of
    MatchAt v rem => MatchAt v (branch b0 b1 b2 rem)
    NoMatchAt     => NoMatchAt
decompAt _ _ = NoMatchAt

public export
data Decomp : Type -> Type where
  NoMatch : Decomp a
  Match   : (k : Key) -> (v : a) -> (rem : BitMap a) -> Decomp a

export
decomp : BitMap a -> Decomp a
decomp (Leaf v) = Match 0 v Empty
decomp (Branch b0 b1 b2 b3) = case decomp b0 of
  (Match k v rem) => Match (shl2 k) v (branch rem b1 b2 b3)
  NoMatch           => case decomp b1 of
    (Match k v rem) => Match (shl2 k + 1) v (branch b0 rem b2 b3)
    NoMatch           => case decomp b2 of
      (Match k v rem) => Match (shl2 k + 2) v (branch b0 b1 rem b3)
      NoMatch           => case decomp b3 of
        (Match k v rem) => Match (shl2 k + 3) v (branch b0 b1 b2 rem)
        NoMatch           => NoMatch

decomp Empty = NoMatch

--------------------------------------------------------------------------------
--          Interfaces
--------------------------------------------------------------------------------

export
Eq v => Eq (BitMap v) where
  (==) = (==) `on` pairs

export
Show v => Show (BitMap v) where
  showPrec p m = showCon p "fromList" $ showArg (pairs m)

export
Functor BitMap where
  map _ Empty                = Empty
  map f (Leaf v)             = Leaf $ f v
  map f (Branch b0 b1 b2 b3) =
    Branch (map f b0) (map f b1) (map f b2) (map f b3)

export
Foldable BitMap where
  foldr _ acc Empty = acc
  foldr f acc (Leaf v) = f v acc
  foldr f acc (Branch b0 b1 b2 b3) =
    foldr f (foldr f (foldr f (foldr f acc b3) b2 ) b1) b0

  foldl _ acc Empty = acc
  foldl f acc (Leaf v) = f acc v
  foldl f acc (Branch b0 b1 b2 b3) =
    foldl f (foldl f (foldl f (foldl f acc b0) b1 ) b2) b3

  foldMap _ Empty = neutral
  foldMap f (Leaf v) = f v
  foldMap f (Branch b0 b1 b2 b3) =
    foldMap f b0 <+> foldMap f b1 <+> foldMap f b2 <+> foldMap f b3

  foldlM _ acc Empty    = pure acc
  foldlM f acc (Leaf v) = f acc v
  foldlM f acc (Branch b0 b1 b2 b3) = do
    acc1 <- foldlM f acc  b0
    acc2 <- foldlM f acc1 b1
    acc3 <- foldlM f acc2 b2
    foldlM f acc3 b3

  null m  = isEmpty m

export
Traversable BitMap where
  traverse f Empty = pure Empty
  traverse f (Leaf v) = Leaf <$> f v
  traverse f (Branch b0 b1 b2 b3) =
    [| Branch (traverse f b0)
              (traverse f b1)
              (traverse f b2)
              (traverse f b3) |]
