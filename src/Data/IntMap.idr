module Data.IntMap

public export
Key : Type
Key = Bits64

--------------------------------------------------------------------------------
--          Primitives
--------------------------------------------------------------------------------

%inline
eq : Key -> Key -> Int
eq = prim__eq_Bits64

lte : Key -> Key -> Int
lte = prim__lte_Bits64

gte : Key -> Key -> Int
gte = prim__gte_Bits64

--------------------------------------------------------------------------------
--          2-3-Tree
--------------------------------------------------------------------------------

data Tree : Nat -> (v : Type) -> Type where
  Leaf : (k : Key) -> v -> Tree Z v
  Branch2 : Tree n v -> Key -> Tree n v -> Tree (S n) v
  Branch3 : Tree n v -> Key -> Tree n v -> Key -> Tree n v -> Tree (S n) v

data InsertRes : Nat -> (v : Type) -> Type where
  I1 : Tree n v -> InsertRes n v
  I2 : Tree n v -> Key -> Tree n v -> InsertRes n v

data DeleteRes : Nat -> (v : Type) -> Type where
  DZ : DeleteRes Z v
  DI : Tree n v -> DeleteRes n v
  DS : Tree n v -> DeleteRes (S n) v

data DecompRes : Nat -> (v : Type) -> Type where
  DecZ : Key -> v -> DecompRes Z v
  DecI : Key -> v -> Tree n v -> DecompRes n v
  DecS : Key -> v -> Tree n v -> DecompRes (S n) v

branch4 :
  Tree n v -> Key ->
  Tree n v -> Key ->
  Tree n v -> Key ->
  Tree n v ->
  Tree (S (S n)) v
branch4 a b c d e f g =
  Branch2 (Branch2 a b c) d (Branch2 e f g)

branch5 :
  Tree n v -> Key ->
  Tree n v -> Key ->
  Tree n v -> Key ->
  Tree n v -> Key ->
  Tree n v ->
  Tree (S (S n)) v
branch5 a b c d e f g h i =
  Branch2 (Branch2 a b c) d (Branch3 e f g h i)

branch6 :
  Tree n v -> Key ->
  Tree n v -> Key ->
  Tree n v -> Key ->
  Tree n v -> Key ->
  Tree n v -> Key ->
  Tree n v ->
  Tree (S (S n)) v
branch6 a b c d e f g h i j k =
  Branch3 (Branch2 a b c) d (Branch2 e f g) h (Branch2 i j k)

branch7 :
  Tree n v -> Key ->
  Tree n v -> Key ->
  Tree n v -> Key ->
  Tree n v -> Key ->
  Tree n v -> Key ->
  Tree n v -> Key ->
  Tree n v ->
  Tree (S (S n)) v
branch7 a b c d e f g h i j k l m =
  Branch3 (Branch3 a b c d e) f (Branch2 g h i) j (Branch2 k l m)

merge1 : Tree n v -> Key -> Tree (S n) v -> Key -> Tree (S n) v -> Tree (S (S n)) v
merge1 a b (Branch2 c d e) f (Branch2 g h i) = branch5 a b c d e f g h i
merge1 a b (Branch2 c d e) f (Branch3 g h i j k) = branch6 a b c d e f g h i j k
merge1 a b (Branch3 c d e f g) h (Branch2 i j k) = branch6 a b c d e f g h i j k
merge1 a b (Branch3 c d e f g) h (Branch3 i j k l m) = branch7 a b c d e f g h i j k l m

merge2 : Tree (S n) v -> Key -> Tree n v -> Key -> Tree (S n) v -> Tree (S (S n)) v
merge2 (Branch2 a b c) d e f (Branch2 g h i) = branch5 a b c d e f g h i
merge2 (Branch2 a b c) d e f (Branch3 g h i j k) = branch6 a b c d e f g h i j k
merge2 (Branch3 a b c d e) f g h (Branch2 i j k) = branch6 a b c d e f g h i j k
merge2 (Branch3 a b c d e) f g h (Branch3 i j k l m) = branch7 a b c d e f g h i j k l m

merge3 : Tree (S n) v -> Key -> Tree (S n) v -> Key -> Tree n v -> Tree (S (S n)) v
merge3 (Branch2 a b c) d (Branch2 e f g) h i = branch5 a b c d e f g h i
merge3 (Branch2 a b c) d (Branch3 e f g h i) j k = branch6 a b c d e f g h i j k
merge3 (Branch3 a b c d e) f (Branch2 g h i) j k = branch6 a b c d e f g h i j k
merge3 (Branch3 a b c d e) f (Branch3 g h i j k) l m = branch7 a b c d e f g h i j k l m

lookupT : Key -> Tree n v -> Maybe v
lookupT k (Leaf k' v) with (eq k k')
    _ | 0 = Nothing
    _ | _ = Just v

lookupT k (Branch2 t1 k' t2) with (lte k k')
    _ | 0 = lookupT k t2
    _ | _ = lookupT k t1

lookupT k (Branch3 t1 k1 t2 k2 t3) with (lte k k1)
  _ | 0 with (lte k k2)
    _ | 0 = lookupT k t3
    _ | _ = lookupT k t2
  _ | _ = lookupT k t1

insertT : Key -> v -> Tree n v -> InsertRes n v
insertT k v t@(Leaf k' v') with (lte k k')
  _ | 0 = I2 t k' (Leaf k v)
  _ | _ with (eq k k')
    _ | 0 = I2 (Leaf k v) k t
    _ | _ = I1 $ Leaf k v

insertT k v (Branch2 t1 k' t2) with (lte k k')
  _ | 0 with (insertT k v t2)
    _ | I1 t2'   = I1 (Branch2 t1 k' t2')
    _ | I2 a b c = I1 (Branch3 t1 k' a b c)
  _ | _ with (insertT k v t1)
    _ | I1 t1'   = I1 (Branch2 t1' k' t2)
    _ | I2 a b c = I1 (Branch3 a b c k' t2)

insertT k v (Branch3 t1 k1 t2 k2 t3) with (lte k k1)
  _ | 0 with (lte k k2)
    _ | 0 with (insertT k v t3)
      _ | I1 t3'   = I1 (Branch3 t1 k1 t2 k2 t3')
      _ | I2 a b c = I2 (Branch2 t1 k1 t2) k2 (Branch2 a b c)
    _ | _ with (insertT k v t2)
      _ | I1 t2'   = I1 (Branch3 t1 k1 t2' k2 t3)
      _ | I2 a b c = I2 (Branch2 t1 k1 a) b (Branch2 c k2 t3)
  _ | _ with (insertT k v t1)
    _ | I1 t1'   = I1 (Branch3 t1' k1 t2 k2 t3)
    _ | I2 a b c = I2 (Branch2 a b c) k1 (Branch2 t2 k2 t3)

insertWithT : (f : v -> v -> v) -> Key -> v -> Tree n v -> InsertRes n v
insertWithT f k v t@(Leaf k' v') with (lte k k')
  _ | 0 = I2 t k' (Leaf k v)
  _ | _ with (eq k k')
    _ | 0 = I2 (Leaf k v) k t
    _ | _ = I1 $ Leaf k (f v v')

insertWithT f k v (Branch2 t1 k' t2) with (lte k k')
  _ | 0 with (insertWithT f k v t2)
    _ | I1 t2'   = I1 (Branch2 t1 k' t2')
    _ | I2 a b c = I1 (Branch3 t1 k' a b c)
  _ | _ with (insertWithT f k v t1)
    _ | I1 t1'   = I1 (Branch2 t1' k' t2)
    _ | I2 a b c = I1 (Branch3 a b c k' t2)

insertWithT f k v (Branch3 t1 k1 t2 k2 t3) with (lte k k1)
  _ | 0 with (lte k k2)
    _ | 0 with (insertWithT f k v t3)
      _ | I1 t3'   = I1 (Branch3 t1 k1 t2 k2 t3')
      _ | I2 a b c = I2 (Branch2 t1 k1 t2) k2 (Branch2 a b c)
    _ | _ with (insertWithT f k v t2)
      _ | I1 t2'   = I1 (Branch3 t1 k1 t2' k2 t3)
      _ | I2 a b c = I2 (Branch2 t1 k1 a) b (Branch2 c k2 t3)
  _ | _ with (insertWithT f k v t1)
    _ | I1 t1'   = I1 (Branch3 t1' k1 t2 k2 t3)
    _ | I2 a b c = I2 (Branch2 a b c) k1 (Branch2 t2 k2 t3)

updateT : (f : v -> v) -> Key -> Tree n v -> Tree n v
updateT f k t@(Leaf k' v') with (eq k k')
  _ | 0 = t
  _ | _ = Leaf k' (f v')

updateT f k (Branch2 t1 k' t2) with (lte k k')
  _ | 0 = Branch2 t1 k' (updateT f k t2)
  _ | _ = Branch2 (updateT f k t1) k' t2

updateT f k (Branch3 t1 k1 t2 k2 t3) with (lte k k1)
  _ | 0 with (lte k k2)
    _ | 0 = Branch3 t1 k1 t2 k2 (updateT f k t3)
    _ | _ = Branch3 t1 k1 (updateT f k t2) k2 t3
  _ | _ = Branch3 (updateT f k t1) k1 t2 k2 t3

deleteT : Key -> Tree n v -> DeleteRes n v
deleteT k t@(Leaf k' v) with (eq k k')
  _ | 0 = DI t
  _ | _ = DZ

deleteT k (Branch2 t1 k' t2) with (lte k k')
  _ | 0 with (deleteT k t2)
    _ | DZ   = DS t1
    _ | DI x = DI $ Branch2 t1 k' x
    _ | DS x with (t1)
      _ | Branch2 a b c     = DS $ Branch3 a b c k' x
      _ | Branch3 a b c d e = DI $ branch4 a b c d e k' x
  _ | _ with (deleteT k t1)
    _ | DZ   = DS t2
    _ | DI x = DI $ Branch2 x k' t2
    _ | DS x with (t2)
      _ | Branch2 a b c     = DS $ Branch3 x k' a b c
      _ | Branch3 a b c d e = DI $ branch4 x k' a b c d e

deleteT k (Branch3 t1 k1 t2 k2 t3) {n = S n} with (lte k k1)
  deleteT k (Branch3 t1 k1 t2 k2 t3) {n = S n} | 0 with (lte k k2)
    deleteT k (Branch3 t1 k1 t2 k2 t3) {n = S n} | 0 | 0 with (deleteT k t3)
      deleteT k (Branch3 t1 k1 t2 k2 t3) {n = S Z}     | 0 | 0 | DZ   = DI $ Branch2 t1 k1 t2
      deleteT k (Branch3 t1 k1 t2 k2 t3) {n = S n}     | 0 | 0 | DI x = DI $ Branch3 t1 k1 t2 k2 x
      deleteT k (Branch3 t1 k1 t2 k2 t3) {n = S (S n)} | 0 | 0 | DS x = DI $ merge3 t1 k1 t2 k2 x
    deleteT k (Branch3 t1 k1 t2 k2 t3) {n = S n} | 0 | _ with (deleteT k t2)
      deleteT k (Branch3 t1 k1 t2 k2 t3) {n = S Z}     | 0 | _ | DZ   = DI $ Branch2 t1 k1 t3
      deleteT k (Branch3 t1 k1 t2 k2 t3) {n = S n}     | 0 | _ | DI x = DI $ Branch3 t1 k1 x k2 t3
      deleteT k (Branch3 t1 k1 t2 k2 t3) {n = S (S n)} | 0 | _ | DS x = DI $ merge2 t1 k1 x k2 t3
  deleteT k (Branch3 t1 k1 t2 k2 t3) {n = S n} | _  with (deleteT k t1)
    deleteT k (Branch3 t1 k1 t2 k2 t3) {n = S Z}     | _ | DZ   = DI $ Branch2 t2 k2 t3
    deleteT k (Branch3 t1 k1 t2 k2 t3) {n = S n}     | _ | DI x = DI $ Branch3 x k1 t2 k2 t3
    deleteT k (Branch3 t1 k1 t2 k2 t3) {n = S (S n)} | _ | DS x = DI $ merge1 x k1 t2 k2 t3

decompT : Tree n v -> DecompRes n v
decompT (Leaf k x) = DecZ k x
decompT (Branch2 t1 k1 t2) with (decompT t2)
  _ | DecZ k val   = DecS k val t1
  _ | DecI k val x = DecI k val (Branch2 t1 k1 x)
  _ | DecS k val x with (t1)
    _ | Branch2 a b c     = DecS k val $ Branch3 a b c k1 x
    _ | Branch3 a b c d e = DecI k val $ branch4 a b c d e k1 x
decompT (Branch3 t1 k1 t2 k2 t3) with (decompT t3)
  _ | DecZ k val   = DecI k val (Branch2 t1 k1 t2)
  _ | DecI k val x = DecI k val (Branch3 t1 k1 t2 k2 x)
  _ | DecS k val x = DecI k val $ merge3 t1 k1 t2 k2 x

toListT : Tree n v -> List (Key, v)
toListT (Leaf k x)          = [(k,x)]
toListT (Branch2 x _ y)     = toListT x ++ toListT y
toListT (Branch3 x _ y _ z) = toListT x ++ toListT y ++ toListT z

treeMap : (a -> b) -> Tree n a -> Tree n b
treeMap f (Leaf k x) = Leaf k $ f x
treeMap f (Branch2 x y z) = Branch2 (treeMap f x) y (treeMap f z)
treeMap f (Branch3 x y z w v) =
  Branch3 (treeMap f x) y (treeMap f z) w (treeMap f v)

traverseT : Applicative f => (a -> f b) -> Tree n a -> f (Tree n b)
traverseT g (Leaf k x) = Leaf k <$> g x

traverseT g (Branch2 x y z) =
  (\x2,z2 => Branch2 x2 y z2) <$>
  traverseT g x               <*>
  traverseT g z

traverseT g (Branch3 x y z w v) =
  (\x2,z2,v2 => Branch3 x2 y z2 w v2) <$>
  traverseT g x                       <*>
  traverseT g z                       <*>
  traverseT g v

foldlT : (a -> e -> a) -> a -> Tree n e -> a
foldlT f acc (Leaf k v)          = f acc v
foldlT f acc (Branch2 x _ y)     = foldlT f (foldlT f acc x) y
foldlT f acc (Branch3 x _ y _ z) = foldlT f (foldlT f (foldlT f acc x) y) z 

foldlPT : (a -> Key -> e -> a) -> a -> Tree n e -> a
foldlPT f acc (Leaf k v)          = f acc k v
foldlPT f acc (Branch2 x _ y)     = foldlPT f (foldlPT f acc x) y
foldlPT f acc (Branch3 x _ y _ z) = foldlPT f (foldlPT f (foldlPT f acc x) y) z 

foldrT : (e -> a -> a) -> a -> Tree n e -> a
foldrT f acc (Leaf k v)          = f v acc
foldrT f acc (Branch2 x _ y)     = foldrT f (foldrT f acc y) x
foldrT f acc (Branch3 x _ y _ z) = foldrT f (foldrT f (foldrT f acc z) y) z

foldMapT : Monoid m => (e -> m) -> Tree n e -> m
foldMapT f (Leaf _ v)         = f v
foldMapT f (Branch2 x _ y)    = foldMapT f x <+> foldMapT f y
foldMapT f (Branch3 x _ y _z) = foldMapT f x <+> foldMapT f y <+> foldMapT f z

foldlMT : Monad m => (a -> e -> m a) -> a -> Tree n e -> m a
foldlMT f acc  (Leaf _ v) = f acc v

foldlMT f acc0 (Branch2 x _ y) = do
  acc1 <- foldlMT f acc0 x
  foldlMT f acc1 y

foldlMT f acc0 (Branch3 x _ y _ z) = do
  acc1 <- foldlMT f acc0 x
  acc2 <- foldlMT f acc1 y
  foldlMT f acc2 z

--------------------------------------------------------------------------------
--          IntMap
--------------------------------------------------------------------------------

export
data IntMap : (v : Type) -> Type where
  Empty : IntMap v
  M     : {0 n : Nat} -> Tree n v -> IntMap v

export
isEmpty : IntMap v -> Bool
isEmpty Empty = True
isEmpty _     = False

export
nonEmpty : IntMap v -> Bool
nonEmpty Empty = False
nonEmpty _     = True

export
empty : IntMap v
empty = Empty

export
lookup : (k : Key) -> IntMap v -> Maybe v
lookup _ Empty = Nothing
lookup k (M t) = lookupT k t

export
insert : (k : Key) -> v -> IntMap v -> IntMap v
insert k v Empty = M (Leaf k v)
insert k v (M x) with (insertT k v x)
  _ | I1 y     = M y
  _ | I2 y z w = M $ Branch2 y z w

export
insertWith : (f : v -> v -> v) -> (k : Key) -> v -> IntMap v -> IntMap v
insertWith _ k v Empty = M (Leaf k v)
insertWith f k v (M x) with (insertWithT f k v x)
  _ | I1 y     = M y
  _ | I2 y z w = M $ Branch2 y z w

export
update : (k : Key) -> (f : v -> v) -> IntMap v -> IntMap v
update _ _ Empty = Empty
update k f (M x) = M $ updateT f k x

export
singleton : Key -> v -> IntMap v 
singleton k v = M (Leaf k v)

export
insertFrom : Foldable f => f (Key,v) -> IntMap v -> IntMap v
insertFrom ps m = foldl (\m,(k,x) => insert k x m) m ps

export
delete : Key -> IntMap v -> IntMap v
delete _ Empty = Empty
delete k (M m) with (deleteT k m)
  _ | DZ   = Empty
  _ | DI x = M x
  _ | DS x = M x

export
fromList : List (Key,v) -> IntMap v
fromList = foldl (\m,(k,v) => insert k v m) empty

export
pairs : IntMap v -> List (Key,v)
pairs Empty = []
pairs (M t) = toListT t

||| Gets the keys of the map.
export
keys : IntMap v -> List Key
keys = map fst . pairs

export
values : IntMap v -> List v
values = map snd . pairs

export
foldlKV : (acc -> Key -> el -> acc) -> acc -> IntMap el -> acc
foldlKV _ acc Empty = acc
foldlKV f acc (M t) = foldlPT f acc t

public export
data Decomp : (v : Type) -> Type where
  Done : Decomp v
  Dec  : Key -> v -> IntMap v -> Decomp v

export
decomp : IntMap v -> Decomp v
decomp Empty = Done
decomp (M x) = case decompT x of
  DecZ k val   => Dec k val Empty
  DecI k val t => Dec k val (M t)
  DecS k val t => Dec k val (M t)

export
Eq v => Eq (IntMap v) where
  (==) = (==) `on` pairs

export
Show v => Show (IntMap v) where
  showPrec p m = showCon p "fromList" $ showArg (pairs m)

export
Functor IntMap where
  map _ Empty = Empty
  map f (M t) = M $ treeMap f t

export
Foldable IntMap where
  foldr _ acc Empty = acc
  foldr f acc (M t) = foldrT f acc t

  foldl _ acc Empty = acc
  foldl f acc (M t) = foldlT f acc t

  foldMap _ Empty = neutral
  foldMap f (M t) = foldMapT f t

  foldlM _ acc Empty = pure acc
  foldlM f acc (M t) = foldlMT f acc t

  null m  = isEmpty m

export
Traversable IntMap where
  traverse _ Empty = pure Empty
  traverse f (M t) = M <$> traverseT f t
