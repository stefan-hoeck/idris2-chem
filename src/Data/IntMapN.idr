module Data.IntMapN

public export
Key : Type
Key = Bits64

%inline
eq : Key -> Key -> Int
eq = prim__eq_Bits64

lte : Key -> Key -> Int
lte = prim__lte_Bits64

gte : Key -> Key -> Int
gte = prim__gte_Bits64

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

treeLookup : Key -> Tree n v -> Maybe v
treeLookup k (Leaf k' v) with (eq k k')
    _ | 0 = Nothing
    _ | _ = Just v

treeLookup k (Branch2 t1 k' t2) with (lte k k')
    _ | 0 = treeLookup k t2
    _ | _ = treeLookup k t1

treeLookup k (Branch3 t1 k1 t2 k2 t3) with (lte k k1)
  _ | 0 with (lte k k2)
    _ | 0 = treeLookup k t3
    _ | _ = treeLookup k t2
  _ | _ = treeLookup k t1

insert' : Key -> v -> Tree n v -> InsertRes n v
insert' k v t@(Leaf k' v') with (lte k k')
  _ | 0 = I2 t k' (Leaf k v)
  _ | _ with (eq k k')
    _ | 0 = I2 (Leaf k v) k t
    _ | _ = I1 $ Leaf k v

insert' k v (Branch2 t1 k' t2) with (lte k k')
  _ | 0 with (insert' k v t2)
    _ | I1 t2'   = I1 (Branch2 t1 k' t2')
    _ | I2 a b c = I1 (Branch3 t1 k' a b c)
  _ | _ with (insert' k v t1)
    _ | I1 t1'   = I1 (Branch2 t1' k' t2)
    _ | I2 a b c = I1 (Branch3 a b c k' t2)

insert' k v (Branch3 t1 k1 t2 k2 t3) with (lte k k1)
  _ | 0 with (lte k k2)
    _ | 0 with (insert' k v t3)
      _ | I1 t3'   = I1 (Branch3 t1 k1 t2 k2 t3')
      _ | I2 a b c = I2 (Branch2 t1 k1 t2) k2 (Branch2 a b c)
    _ | _ with (insert' k v t2)
      _ | I1 t2'   = I1 (Branch3 t1 k1 t2' k2 t3)
      _ | I2 a b c = I2 (Branch2 t1 k1 a) b (Branch2 c k2 t3)
  _ | _ with (insert' k v t1)
    _ | I1 t1'   = I1 (Branch3 t1' k1 t2 k2 t3)
    _ | I2 a b c = I2 (Branch2 a b c) k1 (Branch2 t2 k2 t3)

insertWith' : (f : v -> v -> v) -> Key -> v -> Tree n v -> InsertRes n v
insertWith' f k v t@(Leaf k' v') with (lte k k')
  _ | 0 = I2 t k' (Leaf k v)
  _ | _ with (eq k k')
    _ | 0 = I2 (Leaf k v) k t
    _ | _ = I1 $ Leaf k (f v v')

insertWith' f k v (Branch2 t1 k' t2) with (lte k k')
  _ | 0 with (insertWith' f k v t2)
    _ | I1 t2'   = I1 (Branch2 t1 k' t2')
    _ | I2 a b c = I1 (Branch3 t1 k' a b c)
  _ | _ with (insertWith' f k v t1)
    _ | I1 t1'   = I1 (Branch2 t1' k' t2)
    _ | I2 a b c = I1 (Branch3 a b c k' t2)

insertWith' f k v (Branch3 t1 k1 t2 k2 t3) with (lte k k1)
  _ | 0 with (lte k k2)
    _ | 0 with (insertWith' f k v t3)
      _ | I1 t3'   = I1 (Branch3 t1 k1 t2 k2 t3')
      _ | I2 a b c = I2 (Branch2 t1 k1 t2) k2 (Branch2 a b c)
    _ | _ with (insertWith' f k v t2)
      _ | I1 t2'   = I1 (Branch3 t1 k1 t2' k2 t3)
      _ | I2 a b c = I2 (Branch2 t1 k1 a) b (Branch2 c k2 t3)
  _ | _ with (insertWith' f k v t1)
    _ | I1 t1'   = I1 (Branch3 t1' k1 t2 k2 t3)
    _ | I2 a b c = I2 (Branch2 a b c) k1 (Branch2 t2 k2 t3)

update' : (f : v -> v) -> Key -> Tree n v -> Tree n v
update' f k t@(Leaf k' v') with (eq k k')
  _ | 0 = t
  _ | _ = Leaf k' (f v')

update' f k (Branch2 t1 k' t2) with (lte k k')
  _ | 0 = Branch2 t1 k' (update' f k t2)
  _ | _ = Branch2 (update' f k t1) k' t2

update' f k (Branch3 t1 k1 t2 k2 t3) with (lte k k1)
  _ | 0 with (lte k k2)
    _ | 0 = Branch3 t1 k1 t2 k2 (update' f k t3)
    _ | _ = Branch3 t1 k1 (update' f k t2) k2 t3
  _ | _ = Branch3 (update' f k t1) k1 t2 k2 t3

delete' : Key -> Tree n v -> DeleteRes n v
delete' k t@(Leaf k' v) with (eq k k')
  _ | 0 = DI t
  _ | _ = DZ

delete' k (Branch2 t1 k' t2) with (lte k k')
  _ | 0 with (delete' k t2)
    _ | DZ   = DS t1
    _ | DI x = DI $ Branch2 t1 k' x
    _ | DS x with (t1)
      _ | Branch2 a b c     = DS $ Branch3 a b c k' x
      _ | Branch3 a b c d e = DI $ branch4 a b c d e k' x
  _ | _ with (delete' k t1)
    _ | DZ   = DS t2
    _ | DI x = DI $ Branch2 x k' t2
    _ | DS x with (t2)
      _ | Branch2 a b c     = DS $ Branch3 x k' a b c
      _ | Branch3 a b c d e = DI $ branch4 x k' a b c d e

delete' k (Branch3 t1 k1 t2 k2 t3) {n = S n} with (lte k k1)
  delete' k (Branch3 t1 k1 t2 k2 t3) {n = S n} | 0 with (lte k k2)
    delete' k (Branch3 t1 k1 t2 k2 t3) {n = S n} | 0 | 0 with (delete' k t3)
      delete' k (Branch3 t1 k1 t2 k2 t3) {n = S Z}     | 0 | 0 | DZ   = DI $ Branch2 t1 k1 t2
      delete' k (Branch3 t1 k1 t2 k2 t3) {n = S n}     | 0 | 0 | DI x = DI $ Branch3 t1 k1 t2 k2 x
      delete' k (Branch3 t1 k1 t2 k2 t3) {n = S (S n)} | 0 | 0 | DS x = DI $ merge3 t1 k1 t2 k2 x
    delete' k (Branch3 t1 k1 t2 k2 t3) {n = S n} | 0 | _ with (delete' k t2)
      delete' k (Branch3 t1 k1 t2 k2 t3) {n = S Z}     | 0 | _ | DZ   = DI $ Branch2 t1 k1 t3
      delete' k (Branch3 t1 k1 t2 k2 t3) {n = S n}     | 0 | _ | DI x = DI $ Branch3 t1 k1 x k2 t3
      delete' k (Branch3 t1 k1 t2 k2 t3) {n = S (S n)} | 0 | _ | DS x = DI $ merge2 t1 k1 x k2 t3
  delete' k (Branch3 t1 k1 t2 k2 t3) {n = S n} | _  with (delete' k t1)
    delete' k (Branch3 t1 k1 t2 k2 t3) {n = S Z}     | _ | DZ   = DI $ Branch2 t2 k2 t3
    delete' k (Branch3 t1 k1 t2 k2 t3) {n = S n}     | _ | DI x = DI $ Branch3 x k1 t2 k2 t3
    delete' k (Branch3 t1 k1 t2 k2 t3) {n = S (S n)} | _ | DS x = DI $ merge1 x k1 t2 k2 t3

treeToList : Tree n v -> List (Key, v)
treeToList = treeToList' (:: [])
  where
    treeToList' : ((Key,v) -> List (Key,v)) -> Tree k v -> List (Key,v)
    treeToList' cont (Leaf k v) = cont (k, v)
    treeToList' cont (Branch2 t1 _ t2)      = treeToList' (:: treeToList' cont t2) t1
    treeToList' cont (Branch3 t1 _ t2 _ t3) = treeToList' (:: treeToList' (:: treeToList' cont t3) t2) t1

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
lookup k (M t) = treeLookup k t

export
insert : (k : Key) -> v -> IntMap v -> IntMap v
insert k v Empty = M (Leaf k v)
insert k v (M x) with (insert' k v x)
  _ | I1 y     = M y
  _ | I2 y z w = M $ Branch2 y z w

export
insertWith : (f : v -> v -> v) -> (k : Key) -> v -> IntMap v -> IntMap v
insertWith _ k v Empty = M (Leaf k v)
insertWith f k v (M x) with (insertWith' f k v x)
  _ | I1 y     = M y
  _ | I2 y z w = M $ Branch2 y z w

export
update : (k : Key) -> (f : v -> v) -> IntMap v -> IntMap v
update _ _ Empty = Empty
update k f (M x) = M $ update' f k x

export
singleton : Key -> v -> IntMap v 
singleton k v = M (Leaf k v)

export
insertFrom : Foldable f => f (Key,v) -> IntMap v -> IntMap v
insertFrom ps m = foldl (\m,(k,x) => insert k x m) m ps

export
delete : Key -> IntMap v -> IntMap v
delete _ Empty = Empty
delete k (M m) with (delete' k m)
  _ | DZ   = Empty
  _ | DI x = M x
  _ | DS x = M x

export
fromList : List (Key,v) -> IntMap v
fromList = foldl (\m,(k,v) => insert k v m) empty

export
pairs : IntMap v -> List (Key,v)
pairs Empty = []
pairs (M t) = treeToList t

||| Gets the keys of the map.
export
keys : IntMap v -> List Key
keys = map fst . pairs

export
values : IntMap v -> List v
values = map snd . pairs

export
Eq v => Eq (IntMap v) where
  (==) = (==) `on` pairs

export
Show v => Show (IntMap v) where
  showPrec p m = showCon p "fromList" $ showArg (pairs m)

export
Functor IntMap where
  map _ Empty = Empty
  map f (M $ Leaf k x) = M $ Leaf k (f x)
  map f (M $ Branch2 x y z) = M $ Branch2 (map f x) y (map f z)
  map f (M $ Branch3 x y z w v) = M $ Branch3 (map f x) y (map f z) w (map f v)
