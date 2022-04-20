module Data.AssocList

import Data.DPair
import Data.Prim.Bits64
import Data.Maybe.NothingMax

%default total

public export
0 Key : Type
Key = Bits64

public export
0 (<): Maybe Key -> Maybe Key -> Type
(<) = LT (<)

public export
0 (<=): Maybe Key -> Maybe Key -> Type
m1 <= m2 = Either (m1 < m2) (m1 === m2)

||| A provably sorted assoc list with `Bits64` as the key type.
|||
||| This is mainly useful for short sequences of key / value pairs.
||| It comes with O(n) runtime complexity for `insert`, `update`,
||| `lookup` and `delete`, but also with fast O(n) complexity for
||| `union` and `intersection`.
public export
data AL : (ix : Maybe Key) -> Type -> Type where
  Nil : AL Nothing a
  (::) :  {0 ix : _}
       -> (p     : (Key,a))
       -> (ps    : AL ix a)
       -> (0 prf : Just (fst p) < ix)
       => AL (Just $ fst p) a

public export
Functor (AL ix) where
  map f []       = []
  map f ((k,v) :: t) = (k,f v) :: map f t

public export
Foldable (AL ix) where
  foldr c n [] = n
  foldr c n (x::xs) = c (snd x) (foldr c n xs)

  foldl f q [] = q
  foldl f q (x::xs) = foldl f (f q $ snd x) xs

  null [] = True
  null (_::_) = False

  foldMap f = foldl (\acc, elem => acc <+> f elem) neutral

public export
Traversable (AL ix) where
  traverse f [] = pure []
  traverse f (p :: ps) =
    (\v,qs => (fst p,v) :: qs) <$> f (snd p) <*> traverse f ps

||| Lookup a key in an assoc list.
public export
lookup : (k : Key) -> AL ix a -> Maybe a
lookup k (p :: ps) = case comp k (fst p) of
  LT _ _ _ => Nothing
  EQ _ _ _ => Just $ snd p
  GT _ _ _ => lookup k ps
lookup _ []        = Nothing

public export
nonEmpty : AL m a -> Bool
nonEmpty (p :: ps) = True
nonEmpty []        = False

public export
isEmpty : AL m a -> Bool
isEmpty (p :: ps) = False
isEmpty []        = True

||| Extracts the key / value pairs for the assoc list.
public export
pairs : AL ix a -> List (Key,a)
pairs (p :: ps) = p :: pairs ps
pairs []        = []

||| Heterogeneous equality check.
public export
heq : Eq a => AL m a -> AL n a -> Bool
heq (p :: ps) (q :: qs) = p == q && heq ps qs
heq [] [] = True
heq _ _   = False

export %inline
Eq a => Eq (AL m a) where
  (==) = heq

export %inline
Show a => Show (AL m a) where
  showPrec p m = showPrec p (pairs m)

--------------------------------------------------------------------------------
--          Insert
--------------------------------------------------------------------------------

||| Inserting a new key / value pair leads to a new assoc list where the
||| key at the head is either equal to the new key or the one previously
||| at the head.
|||
||| @ k  New key that was inserted
||| @ mk Key index of the original assoc list
public export
record InsertRes (k : Key) (mk : Maybe Key) (a : Type) where
  constructor IR
  pairs : AL (Just x) a
  0 prf : Either (x === k) (Just x === mk)

0 prependLemma :  {x,y,k : Key}
               -> {mk : Maybe Key}
               -> Either (x === k) (Just x === mk)
               -> (0 ltyk : Just y < Just k)
               => (0 ltym : Just y < mk)
               => Just y < Just x
prependLemma (Left Refl) = ltyk
prependLemma (Right z)   = rewrite z in ltym

%inline
prepend :  (p : (Key,a))
        -> InsertRes k mk a
        -> (0 lt : Just (fst p) < Just k)
        => (0 sm : Just (fst p) < mk)
        => InsertRes k (Just $ fst p) a
prepend p (IR ps prf1) =
  let 0 prf = prependLemma prf1
   in IR (p :: ps) (Right Refl)

||| Inserts a new key / value pair into an assoc list.
||| The result type reflects the possibilities with regard
||| to the head pair of the new assoc list.
|||
||| Note: If the given key `k` is already present in the assoc list,
||| its associated value will be replaced with `v`.
export
insert : (k : Key) -> (v : a) -> AL ix a -> InsertRes k ix a
insert k v (p :: ps) = case comp k (fst p) of
  LT prf _ _ => IR ((k,v) :: p :: ps) (Left Refl)
  EQ _ prf _ => IR ((fst p, v) :: ps) (Right Refl)
  GT _ _ prf => prepend p $ insert  k v ps
insert k v []        = IR [(k,v)] (Left Refl)

||| Like `insert` but in case `k` is already present in the assoc
||| list, the `v` will be cobine with the old value via function `f`.
export
insertWith :  (f : a -> a -> a)
           -> (k : Key)
           -> (v : a)
           -> AL ix a
           -> InsertRes k ix a
insertWith f k v (p :: ps) = case comp k (fst p) of
  LT prf _ _ => IR ((k,v) :: p :: ps) (Left Refl)
  EQ _ prf _ => IR ((fst p, f v $ snd p) :: ps) (Right Refl)
  GT _ _ prf => prepend p $ insertWith f k v ps
insertWith _ k v []        = IR [(k,v)] (Left Refl)

export
fromList : List (Key,a) -> Exists (\m => AL m a)
fromList []        = Evidence _ []
fromList (x :: xs) =
  let Evidence _ al = fromList xs
      IR al2 _      = insert (fst x) (snd x) al
   in Evidence _ al2


--------------------------------------------------------------------------------
--          Delete
--------------------------------------------------------------------------------

||| Deleting an entry from an assoc list results in a new assoc list
||| the index of which is equal to or smaller than the one from
||| the original list.
|||
||| @ m1 : Key index of the original assoc list.
public export
record DeleteRes (m1 : Maybe Key) (a : Type) where
  constructor DR
  {0 mx : Maybe Key}
  pairs : AL mx a
  0 prf : m1 <= mx

%inline
prependDR :  (p : (Key,a))
          -> DeleteRes m a
          -> (0 lt : Just (fst p) < m)
          => DeleteRes (Just $ fst p) a
prependDR p (DR ps lte) =
  let 0 lt = trans_LT_LTE lt lte
   in DR (p :: ps) (Right Refl)

||| Tries to remove the entry with the given key from the
||| assoc list. The key index of the result will be equal to
||| or greater than `m`.
export
delete : (k : Key) -> AL m a -> DeleteRes m a
delete k (p :: ps) = case comp k (fst p) of
  LT _ _ _ => DR (p :: ps) %search
  EQ _ _ _ => DR ps %search
  GT _ _ _ => prependDR p $ delete k ps
delete k []        = DR [] %search

--------------------------------------------------------------------------------
--          Update
--------------------------------------------------------------------------------

||| Updates the value at the given position by applying the given function.
export
update : (k : Key) -> (a -> a) -> AL m a -> AL m a
update k f (p :: ps) = case comp k (fst p) of
  LT _ _ _ => p :: ps
  EQ _ _ _ => (fst p, f $ snd p) :: ps
  GT _ _ _ => p :: update k f ps
update k f []        = []

||| Updates the value at the given position by applying the given effectful
||| computation.
export
updateA : Applicative f => (k : Key) -> (a -> f a) -> AL m a -> f (AL m a)
updateA k g (p :: ps) = case comp k (fst p) of
  LT _ _ _ => pure $ p :: ps
  EQ _ _ _ => map (\v => (fst p, v) :: ps) (g $ snd p)
  GT _ _ _ => (p ::) <$>  updateA k g ps
updateA k g []        = pure []

--------------------------------------------------------------------------------
--          Union
--------------------------------------------------------------------------------

||| Result of computing the union of two assoc lists with
||| key indices `m1` and `m2`. The result's key index is equal to either
||| `m1` or `m2`
public export
record UnionRes (m1,m2 : Maybe Key) (a : Type) where
  constructor UR
  {0 mx : Maybe Key}
  pairs : AL mx a
  0 prf : Either (m1 === mx) (m2 === mx)

%inline
prepLT : (p : (Key,a))
       -> UnionRes m1 (Just k2) a
       -> (0 prf1 : Just (fst p) < m1)
       => (0 prf2 : Just (fst p) < Just k2)
       => UnionRes (Just $ fst p) (Just k2) a
prepLT p (UR ps prf) =
  let 0 lt = either (trans_LT_EQ prf1) (trans_LT_EQ prf2) prf
   in UR (p :: ps) (Left Refl)

%inline
prepGT : (p : (Key,a))
       -> UnionRes (Just k1) m2 a
       -> (0 prf1 : Just (fst p) < m2)
       => (0 prf2 : Just (fst p) < Just k1)
       => UnionRes (Just k1) (Just $ fst p) a
prepGT p (UR ps prf) =
  let 0 lt = either (trans_LT_EQ prf2) (trans_LT_EQ prf1) prf
   in UR (p :: ps) (Right Refl)

%inline
prepEQ :  {0 x : Maybe Key}
       -> (p : (Key,a))
       -> (0 eq  : fst p === k)
       -> UnionRes m1 m2 a
       -> (0 prf1 : Just (fst p) < m1)
       => (0 prf2 : Just k < m2)
       => UnionRes (Just $ fst p) x a
prepEQ p eq (UR ps prf) =
  let 0 fstp_lt_m2 = rewrite eq in prf2
      0 lt = either (trans_LT_EQ prf1) (trans_LT_EQ fstp_lt_m2) prf
   in UR (p :: ps) (Left Refl)

||| Computes the union of two assoc lists.
|||
||| In case of identical keys, the value of the second list
||| is dropped. Use `unionWith` for better control over handling
||| duplicate entries.
export
union : AL m1 a -> AL m2 a -> UnionRes m1 m2 a
union (p :: ps) (q :: qs) = case comp (fst p) (fst q) of
  LT prf _   _   => prepLT p $ union ps (q :: qs)
  EQ _   prf _   => prepEQ p prf $ union ps qs
  GT _   _   prf => prepGT q $ union (p :: ps) qs
union y [] = UR y (Left Refl)
union [] y = UR y (Right Refl)

||| Like `union` but in case of identical keys appearing in
||| both lists, the associated values are combined using
||| function `f`.
export
unionWith : (a -> a -> a) -> AL m1 a -> AL m2 a -> UnionRes m1 m2 a
unionWith f (p :: ps) (q :: qs) = case comp (fst p) (fst q) of
  LT prf _   _   => prepLT p $ unionWith f ps (q :: qs)
  EQ _   prf _   => prepEQ (fst p, f (snd p) (snd q)) prf $ unionWith f ps qs
  GT _   _   prf => prepGT q $ unionWith f (p :: ps) qs
unionWith _ y [] = UR y (Left Refl)
unionWith _ [] y = UR y (Right Refl)

--------------------------------------------------------------------------------
--          Intersection
--------------------------------------------------------------------------------

||| The result of building the intersection of two assoc lists may
||| contain an arbitrary new key index, which is not smaller than
||| the head indices of the original lists.
public export
record IntersectRes (m1,m2 : Maybe Key) (a : Type) where
  constructor IS
  {0 mx : Maybe Key}
  pairs  : AL mx a
  0 prf1 : m1 <= mx
  0 prf2 : m2 <= mx

0 lteNothing : {m : Maybe Key} -> m <= Nothing
lteNothing {m = Nothing} = Right Refl
lteNothing {m = Just _}  = Left %search

%inline
prependIS :  {0 m1,m2 : Maybe Key}
          -> (p : (Key, a))
          -> (0 prf : fst p === k)
          -> IntersectRes m1 m2 a
          -> (0 lt  : Just (fst p) < m1)
          => IntersectRes (Just $ fst p) (Just k) a
prependIS p prf (IS ps prf1 prf2) =
  let 0 ltp = trans_LT_LTE lt prf1
   in IS (p :: ps) (Right Refl) (Right $ cong Just (sym prf))

||| Computes the intersection of two assoc lists, keeping
||| only entries appearing in both lists. Only the values of
||| the first list are being kept.
export
intersect : AL m1 a -> AL m2 a -> IntersectRes m1 m2 a
intersect (p :: ps) (q :: qs) = case comp (fst p) (fst q) of
  LT _ _ _   =>
    let IS res p1 p2 = intersect ps (q :: qs)
     in IS res (trans %search p1) p2
  EQ _ y _ => prependIS p y $ intersect ps qs
  GT _ _ _ =>
    let IS res p1 p2 = intersect (p :: ps) qs
     in IS res p1 (trans %search p2)
intersect y [] = IS [] lteNothing %search
intersect [] y = IS [] %search lteNothing

||| Computes the intersection of two assoc lists, keeping
||| only entries appearing in both lists. Values of the two
||| lists are combine using function `f`.
export
intersectWith : (a -> a -> a) -> AL m1 a -> AL m2 a -> IntersectRes m1 m2 a
intersectWith f (p :: ps) (q :: qs) = case comp (fst p) (fst q) of
  LT _ _ _ =>
    let IS res p1 p2 = intersectWith f ps (q :: qs)
     in IS res (trans %search p1) p2
  EQ _ y _ => prependIS (fst p, f (snd p) (snd q)) y $ intersectWith f ps qs
  GT _ _ _ =>
    let IS res p1 p2 = intersectWith f (p :: ps) qs
     in IS res p1 (trans %search p2)
intersectWith _ y [] = IS [] lteNothing %search
intersectWith _ [] y = IS [] %search lteNothing
