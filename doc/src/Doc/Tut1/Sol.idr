module Doc.Tut1.Sol

import Doc.Tut1

%default total

--------------------------------------------------------------------------------
--          Exercise 1
--------------------------------------------------------------------------------

public export
atomicNr : Element -> Bits8
atomicNr H   = 1
atomicNr He  = 2
atomicNr Li  = 3
atomicNr B   = 5
atomicNr C   = 6
atomicNr N   = 7
atomicNr O   = 8
atomicNr F   = 9
atomicNr Ne  = 10
atomicNr P   = 15
atomicNr S   = 16
atomicNr Cl  = 17
atomicNr Ar  = 18
atomicNr Se  = 34
atomicNr Br  = 35
atomicNr Kr  = 36

public export
fromAtomicNr : Bits8 -> Maybe Element
fromAtomicNr 1   = Just H
fromAtomicNr 2   = Just He
fromAtomicNr 3   = Just Li
fromAtomicNr 5   = Just B
fromAtomicNr 6   = Just C
fromAtomicNr 7   = Just N
fromAtomicNr 8   = Just O
fromAtomicNr 9   = Just F
fromAtomicNr 10  = Just Ne
fromAtomicNr 15  = Just P
fromAtomicNr 16  = Just S
fromAtomicNr 17  = Just Cl
fromAtomicNr 18  = Just Ar
fromAtomicNr 34  = Just Se
fromAtomicNr 35  = Just Br
fromAtomicNr 36  = Just Kr
fromAtomicNr _   = Nothing

export
symbol : Element -> String
symbol H  = "H"
symbol He = "He"
symbol Li = "Le"
symbol B  = "B"
symbol C  = "C"
symbol N  = "N"
symbol O  = "O"
symbol F  = "F"
symbol Ne = "Ne"
symbol P  = "P"
symbol S  = "S"
symbol Cl = "Cl"
symbol Ar = "Ar"
symbol Se = "Se"
symbol Br = "Br"
symbol Kr = "Kr"

export
read : String -> Maybe Element
read "H"  = Just H
read "He" = Just He
read "Li" = Just Li
read "B"  = Just B
read "C"  = Just C
read "N"  = Just N
read "O"  = Just O
read "F"  = Just F
read "Ne" = Just Ne
read "P"  = Just P
read "S"  = Just S
read "Cl" = Just Cl
read "Ar" = Just Ar
read "Se" = Just Se
read "Br" = Just Br
read "Kr" = Just Kr
read _    = Nothing

--------------------------------------------------------------------------------
--          Exercise 2
--------------------------------------------------------------------------------

Eq a => Eq (BTree a) where
  Leaf       == Leaf       = True
  Node x y z == Node a b c = x == a && y == b && z == c
  _          == _          = False

Ord a => Ord (BTree a) where
  compare Leaf Leaf                 = EQ
  compare Leaf _                    = LT
  compare _    Leaf                 = GT
  compare (Node x y z) (Node a b c) =
    compare x a <+> compare y b <+> compare z c

Functor BTree where
  map _ Leaf         = Leaf
  map f (Node x y z) = Node (map f x) (f y) (map f z)

Foldable BTree where
  foldMap _ Leaf = neutral
  foldMap f (Node x y z) = foldMap f x <+> f y <+> foldMap f z

  foldr _ acc Leaf         = acc
  foldr f acc (Node x y z) = foldr f (f y $ foldr f acc z) x
  
  foldl _ acc Leaf         = acc
  foldl f acc (Node x y z) = foldl f (f (foldl f acc x) y) z

  null  Leaf         = True
  null  (Node _ _ _) = False

Traversable BTree where
  traverse _ Leaf         = pure Leaf
  traverse f (Node x y z) =
    Node <$> traverse f x <*> f y <*> traverse f z

size : BTree a -> Nat
size = foldl (\n,_ => n + 1) 0

depth : BTree a -> Nat
depth Leaf         = 0
depth (Node x _ z) = 1 + max (depth x) (depth z)
