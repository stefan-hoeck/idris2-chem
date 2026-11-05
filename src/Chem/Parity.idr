module Chem.Parity

import Derive.Prelude

%default total
%language ElabReflection

public export
data Parity = Even | Odd

%runElab derive "Parity" [Show,Eq,Ord]

public export
Semigroup Parity where
  Even <+> p    = p
  Odd  <+> Even = Odd
  Odd  <+> Odd  = Even

public export
Monoid Parity where
  neutral = Even

export %inline
Cast Nat Parity where
  cast n =
    case prim__and_Integer (cast n) 1 of
      0 => Even
      _ => Odd

||| Computes the parity of a permutation, that is, the number
||| of swaps required to convert the given list into an ordered
||| list.
|||
||| Note: The list is expected to hold no duplicates
export
parity : Ord a => List a -> Parity
parity []        = Even
parity (x :: xs) = cast (count (< x) xs) <+> parity xs

||| Tests if the given two permutations have the same parity.
|||
||| Does not verify if the two lists are actually permutations of
||| the same sequence.
export
sameParity : Ord a => (xs,ys : List a) -> Bool
sameParity xs ys = parity xs == parity ys
