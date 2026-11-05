module Test.Chem.Parity

import Chem.Parity
import Data.Vect
import Hedgehog

%default total

distinct : Eq a => (a,a) -> Bool
distinct (x,y) = x /= y

gen : (curr : Nat) -> (n : Nat) -> Vect n Nat
gen c 0     = []
gen c (S n) = c :: gen (S c) n

parameters (n          : Nat)
           {auto 0 prf : IsSucc n}

  genSwap : Gen (Fin n, Fin n)
  genSwap = MkPair <$> anyFin n <*> anyFin n

  genSwaps : Gen (List (Fin n, Fin n))
  genSwaps = filter distinct <$> list (linear 0 30) genSwap

swap : Vect n a -> (Fin n, Fin n) -> Vect n a
swap v (i,j) = replaceAt j (index i v) $ replaceAt i (index j v) v

prop_parity : Property
prop_parity =
  property $ do
    n      <- forAll $ Gen.nat $ linear 0 10
    let vs := gen 0 (S n)
    sw     <- forAll $ genSwaps (S n)
    parity (toList $ foldl swap vs sw) === cast (length sw)

export
props : Group
props = MkGroup "Chem.Parity" [("prop_parity", prop_parity)]
