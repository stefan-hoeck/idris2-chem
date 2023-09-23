module Test.Chem.Formula

import Chem
import Chem.Formula
import Test.Chem.Elem

import Hedgehog

%default total

export
formula : Gen Formula
formula =
  foldMap (uncurry singleton) <$>
  list (linear 0 20) [| MkPair elem (nat $ linear 0 20) |]
