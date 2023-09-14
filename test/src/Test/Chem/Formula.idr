module Test.Chem.Formula

import Chem
import Chem.Formula
import Test.Chem.Element

import Hedgehog

%default total

export
formula : Gen Formula
formula =
  foldMap (uncurry singleton) <$>
  list (linear 0 20) [| MkPair element (nat $ linear 0 20) |]
