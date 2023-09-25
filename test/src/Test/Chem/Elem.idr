module Test.Chem.Elem

import Data.Finite
import Data.Vect
import Test.Chem.Generators

prop_elems : Property
prop_elems = withTests 1 $ property $
  map (value . atomicNr) values === [the Bits8 1..118]

prop_atomicNr_roundTrip : Property
prop_atomicNr_roundTrip = withTests 1 . property . for_ values $ \e =>
  fromAtomicNr (atomicNr e) === e

export
props : Group
props = MkGroup "Chem.Element"
  [ ("prop_elems", prop_elems)
  , ("prop_atomicNr_roundTrip", prop_atomicNr_roundTrip)
  ]
