module Test.Chem.Element

import Chem
import Data.Finite
import Test.Chem.Types

import Hedgehog

export
element : Gen Elem
element = fromAtomicNr <$> atomicNr

prop_elements : Property
prop_elements = withTests 1 $ property $
  map (value . atomicNr) values === [the Bits8 1..118]

prop_atomicNr_roundTrip : Property
prop_atomicNr_roundTrip = withTests 1 . property . for_ values $ \e =>
  fromAtomicNr (atomicNr e) === e

export
props : Group
props = MkGroup "Chem.Element"
  [ ("prop_elements", prop_elements)
  , ("prop_atomicNr_roundTrip", prop_atomicNr_roundTrip)
  ]
