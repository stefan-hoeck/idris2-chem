module Test.Chem.Element

import Chem.Types
import Chem.Element
import Test.Chem.Types

import Hedgehog

export
element : Gen Elem
element = fromAtomicNr <$> atomicNr
