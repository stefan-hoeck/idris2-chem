module Test.Chem.Isotope

import Chem
import Hedgehog
import Test.Chem.Elem
import Test.Chem.Types

export
isotope : Gen Isotope
isotope = [| MkI elem (maybe massNr) |]

export
aromIsotope : Gen AromIsotope
aromIsotope = [| mkAI aromElem (maybe massNr) |]
  where
    mkAI : AromElem -> Maybe MassNr -> AromIsotope
    mkAI (MkAE e a) m = MkAI e m a

