module Test.Chem.Types

import Chem.Types
import Data.Refined
import Hedgehog

export
atomicNr : Gen AtomicNr
atomicNr = fromMaybe 1 . refineSo MkAtomicNr <$> bits8 (linear 1 118)

export
massNr : Gen MassNr
massNr = fromMaybe 1 . refineSo MkMassNr <$> bits16 (linear 1 511)

export
abundance : Gen Abundance
abundance =   fromMaybe 1.0 . refineSo MkAbundance
          <$> double (linear minAbundanceValue 1.0)

export
molecularMass : Gen MolecularMass
molecularMass =   fromMaybe 1.0 . refineSo MkMolecularMass
              <$> double (linear 0 maxMolecularMass)

export
molarMass : Gen MolarMass
molarMass =   fromMaybe 1.0 . refineSo MkMolarMass
          <$> double (linear 0 maxMolecularMass)
