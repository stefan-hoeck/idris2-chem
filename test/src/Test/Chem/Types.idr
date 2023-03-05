module Test.Chem.Types

import Data.Maybe
import Chem
import Hedgehog

export
atomicNr : Gen AtomicNr
atomicNr = fromMaybe 1 . refineAtomicNr <$> bits8 (linear 1 118)

export
massNr : Gen MassNr
massNr = fromMaybe 1 . refineMassNr <$> bits16 (linear 1 511)

export
abundance : Gen Abundance
abundance = fromMaybe 1.0 . refineAbundance <$> double (linear MinAbundanceValue 1.0)

export
molecularMass : Gen MolecularMass
molecularMass = fromMaybe 1.0 . refineMolecularMass <$> double (linear 0 MaxMolecularMass)

export
molarMass : Gen MolarMass
molarMass = fromMaybe 1.0 . refineMolarMass <$> double (linear 0 MaxMolecularMass)

export
charge : Gen Charge
charge = fromMaybe 0 . refineCharge <$> int8 (linearFrom 0 (-15) 15)
