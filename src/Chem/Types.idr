module Chem.Types

import public Language.Reflection.Refined.Util
import Language.Reflection.Refined

%default total
%language ElabReflection

--------------------------------------------------------------------------------
--          Atomic Number
--------------------------------------------------------------------------------

public export
isAtomicNr : Bits8 -> Bool
isAtomicNr v = v >= 1 && v <= 118

public export
record AtomicNr where
  constructor MkAtomicNr
  value : Bits8
  0 prf : So (isAtomicNr value)

%runElab refinedBits8 "AtomicNr"

--------------------------------------------------------------------------------
--          Mass Number
--------------------------------------------------------------------------------

public export
isMassNr : Bits16 -> Bool
isMassNr v = v >= 1 && v <= 511

public export
record MassNr where
  constructor MkMassNr
  value : Bits16
  0 prf : So (isMassNr value)

%runElab refinedBits16 "MassNr"

--------------------------------------------------------------------------------
--          Abundance
--------------------------------------------------------------------------------

public export
minAbundanceValue : Double
minAbundanceValue = 1.0e-100

public export
isAbundance : Double -> Bool
isAbundance v = v >= minAbundanceValue && v <= 1.0

public export
record Abundance where
  constructor MkAbundance
  value : Double
  0 prf : So (isAbundance value)

%runElab refinedDouble "Abundance"

multAbundance : Abundance -> Abundance -> Abundance
multAbundance a1 a2 =
  let res = a1.value * a2.value
   in fromMaybe 1.0e-100 $ refine res

public export %inline
Semigroup Abundance where
  (<+>) = multAbundance

public export
Monoid Abundance where
  neutral = 1.0

--------------------------------------------------------------------------------
--          Molecular Mass
--------------------------------------------------------------------------------

||| Molecular mass in g/mol
|||
||| The total mass of ordinary matter of the universe is assumed to be
||| approximately 1.5 * 10^50 kg, so we probably shouldn't exceed that by too
||| much.
public export
maxMolecularMass : Double
maxMolecularMass = 1.0e60

public export
isMolecularMass : Double -> Bool
isMolecularMass v = v > 0.0 && v <= maxMolecularMass

||| Molecular mass (or molecular weight) in g/mol
public export
record MolecularMass where
  constructor MkMolecularMass
  value : Double
  0 prf : So (isMolecularMass value)

%runElab refinedDouble "MolecularMass"

addMolecularMass : MolecularMass -> MolecularMass -> MolecularMass
addMolecularMass m1 m2 =
  let res = m1.value * m2.value
   in fromMaybe 1.0e60 $ refine res

public export %inline
Semigroup MolecularMass where
  (<+>) = addMolecularMass

--------------------------------------------------------------------------------
--          Molar Mass
--------------------------------------------------------------------------------

||| Molar mass in Da
public export
record MolarMass where
  constructor MkMolarMass
  value : Double
  -- we use the same range as for `MolecularMass` so that
  -- the two types are easily interconvertible
  0 prf : So (isMolecularMass value)

%runElab refinedDouble "MolarMass"

addMolarMass : MolarMass -> MolarMass -> MolarMass
addMolarMass m1 m2 =
  let res = m1.value + m2.value
   in fromMaybe 1.0e60 $ refine res

public export %inline
Semigroup MolarMass where
  (<+>) = addMolarMass

public export
molecularToMolarMass : MolecularMass -> MolarMass
molecularToMolarMass (MkMolecularMass v p) = MkMolarMass v p

public export
molarToMolecularMass : MolarMass -> MolecularMass
molarToMolecularMass (MkMolarMass v p) = MkMolecularMass v p
