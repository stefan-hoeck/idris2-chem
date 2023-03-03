module Chem.Types

import public Data.Refined
import public Decidable.HDec.Bits16
import public Decidable.HDec.Bits8
import public Decidable.HDec.Int8
import Derive.Prelude
import Derive.Refined
import Text.RW

%default total
%language ElabReflection

--------------------------------------------------------------------------------
--          Mass Number
--------------------------------------------------------------------------------

public export
record MassNr where
  constructor MkMassNr
  value : Bits16
  {auto 0 prf : FromTo 1 511 value}

export %inline
Interpolation MassNr where
  interpolate = show . value

namespace MassNr
  %runElab derive "MassNr" [Show,Eq,Ord,RefinedInteger]

--------------------------------------------------------------------------------
--          Abundance
--------------------------------------------------------------------------------

public export %inline
MinAbundanceValue : Double
MinAbundanceValue = 1.0e-100

public export
IsAbundance : Double -> Bool
IsAbundance v = v >= MinAbundanceValue && v <= 1.0

public export
record Abundance where
  constructor MkAbundance
  value : Double
  {auto 0 prf : Holds IsAbundance value}

export %inline
Interpolation Abundance where
  interpolate = show . value

namespace Abundance
  %runElab derive "Abundance" [Show,Eq,Ord,RefinedDouble]

public export %inline
multAbundance : Abundance -> Abundance -> Abundance
multAbundance a1 a2 =
  let res = a1.value * a2.value
   in case hdec0 {p = Holds IsAbundance} res of
        Just0 _ => MkAbundance res
        Nothing0 => 1.0e-100

public export %inline
Semigroup Abundance where
  (<+>) = multAbundance

public export %inline
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
public export %inline
MaxMolecularMass : Double
MaxMolecularMass = 1.0e60

public export %inline
IsMolecularMass : Double -> Bool
IsMolecularMass v = v > 0.0 && v <= MaxMolecularMass

||| Molecular mass (or molecular weight) in g/mol
public export
record MolecularMass where
  constructor MkMolecularMass
  value : Double
  {auto 0 prf : Holds IsMolecularMass value}

export %inline
Interpolation MolecularMass where
  interpolate = show . value

namespace MolecularMass
  %runElab derive "MolecularMass" [Show,Eq,Ord,RefinedDouble]

public export %inline
addMolecularMass : MolecularMass -> MolecularMass -> MolecularMass
addMolecularMass a1 a2 =
  let res = a1.value * a2.value
   in case hdec0 {p = Holds IsMolecularMass} res of
        Just0 _ => MkMolecularMass res
        Nothing0 => 1.0e60

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
  {auto 0 prf : Holds IsMolecularMass value}

export %inline
Interpolation MolarMass where
  interpolate = show . value

namespace MolarMass
  %runElab derive "MolarMass" [Show,Eq,Ord,RefinedDouble]

public export %inline
addMolarMass : MolarMass -> MolarMass -> MolarMass
addMolarMass a1 a2 =
  let res = a1.value * a2.value
   in case hdec0 {p = Holds IsMolecularMass} res of
        Just0 _ => MkMolarMass res
        Nothing0 => 1.0e60

public export %inline
Semigroup MolarMass where
  (<+>) = addMolarMass

public export %inline
molecularToMolarMass : MolecularMass -> MolarMass
molecularToMolarMass (MkMolecularMass v) = MkMolarMass v

public export %inline
molarToMolecularMass : MolarMass -> MolecularMass
molarToMolecularMass (MkMolarMass v) = MkMolecularMass v

--------------------------------------------------------------------------------
--          Charge
--------------------------------------------------------------------------------

public export
record Charge where
  constructor MkCharge
  value : Int8
  {auto 0 prf : FromTo (-15) 15 value}

export %inline
Interpolation Charge where
  interpolate = show . value

namespace Charge
  %runElab derive "Charge" [Show,Eq,Ord,RefinedInteger]

--------------------------------------------------------------------------------
--          HCount
--------------------------------------------------------------------------------

public export
record HCount where
  constructor MkHCount
  value : Bits8
  {auto 0 prf : value < 10}

export %inline
Interpolation HCount where
  interpolate = show . value

namespace HCount
  %runElab derive "HCount" [Show,Eq,Ord,RefinedInteger]
