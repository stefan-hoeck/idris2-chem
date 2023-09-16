module Chem.Hydrogen

import Chem.Atom
import Chem.Element
import Chem.Types
import Derive.Prelude

%language ElabReflection
%default total

---------------------------------------------------------------------
-- Error type
---------------------------------------------------------------------

public export
record HErr where
  constructor HE
  atom    : Nat
  elem    : Elem
  valence : Nat

%runElab derive "HErr" [Eq,Show]

export
Interpolation HErr where
  interpolate (HE n el v) =
    "Valence exceeded for \{el}: " ++
    "\{show v} bond equivalents found at node \{show n}"

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

public export
record BondOrder where
  constructor BO
  order : Nat

%runElab derive "BondOrder" [Eq,Ord,Show,FromInteger]

export %inline
Semigroup BondOrder where
  BO x <+> BO y = BO $ x + y

export %inline
Monoid BondOrder where neutral = 0

-- calculates the total bond order
bondTotal : Cast b BondOrder => List b -> BondOrder
bondTotal = foldl (\n,b => n <+> cast b) 0
