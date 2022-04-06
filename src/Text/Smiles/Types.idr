module Text.Smiles.Types

import Chem.Element
import Chem.Types
import public Data.Graph
import Data.Refined
import Generics.Derive
import Language.Reflection.Refined
import Text.RW

--------------------------------------------------------------------------------
--          Pragmas
--------------------------------------------------------------------------------

%default total

%language ElabReflection

--------------------------------------------------------------------------------
--          HCount and Charge
--------------------------------------------------------------------------------

public export
record HCount where
  constructor MkHCount
  value : Bits8
  0 prf : So (value < 10)

%runElab rwInt "HCount" `(Bits8)

--------------------------------------------------------------------------------
--          Chirality
--------------------------------------------------------------------------------

public export
record TBIx where
  constructor MkTBIx
  value : Bits8
  0 prf : So (1 <= value && value <= 20)

%runElab rwInt "TBIx" `(Bits8)

public export
record OHIx where
  constructor MkOHIx
  value : Bits8
  0 prf : So (1 <= value && value <= 20)

%runElab rwInt "OHIx" `(Bits8)

public export
data Chirality =
  None | CW | CCW | TH1 | TH2 | AL1 | AL2 | SP1 | SP2 | SP3 | TB TBIx | OH OHIx

%runElab derive "Chirality" [Generic,Meta,Eq,Show]

--------------------------------------------------------------------------------
--          Atoms
--------------------------------------------------------------------------------

public export
data SubsetAromatic = BArom | CArom | NArom | OArom | SArom | PArom

public export
Eq SubsetAromatic where
  CArom == CArom = True
  BArom == BArom = True
  NArom == NArom = True
  OArom == OArom = True
  SArom == SArom = True
  PArom == PArom = True
  _     == _     = False


%runElab derive "SubsetAromatic" [Generic,Meta,Show]

public export
data Aromatic = SA SubsetAromatic | SeArom | AsArom

public export
Eq Aromatic where
  SA x   == SA y   = x == y
  SeArom == SeArom = True
  AsArom == AsArom = True
  _      == _      = False


%runElab derive "Aromatic" [Generic,Meta,Show]


public export
data OrgSubset = B | C | N | O | F | P | S | Cl | Br | I | OA SubsetAromatic

public export
Eq OrgSubset where
  C    == C    = True
  O    == O    = True
  N    == N    = True
  F    == F    = True
  P    == P    = True
  S    == S    = True
  Cl   == Cl   = True
  Br   == Br   = True
  I    == I    = True
  B    == B    = True
  OA x == OA y = True
  _    == _    = False

%runElab derive "OrgSubset" [Generic,Meta,Show]

public export
data SmilesElem = El Elem | A Aromatic

public export
Eq SmilesElem where
  El x == El y = x == y
  A  x == A  y = x == y
  _    == _    = False

%runElab derive "SmilesElem" [Generic,Meta,Show]

public export
data Atom : Type where
  SubsetAtom :  (elem : OrgSubset) -> Atom
  MkAtom     :  (massNr    : Maybe MassNr)
             -> (elem      : SmilesElem)
             -> (chirality : Chirality)
             -> (hydrogens : HCount)
             -> (charge    : Charge)
             -> Atom

%runElab derive "Atom" [Generic,Meta,Eq,Show]

--------------------------------------------------------------------------------
--          Bonds
--------------------------------------------------------------------------------

public export
record RingNr where
  constructor MkRingNr
  value : Bits8
  0 prf : So (value < 99)

%runElab rwInt "RingNr" `(Bits8)

public export
data Bond = Sngl | Arom | Dbl | Trpl | Quad

%runElab derive "Bond" [Generic,Meta,Eq,Show]

public export
SmilesMol : Type
SmilesMol = Graph Bond Atom
