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

%runElab derive "SubsetAromatic" [Generic,Meta,Eq,Show]

public export
data Aromatic = SA SubsetAromatic | SeArom | AsArom

%runElab derive "Aromatic" [Generic,Meta,Eq,Show]

public export
data OrgSubset = B | C | N | O | F | P | S | Cl | Br | I | OA SubsetAromatic

%runElab derive "OrgSubset" [Generic,Meta,Eq,Show]

public export
data SmilesElem = El Elem | A Aromatic

%runElab derive "SmilesElem" [Generic,Meta,Eq,Show]

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
