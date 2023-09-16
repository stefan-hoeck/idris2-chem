module Text.Smiles.Types

import Chem
import Derive.Prelude
import Derive.Refined

%default total
%language ElabReflection

--------------------------------------------------------------------------------
--          Chirality
--------------------------------------------------------------------------------

||| Index for tetrahedral chirality flags as given in the
||| OpenSMILES specification
public export
record TBIx where
  constructor MkTBIx
  value : Bits8
  {auto 0 prf : FromTo 1 20 value}

export %inline
Interpolation TBIx where
  interpolate = show . value

namespace TBIx
  %runElab derive "TBIx" [Show,Eq,Ord,RefinedInteger]

||| Index for octahedral chirality flags as given in the
||| OpenSMILES specification
public export
record OHIx where
  constructor MkOHIx
  value : Bits8
  {auto 0 prf : FromTo 1 20 value}

export %inline
Interpolation OHIx where
  interpolate = show . value

namespace OHIx
  %runElab derive "OHIx" [Show,Eq,Ord,RefinedInteger]

||| Chirality flag of a bracket atom
public export
data Chirality =
  None | CW | CCW | TH1 | TH2 | AL1 | AL2 | SP1 | SP2 | SP3 | TB TBIx | OH OHIx

export
Interpolation Chirality where
  interpolate None   = ""
  interpolate CW     = "@@"
  interpolate CCW    = "@"
  interpolate TH1    = "@TH1"
  interpolate TH2    = "@TH2"
  interpolate AL1    = "@AL1"
  interpolate AL2    = "@AL2"
  interpolate SP1    = "@SP1"
  interpolate SP2    = "@SP2"
  interpolate SP3    = "@SP3"
  interpolate (TB x) = "@TB\{x}"
  interpolate (OH x) = "@OH\{x}"

%runElab derive "Chirality" [Ord,Eq,Show]

--------------------------------------------------------------------------------
--          Atoms
--------------------------------------------------------------------------------

||| Proof that an element (plus aromaticity flag) is a valid subset
||| element that can appear without being wrapped in a pair of
||| brackets.
public export
data ValidSubset : Elem -> Bool -> Type where
  VB  : ValidSubset B b
  VC  : ValidSubset C b
  VN  : ValidSubset N b
  VO  : ValidSubset O b
  VF  : ValidSubset F False
  VP  : ValidSubset P b
  VS  : ValidSubset S b
  VCl : ValidSubset Cl False
  VBr : ValidSubset Br False
  VI  : ValidSubset I False

export %hint
0 toValidArom : ValidSubset e b => ValidAromatic e b
toValidArom {b = False}       = VARest
toValidArom {b = True} @{VB}  = VAB
toValidArom {b = True} @{VC}  = VAC
toValidArom {b = True} @{VN}  = VAN
toValidArom {b = True} @{VO}  = VAO
toValidArom {b = True} @{VP}  = VAP
toValidArom {b = True} @{VS}  = VAS

public export
data SmilesAtom : Type where
  SubsetAtom :
       (elem       : Elem)
    -> (arom       : Bool)
    -> {auto 0 prf : ValidSubset elem arom}
    -> SmilesAtom
  Bracket : Atom AromIsotope Charge () () HCount () Chirality () -> SmilesAtom

%runElab derive "SmilesAtom" [Show,Eq]

export %inline
bracket : AromIsotope -> Chirality -> HCount -> Charge -> SmilesAtom
bracket a c h ch = Bracket (MkAtom a ch () () h () c ())

export %inline
isArom : SmilesAtom -> Bool
isArom (SubsetAtom _ a) = a
isArom (Bracket a)      = a.elem.arom

%inline
aromElem : Elem -> Bool -> String
aromElem e True  = toLower $ symbol e
aromElem e False = symbol e

encodeCharge : Charge -> String
encodeCharge 0    = ""
encodeCharge 1    = "+"
encodeCharge (-1) = "-"
encodeCharge v    = if v.value > 0 then "+\{v}" else "\{v}"

encodeH : HCount -> String
encodeH 0 = ""
encodeH 1 = "H"
encodeH n = "H\{n}"

encodeAtom : SmilesAtom -> String
encodeAtom (SubsetAtom e b)  = aromElem e b
encodeAtom (Bracket $ MkAtom (MkAI e mn ar) chrg () () h () ch ()) =
  let mns := maybe "" (show . value) mn
   in "[\{mns}\{aromElem e ar}\{ch}\{encodeH h}\{encodeCharge chrg}]"

export %inline
Interpolation SmilesAtom where
  interpolate = encodeAtom

--------------------------------------------------------------------------------
--          Bonds
--------------------------------------------------------------------------------

||| An natural number in the range [0,99] representing a ring opening
||| or -closure in a SMILES string
public export
record RingNr where
  constructor MkRingNr
  value : Bits8
  0 prf : value <= 99

export %inline
Interpolation RingNr where
  interpolate n = if n.value >= 10 then "%\{show n.value}" else show n.value

namespace RingNr
  %runElab derive "RingNr" [Show,Eq,Ord,RefinedInteger]

||| A bond in a SMILES string
public export
data SmilesBond = Sngl | Arom | Dbl | Trpl | Quad | FW | BW

export %inline
Interpolation SmilesBond where
  interpolate Sngl = "-"
  interpolate Arom = ":"
  interpolate Dbl  = "="
  interpolate Trpl = "#"
  interpolate Quad = "$"
  interpolate FW   = "/"
  interpolate BW   = "\\"

%runElab derive "SmilesBond" [Show,Eq,Ord]

public export
SmilesMol : Type
SmilesMol = Graph SmilesBond SmilesAtom
