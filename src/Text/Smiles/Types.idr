module Text.Smiles.Types

import Chem
import Derive.Prelude
import Derive.Refined

--------------------------------------------------------------------------------
--          Pragmas
--------------------------------------------------------------------------------

%default total

%language ElabReflection

--------------------------------------------------------------------------------
--          Chirality
--------------------------------------------------------------------------------

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

public export
data Atom : Type where
  SubsetAtom :
       (elem : Elem)
    -> (arom : Bool)
    -> (0 prf : ValidSubset elem arom)
    => Atom
  Bracket    :
       (massNr    : Maybe MassNr)
    -> (elem      : Elem)
    -> (isArom    : Bool)
    -> (chirality : Chirality)
    -> (hydrogens : HCount)
    -> (charge    : Charge)
    -> (0 prf     : ValidAromatic elem isArom)
    => Atom

public export %inline
isArom : Atom -> Bool
isArom (SubsetAtom _ a)      = a
isArom (Bracket _ _ a _ _ _) = a

public export %inline
bracket : Maybe MassNr -> ValidElem -> Chirality -> HCount -> Charge -> Atom
bracket x (VE e a) z w v = Bracket x e a z w v

%runElab derive "Atom" [Show,Eq]

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

encodeAtom : Atom -> String
encodeAtom (SubsetAtom e b)  = aromElem e b
encodeAtom (Bracket mn e ar ch h chrg) =
  let mns := maybe "" (show . value) mn
   in "[\{mns}\{aromElem e ar}\{ch}\{encodeH h}\{encodeCharge chrg}]"

export %inline
Interpolation Atom where
  interpolate = encodeAtom

--------------------------------------------------------------------------------
--          Bonds
--------------------------------------------------------------------------------

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

public export
data Bond = Sngl | Arom | Dbl | Trpl | Quad | FW | BW

export %inline
Interpolation Bond where
  interpolate Sngl = "-"
  interpolate Arom = ":"
  interpolate Dbl  = "="
  interpolate Trpl = "#"
  interpolate Quad = "$"
  interpolate FW   = "/"
  interpolate BW   = "\\"

%runElab derive "Bond" [Show,Eq,Ord]

public export
SmilesMol : Type
SmilesMol = Graph Bond Atom

export %hint
toValidArom : ValidSubset e b => ValidAromatic e b
toValidArom @{VB}  = VAB
toValidArom @{VC}  = VAC
toValidArom @{VN}  = VAN
toValidArom @{VO}  = VAO
toValidArom @{VF}  = VARest
toValidArom @{VP}  = VAP
toValidArom @{VS}  = VAS
toValidArom @{VCl} = VARest
toValidArom @{VBr} = VARest
toValidArom @{VI}  = VARest
