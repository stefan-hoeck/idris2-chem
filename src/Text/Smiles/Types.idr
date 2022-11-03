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
data ValidAromatic : Elem -> Bool -> Type where
  VAB    : ValidAromatic B b
  VAC    : ValidAromatic C b
  VAN    : ValidAromatic N b
  VAO    : ValidAromatic O b
  VAP    : ValidAromatic P b
  VAS    : ValidAromatic S b
  VASe   : ValidAromatic Se b
  VAAs   : ValidAromatic As b
  VARest : ValidAromatic _ False

public export
record ValidElem where
  constructor VE
  elem : Elem
  arom : Bool
  0 prf : ValidAromatic elem arom

public export
data Atom : Type where
  SubsetAtom :  (elem : Elem)
             -> (arom : Bool)
             -> (0 prf : ValidSubset elem arom)
             => Atom
  Bracket    :  (massNr    : Maybe MassNr)
             -> (elem      : Elem)
             -> (isArom    : Bool)
             -> (chirality : Chirality)
             -> (hydrogens : HCount)
             -> (charge    : Charge)
             -> (0 prf     : ValidAromatic elem isArom)
             => Atom

public export
Eq Atom where
  (SubsetAtom e ar) == (SubsetAtom e2 ar2) = e == e2 && ar == ar2
  (Bracket ma e ar ch hy char) == (Bracket ma2 e2 ar2 ch2 hy2 char2) =
      ma == ma2 && e == e2 && ar == ar2 && ch == ch2 && hy == hy2 && char == char2
  _ == _ = False

Show Atom where
  showPrec p (SubsetAtom elem arom) =
    showCon p "SubsetAtom" $ showArg elem ++ showArg arom ++ " prf"
  showPrec p (Bracket ma e a ch hy char) =
    showCon p "Bracket" $ showArg ma ++ showArg e ++ showArg a ++ 
                         showArg ch ++ showArg hy ++ showArg char ++ " prf"


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

public export
Eq Bond where
  Sngl == Sngl = True
  Arom == Arom = True
  Dbl  == Dbl  = True
  Trpl == Trpl = True
  Quad == Quad = True
  _    == _    = False


%runElab derive "Bond" [Generic,Meta,Show]

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
