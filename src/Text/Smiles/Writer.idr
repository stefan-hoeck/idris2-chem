module Text.Smiles.Writer

import Chem.Element
import Chem.Types
import Text.Smiles.Types

export
chirality : Chirality -> String
chirality None   = ""
chirality CW     = "@@"
chirality CCW    = "@"
chirality TH1    = "@TH1"
chirality TH2    = "@TH2"
chirality AL1    = "@AL1"
chirality AL2    = "@AL2"
chirality SP1    = "@SP1"
chirality SP2    = "@SP2"
chirality SP3    = "@SP3"
chirality (TB x) = #"@TB\#{show x}"#
chirality (OH x) = #"@OH\#{show x}"#

validElem : Elem -> Bool -> String
validElem B False  = "B"
validElem B True = "b"
validElem C False = "C"
validElem C True = "c"
validElem N False = "N"
validElem N True = "n"
validElem O False = "O"
validElem O True = "o"
validElem F False = "F"
validElem P False = "P"
validElem P True = "p"
validElem S False = "S"
validElem S True = "s"
validElem Cl False = "Cl"
validElem Br False = "Br"
validElem I False = "I"
validElem Se False = "Se"
validElem Se True = "se"
validElem As False = "As"
validElem As True = "as"
validElem elem False = show elem
validElem elem True = show elem

export
hcount : HCount -> String
hcount (MkHCount 0 _) = ""
hcount (MkHCount 1 _) = "H"
hcount (MkHCount v _) = "H" ++ show v

export
charge : Charge -> String
charge (MkCharge 0 _)    = ""
charge (MkCharge 1 _)    = "+"
charge (MkCharge (-1) _) = "-"
charge (MkCharge v _)    = if v > 0 then "+" ++ show v else show v

---- not a nice solution ----
export
atom : Atom -> String
atom (SubsetAtom a arom _) = validElem a arom
atom (Bracket m e arom chi h chg prf) =
  "[" ++ maybe "" show m ++ validElem e arom ++ chirality chi ++
  hcount h ++ charge chg ++ "]"

export
bond : Bond -> String
bond Sngl = "-"
bond Arom = ":"
bond Dbl  = "="
bond Trpl = "#"
bond Quad = "$"
