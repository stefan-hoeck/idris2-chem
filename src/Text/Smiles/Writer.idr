module Text.Smiles.Writer

import Chem.Element
import Chem.Types
import Text.Smiles.Types
import Data.String

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

export
validElem : (e : Elem) -> (b : Bool) -> (0 _ : ValidAromatic e b) => String
validElem x False = show x
validElem x True = toLower $ show x

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

export
atom : Atom -> String
atom (SubsetAtom a arom) = validElem a arom
atom (Bracket m e arom chi h chg) =
  "[" ++ maybe "" show m ++ validElem e arom ++ chirality chi ++
  hcount h ++ charge chg ++ "]"

export
bond : Bond -> String
bond Sngl = "-"
bond Arom = ":"
bond Dbl  = "="
bond Trpl = "#"
bond Quad = "$"
