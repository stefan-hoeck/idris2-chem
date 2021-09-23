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

subsetAromatic : SubsetAromatic -> String
subsetAromatic BArom = "b"
subsetAromatic CArom = "c"
subsetAromatic NArom = "n"
subsetAromatic OArom = "o"
subsetAromatic SArom = "s"
subsetAromatic PArom = "p"

aromatic : Aromatic -> String
aromatic (SA x) = subsetAromatic x
aromatic SeArom = "se"
aromatic AsArom = "as"

orgSubset : OrgSubset -> String
orgSubset B      = "B"
orgSubset C      = "C"
orgSubset N      = "N"
orgSubset O      = "O"
orgSubset F      = "F"
orgSubset P      = "P"
orgSubset S      = "S"
orgSubset Cl     = "Cl"
orgSubset Br     = "Br"
orgSubset I      = "I"
orgSubset (OA x) = subsetAromatic x

export
smilesElem : SmilesElem -> String
smilesElem (El x) = symbol x
smilesElem (A x)  = aromatic x

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
atom (SubsetAtom a) = orgSubset a
atom (MkAtom m e chi h chg) =
  "[" ++ maybe "" show m ++ smilesElem e ++ chirality chi ++
  hcount h ++ charge chg ++ "]"

export
bond : Bond -> String
bond Sngl = "-"
bond Arom = ":"
bond Dbl  = "="
bond Trpl = "#"
bond Quad = "$"
