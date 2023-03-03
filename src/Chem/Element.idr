module Chem.Element

import public Data.Refined
import public Decidable.HDec.Bits8
import Derive.Prelude
import Derive.Refined
import Text.RW

%language ElabReflection
%default total

--------------------------------------------------------------------------------
--          Atomic Number
--------------------------------------------------------------------------------

public export
0 IsAtomicNr : Bits8 -> Type
IsAtomicNr = FromTo 1 118

0 test : IsAtomicNr 2
test = %search


public export
record AtomicNr where
  constructor MkAtomicNr
  value : Bits8
  {auto 0 prf : IsAtomicNr value}

namespace AtomicNr
  %runElab derive "AtomicNr" [Show,Eq,Ord,RefinedInteger]

--------------------------------------------------------------------------------
--          The Elements
--------------------------------------------------------------------------------

public export
data Elem =
    H                                                                                  | He
  | Li | Be                                                   | B  | C  | N  | O  | F  | Ne
  | Na | Mg                                                   | Al | Si | P  | S  | Cl | Ar
  | K  | Ca | Sc | Ti | V  | Cr | Mn | Fe | Co | Ni | Cu | Zn | Ga | Ge | As | Se | Br | Kr
  | Rb | Sr | Y  | Zr | Nb | Mo | Tc | Ru | Rh | Pd | Ag | Cd | In | Sn | Sb | Te | I  | Xe
  | Cs | Ba | La
            | Ce | Pr | Nd | Pm | Sm | Eu | Gd
            | Tb | Dy | Ho | Er | Tm | Yb | Lu
                 | Hf | Ta | W  | Re | Os | Ir | Pt | Au | Hg | Tl | Pb | Bi | Po | At | Rn
  | Fr | Ra | Ac
            | Th | Pa | U  | Np | Pu | Am | Cm
            | Bk | Cf | Es | Fm | Md | No | Lr
                 | Rf | Db | Sg | Bh | Hs | Mt | Ds | Rg | Cn | Nh | Fl | Mc | Lv | Ts | Og

%runElab derive "Elem" [Show, Eq, Ord]

--------------------------------------------------------------------------------
--          Conversion from and to AtomicNr
--------------------------------------------------------------------------------

||| This is a proof that we can safely compute an atomic number
||| from each element's index
export
0 indexLemma : (e : Elem) -> IsAtomicNr (conIndexElem e + 1)
indexLemma H  = %search
indexLemma He = %search
indexLemma Li = %search
indexLemma Be = %search
indexLemma B  = %search
indexLemma C  = %search
indexLemma N  = %search
indexLemma O  = %search
indexLemma F  = %search
indexLemma Ne = %search
indexLemma Na = %search
indexLemma Mg = %search
indexLemma Al = %search
indexLemma Si = %search
indexLemma P  = %search
indexLemma S  = %search
indexLemma Cl = %search
indexLemma Ar = %search
indexLemma K  = %search
indexLemma Ca = %search
indexLemma Sc = %search
indexLemma Ti = %search
indexLemma V  = %search
indexLemma Cr = %search
indexLemma Mn = %search
indexLemma Fe = %search
indexLemma Co = %search
indexLemma Ni = %search
indexLemma Cu = %search
indexLemma Zn = %search
indexLemma Ga = %search
indexLemma Ge = %search
indexLemma As = %search
indexLemma Se = %search
indexLemma Br = %search
indexLemma Kr = %search
indexLemma Rb = %search
indexLemma Sr = %search
indexLemma Y  = %search
indexLemma Zr = %search
indexLemma Nb = %search
indexLemma Mo = %search
indexLemma Tc = %search
indexLemma Ru = %search
indexLemma Rh = %search
indexLemma Pd = %search
indexLemma Ag = %search
indexLemma Cd = %search
indexLemma In = %search
indexLemma Sn = %search
indexLemma Sb = %search
indexLemma Te = %search
indexLemma I  = %search
indexLemma Xe = %search
indexLemma Cs = %search
indexLemma Ba = %search
indexLemma La = %search
indexLemma Ce = %search
indexLemma Pr = %search
indexLemma Nd = %search
indexLemma Pm = %search
indexLemma Sm = %search
indexLemma Eu = %search
indexLemma Gd = %search
indexLemma Tb = %search
indexLemma Dy = %search
indexLemma Ho = %search
indexLemma Er = %search
indexLemma Tm = %search
indexLemma Yb = %search
indexLemma Lu = %search
indexLemma Hf = %search
indexLemma Ta = %search
indexLemma W  = %search
indexLemma Re = %search
indexLemma Os = %search
indexLemma Ir = %search
indexLemma Pt = %search
indexLemma Au = %search
indexLemma Hg = %search
indexLemma Tl = %search
indexLemma Pb = %search
indexLemma Bi = %search
indexLemma Po = %search
indexLemma At = %search
indexLemma Rn = %search
indexLemma Fr = %search
indexLemma Ra = %search
indexLemma Ac = %search
indexLemma Th = %search
indexLemma Pa = %search
indexLemma U  = %search
indexLemma Np = %search
indexLemma Pu = %search
indexLemma Am = %search
indexLemma Cm = %search
indexLemma Bk = %search
indexLemma Cf = %search
indexLemma Es = %search
indexLemma Fm = %search
indexLemma Md = %search
indexLemma No = %search
indexLemma Lr = %search
indexLemma Rf = %search
indexLemma Db = %search
indexLemma Sg = %search
indexLemma Bh = %search
indexLemma Hs = %search
indexLemma Mt = %search
indexLemma Ds = %search
indexLemma Rg = %search
indexLemma Cn = %search
indexLemma Nh = %search
indexLemma Fl = %search
indexLemma Mc = %search
indexLemma Lv = %search
indexLemma Ts = %search
indexLemma Og = %search

public export %inline
atomicNr : Elem -> AtomicNr
atomicNr e = MkAtomicNr (conIndexElem e + 1) @{indexLemma e}

public export
fromAtomicNr : AtomicNr -> Elem
fromAtomicNr 6   = C
fromAtomicNr 8   = O
fromAtomicNr 7   = N
fromAtomicNr 1   = H
fromAtomicNr 2   = He
fromAtomicNr 3   = Li
fromAtomicNr 4   = Be
fromAtomicNr 5   = B
fromAtomicNr 9   = F
fromAtomicNr 10  = Ne
fromAtomicNr 11  = Na
fromAtomicNr 12  = Mg
fromAtomicNr 13  = Al
fromAtomicNr 14  = Si
fromAtomicNr 15  = P
fromAtomicNr 16  = S
fromAtomicNr 17  = Cl
fromAtomicNr 18  = Ar
fromAtomicNr 19  = K
fromAtomicNr 20  = Ca
fromAtomicNr 21  = Sc
fromAtomicNr 22  = Ti
fromAtomicNr 23  = V
fromAtomicNr 24  = Cr
fromAtomicNr 25  = Mn
fromAtomicNr 26  = Fe
fromAtomicNr 27  = Co
fromAtomicNr 28  = Ni
fromAtomicNr 29  = Cu
fromAtomicNr 30  = Zn
fromAtomicNr 31  = Ga
fromAtomicNr 32  = Ge
fromAtomicNr 33  = As
fromAtomicNr 34  = Se
fromAtomicNr 35  = Br
fromAtomicNr 36  = Kr
fromAtomicNr 37  = Rb
fromAtomicNr 38  = Sr
fromAtomicNr 39  = Y
fromAtomicNr 40  = Zr
fromAtomicNr 41  = Nb
fromAtomicNr 42  = Mo
fromAtomicNr 43  = Tc
fromAtomicNr 44  = Ru
fromAtomicNr 45  = Rh
fromAtomicNr 46  = Pd
fromAtomicNr 47  = Ag
fromAtomicNr 48  = Cd
fromAtomicNr 49  = In
fromAtomicNr 50  = Sn
fromAtomicNr 51  = Sb
fromAtomicNr 52  = Te
fromAtomicNr 53  = I
fromAtomicNr 54  = Xe
fromAtomicNr 55  = Cs
fromAtomicNr 56  = Ba
fromAtomicNr 57  = La
fromAtomicNr 58  = Ce
fromAtomicNr 59  = Pr
fromAtomicNr 60  = Nd
fromAtomicNr 61  = Pm
fromAtomicNr 62  = Sm
fromAtomicNr 63  = Eu
fromAtomicNr 64  = Gd
fromAtomicNr 65  = Tb
fromAtomicNr 66  = Dy
fromAtomicNr 67  = Ho
fromAtomicNr 68  = Er
fromAtomicNr 69  = Tm
fromAtomicNr 70  = Yb
fromAtomicNr 71  = Lu
fromAtomicNr 72  = Hf
fromAtomicNr 73  = Ta
fromAtomicNr 74  = W
fromAtomicNr 75  = Re
fromAtomicNr 76  = Os
fromAtomicNr 77  = Ir
fromAtomicNr 78  = Pt
fromAtomicNr 79  = Au
fromAtomicNr 80  = Hg
fromAtomicNr 81  = Tl
fromAtomicNr 82  = Pb
fromAtomicNr 83  = Bi
fromAtomicNr 84  = Po
fromAtomicNr 85  = At
fromAtomicNr 86  = Rn
fromAtomicNr 87  = Fr
fromAtomicNr 88  = Ra
fromAtomicNr 89  = Ac
fromAtomicNr 90  = Th
fromAtomicNr 91  = Pa
fromAtomicNr 92  = U
fromAtomicNr 93  = Np
fromAtomicNr 94  = Pu
fromAtomicNr 95  = Am
fromAtomicNr 96  = Cm
fromAtomicNr 97  = Bk
fromAtomicNr 98  = Cf
fromAtomicNr 99  = Es
fromAtomicNr 100 = Fm
fromAtomicNr 101 = Md
fromAtomicNr 102 = No
fromAtomicNr 103 = Lr
fromAtomicNr 104 = Rf
fromAtomicNr 105 = Db
fromAtomicNr 106 = Sg
fromAtomicNr 107 = Bh
fromAtomicNr 108 = Hs
fromAtomicNr 109 = Mt
fromAtomicNr 110 = Ds
fromAtomicNr 111 = Rg
fromAtomicNr 112 = Cn
fromAtomicNr 113 = Nh
fromAtomicNr 114 = Fl
fromAtomicNr 115 = Mc
fromAtomicNr 116 = Lv
fromAtomicNr 117 = Ts
fromAtomicNr 118 = Og

-- this is just an additional measure of safety:
-- if we ever increase the valid range of atomic numbers
-- Idris will shout at us here that this case is actually
-- not impossible.
fromAtomicNr (MkAtomicNr 119 prf) impossible

-- since we are dealing with primitive `Bits8` here,
-- Idris needs our help to figure out that we have reached the end
-- of possible inputs.
fromAtomicNr x   =
  assert_total $
  idris_crash "fromAtomicNr called with invalid AtomicNr: \{show x}"

--------------------------------------------------------------------------------
--          Converting from and to String
--------------------------------------------------------------------------------

public export
fromSymbol : String -> Maybe Elem
fromSymbol "C"   = Just C
fromSymbol "O"   = Just O
fromSymbol "N"   = Just N
fromSymbol "H"   = Just H
fromSymbol "He"  = Just He
fromSymbol "Li"  = Just Li
fromSymbol "Be"  = Just Be
fromSymbol "B"   = Just B
fromSymbol "F"   = Just F
fromSymbol "Ne"  = Just Ne
fromSymbol "Na"  = Just Na
fromSymbol "Mg"  = Just Mg
fromSymbol "Al"  = Just Al
fromSymbol "Si"  = Just Si
fromSymbol "P"   = Just P
fromSymbol "S"   = Just S
fromSymbol "Cl"  = Just Cl
fromSymbol "Ar"  = Just Ar
fromSymbol "K"   = Just K
fromSymbol "Ca"  = Just Ca
fromSymbol "Sc"  = Just Sc
fromSymbol "Ti"  = Just Ti
fromSymbol "V"   = Just V
fromSymbol "Cr"  = Just Cr
fromSymbol "Mn"  = Just Mn
fromSymbol "Fe"  = Just Fe
fromSymbol "Co"  = Just Co
fromSymbol "Ni"  = Just Ni
fromSymbol "Cu"  = Just Cu
fromSymbol "Zn"  = Just Zn
fromSymbol "Ga"  = Just Ga
fromSymbol "Ge"  = Just Ge
fromSymbol "As"  = Just As
fromSymbol "Se"  = Just Se
fromSymbol "Br"  = Just Br
fromSymbol "Kr"  = Just Kr
fromSymbol "Rb"  = Just Rb
fromSymbol "Sr"  = Just Sr
fromSymbol "Y"   = Just Y
fromSymbol "Zr"  = Just Zr
fromSymbol "Nb"  = Just Nb
fromSymbol "Mo"  = Just Mo
fromSymbol "Tc"  = Just Tc
fromSymbol "Ru"  = Just Ru
fromSymbol "Rh"  = Just Rh
fromSymbol "Pd"  = Just Pd
fromSymbol "Ag"  = Just Ag
fromSymbol "Cd"  = Just Cd
fromSymbol "In"  = Just In
fromSymbol "Sn"  = Just Sn
fromSymbol "Sb"  = Just Sb
fromSymbol "Te"  = Just Te
fromSymbol "I"   = Just I
fromSymbol "Xe"  = Just Xe
fromSymbol "Cs"  = Just Cs
fromSymbol "Ba"  = Just Ba
fromSymbol "La"  = Just La
fromSymbol "Ce"  = Just Ce
fromSymbol "Pr"  = Just Pr
fromSymbol "Nd"  = Just Nd
fromSymbol "Pm"  = Just Pm
fromSymbol "Sm"  = Just Sm
fromSymbol "Eu"  = Just Eu
fromSymbol "Gd"  = Just Gd
fromSymbol "Tb"  = Just Tb
fromSymbol "Dy"  = Just Dy
fromSymbol "Ho"  = Just Ho
fromSymbol "Er"  = Just Er
fromSymbol "Tm"  = Just Tm
fromSymbol "Yb"  = Just Yb
fromSymbol "Lu"  = Just Lu
fromSymbol "Hf"  = Just Hf
fromSymbol "Ta"  = Just Ta
fromSymbol "W"   = Just W
fromSymbol "Re"  = Just Re
fromSymbol "Os"  = Just Os
fromSymbol "Ir"  = Just Ir
fromSymbol "Pt"  = Just Pt
fromSymbol "Au"  = Just Au
fromSymbol "Hg"  = Just Hg
fromSymbol "Tl"  = Just Tl
fromSymbol "Pb"  = Just Pb
fromSymbol "Bi"  = Just Bi
fromSymbol "Po"  = Just Po
fromSymbol "At"  = Just At
fromSymbol "Rn"  = Just Rn
fromSymbol "Fr"  = Just Fr
fromSymbol "Ra"  = Just Ra
fromSymbol "Ac"  = Just Ac
fromSymbol "Th"  = Just Th
fromSymbol "Pa"  = Just Pa
fromSymbol "U"   = Just U
fromSymbol "Np"  = Just Np
fromSymbol "Pu"  = Just Pu
fromSymbol "Am"  = Just Am
fromSymbol "Cm"  = Just Cm
fromSymbol "Bk"  = Just Bk
fromSymbol "Cf"  = Just Cf
fromSymbol "Es"  = Just Es
fromSymbol "Fm"  = Just Fm
fromSymbol "Md"  = Just Md
fromSymbol "No"  = Just No
fromSymbol "Lr"  = Just Lr
fromSymbol "Rf"  = Just Rf
fromSymbol "Db"  = Just Db
fromSymbol "Sg"  = Just Sg
fromSymbol "Bh"  = Just Bh
fromSymbol "Hs"  = Just Hs
fromSymbol "Mt"  = Just Mt
fromSymbol "Ds"  = Just Ds
fromSymbol "Rg"  = Just Rg
fromSymbol "Cn"  = Just Cn
fromSymbol "Nh"  = Just Nh
fromSymbol "Fl"  = Just Fl
fromSymbol "Mc"  = Just Mc
fromSymbol "Lv"  = Just Lv
fromSymbol "Ts"  = Just Ts
fromSymbol "Og"  = Just Og
fromSymbol _     = Nothing

public export %inline
symbol : Elem -> String
symbol = show

public export
readMsg : String -> Either String Elem
readMsg = mkReadE fromSymbol "Elem"

public export
readE : String -> (String -> err) -> Either err Elem
readE s f = maybe (Left $ f s) Right $ fromSymbol s

public export %inline
write : Elem -> String
write = symbol

--------------------------------------------------------------------------------
--          Aromaticity
--------------------------------------------------------------------------------

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
  {auto 0 prf : ValidAromatic elem arom}
