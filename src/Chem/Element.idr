module Chem.Element

import Chem.Types
import Text.RW

%default total

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

--------------------------------------------------------------------------------
--          Conversion from and to AtomicNr
--------------------------------------------------------------------------------

||| Converts an `Elem` to the corresponding index of the enum type.
|||
||| Note: This is the identity function, so it will be completely removed
||| during compilation.
public export
toIndex : Elem -> Bits8
toIndex H  = 0
toIndex He = 1
toIndex Li = 2
toIndex Be = 3
toIndex B  = 4
toIndex C  = 5
toIndex N  = 6
toIndex O  = 7
toIndex F  = 8
toIndex Ne = 9
toIndex Na = 10
toIndex Mg = 11
toIndex Al = 12
toIndex Si = 13
toIndex P  = 14
toIndex S  = 15
toIndex Cl = 16
toIndex Ar = 17
toIndex K  = 18
toIndex Ca = 19
toIndex Sc = 20
toIndex Ti = 21
toIndex V  = 22
toIndex Cr = 23
toIndex Mn = 24
toIndex Fe = 25
toIndex Co = 26
toIndex Ni = 27
toIndex Cu = 28
toIndex Zn = 29
toIndex Ga = 30
toIndex Ge = 31
toIndex As = 32
toIndex Se = 33
toIndex Br = 34
toIndex Kr = 35
toIndex Rb = 36
toIndex Sr = 37
toIndex Y  = 38
toIndex Zr = 39
toIndex Nb = 40
toIndex Mo = 41
toIndex Tc = 42
toIndex Ru = 43
toIndex Rh = 44
toIndex Pd = 45
toIndex Ag = 46
toIndex Cd = 47
toIndex In = 48
toIndex Sn = 49
toIndex Sb = 50
toIndex Te = 51
toIndex I  = 52
toIndex Xe = 53
toIndex Cs = 54
toIndex Ba = 55
toIndex La = 56
toIndex Ce = 57
toIndex Pr = 58
toIndex Nd = 59
toIndex Pm = 60
toIndex Sm = 61
toIndex Eu = 62
toIndex Gd = 63
toIndex Tb = 64
toIndex Dy = 65
toIndex Ho = 66
toIndex Er = 67
toIndex Tm = 68
toIndex Yb = 69
toIndex Lu = 70
toIndex Hf = 71
toIndex Ta = 72
toIndex W  = 73
toIndex Re = 74
toIndex Os = 75
toIndex Ir = 76
toIndex Pt = 77
toIndex Au = 78
toIndex Hg = 79
toIndex Tl = 80
toIndex Pb = 81
toIndex Bi = 82
toIndex Po = 83
toIndex At = 84
toIndex Rn = 85
toIndex Fr = 86
toIndex Ra = 87
toIndex Ac = 88
toIndex Th = 89
toIndex Pa = 90
toIndex U  = 91
toIndex Np = 92
toIndex Pu = 93
toIndex Am = 94
toIndex Cm = 95
toIndex Bk = 96
toIndex Cf = 97
toIndex Es = 98
toIndex Fm = 99
toIndex Md = 100
toIndex No = 101
toIndex Lr = 102
toIndex Rf = 103
toIndex Db = 104
toIndex Sg = 105
toIndex Bh = 106
toIndex Hs = 107
toIndex Mt = 108
toIndex Ds = 109
toIndex Rg = 110
toIndex Cn = 111
toIndex Nh = 112
toIndex Fl = 113
toIndex Mc = 114
toIndex Lv = 115
toIndex Ts = 116
toIndex Og = 117

||| This is a proof that we can safely compute an atomic number
||| from each element's index
export
0 indexLemma : (e : Elem) -> So (isAtomicNr (toIndex e + 1))
indexLemma H  = Oh
indexLemma He = Oh
indexLemma Li = Oh
indexLemma Be = Oh
indexLemma B  = Oh
indexLemma C  = Oh
indexLemma N  = Oh
indexLemma O  = Oh
indexLemma F  = Oh
indexLemma Ne = Oh
indexLemma Na = Oh
indexLemma Mg = Oh
indexLemma Al = Oh
indexLemma Si = Oh
indexLemma P  = Oh
indexLemma S  = Oh
indexLemma Cl = Oh
indexLemma Ar = Oh
indexLemma K  = Oh
indexLemma Ca = Oh
indexLemma Sc = Oh
indexLemma Ti = Oh
indexLemma V  = Oh
indexLemma Cr = Oh
indexLemma Mn = Oh
indexLemma Fe = Oh
indexLemma Co = Oh
indexLemma Ni = Oh
indexLemma Cu = Oh
indexLemma Zn = Oh
indexLemma Ga = Oh
indexLemma Ge = Oh
indexLemma As = Oh
indexLemma Se = Oh
indexLemma Br = Oh
indexLemma Kr = Oh
indexLemma Rb = Oh
indexLemma Sr = Oh
indexLemma Y  = Oh
indexLemma Zr = Oh
indexLemma Nb = Oh
indexLemma Mo = Oh
indexLemma Tc = Oh
indexLemma Ru = Oh
indexLemma Rh = Oh
indexLemma Pd = Oh
indexLemma Ag = Oh
indexLemma Cd = Oh
indexLemma In = Oh
indexLemma Sn = Oh
indexLemma Sb = Oh
indexLemma Te = Oh
indexLemma I  = Oh
indexLemma Xe = Oh
indexLemma Cs = Oh
indexLemma Ba = Oh
indexLemma La = Oh
indexLemma Ce = Oh
indexLemma Pr = Oh
indexLemma Nd = Oh
indexLemma Pm = Oh
indexLemma Sm = Oh
indexLemma Eu = Oh
indexLemma Gd = Oh
indexLemma Tb = Oh
indexLemma Dy = Oh
indexLemma Ho = Oh
indexLemma Er = Oh
indexLemma Tm = Oh
indexLemma Yb = Oh
indexLemma Lu = Oh
indexLemma Hf = Oh
indexLemma Ta = Oh
indexLemma W  = Oh
indexLemma Re = Oh
indexLemma Os = Oh
indexLemma Ir = Oh
indexLemma Pt = Oh
indexLemma Au = Oh
indexLemma Hg = Oh
indexLemma Tl = Oh
indexLemma Pb = Oh
indexLemma Bi = Oh
indexLemma Po = Oh
indexLemma At = Oh
indexLemma Rn = Oh
indexLemma Fr = Oh
indexLemma Ra = Oh
indexLemma Ac = Oh
indexLemma Th = Oh
indexLemma Pa = Oh
indexLemma U  = Oh
indexLemma Np = Oh
indexLemma Pu = Oh
indexLemma Am = Oh
indexLemma Cm = Oh
indexLemma Bk = Oh
indexLemma Cf = Oh
indexLemma Es = Oh
indexLemma Fm = Oh
indexLemma Md = Oh
indexLemma No = Oh
indexLemma Lr = Oh
indexLemma Rf = Oh
indexLemma Db = Oh
indexLemma Sg = Oh
indexLemma Bh = Oh
indexLemma Hs = Oh
indexLemma Mt = Oh
indexLemma Ds = Oh
indexLemma Rg = Oh
indexLemma Cn = Oh
indexLemma Nh = Oh
indexLemma Fl = Oh
indexLemma Mc = Oh
indexLemma Lv = Oh
indexLemma Ts = Oh
indexLemma Og = Oh

public export
atomicNr : Elem -> AtomicNr
atomicNr e = MkAtomicNr (toIndex e + 1) (indexLemma e)

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
  idris_crash #"fromAtomicNr called with invalid AtomicNr: \#{show x}"#

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

public export
symbol : Elem -> String
symbol H   = "H"
symbol He  = "He"
symbol Li  = "Li"
symbol Be  = "Be"
symbol B   = "B"
symbol C   = "C"
symbol N   = "N"
symbol O   = "O"
symbol F   = "F"
symbol Ne  = "Ne"
symbol Na  = "Na"
symbol Mg  = "Mg"
symbol Al  = "Al"
symbol Si  = "Si"
symbol P   = "P"
symbol S   = "S"
symbol Cl  = "Cl"
symbol Ar  = "Ar"
symbol K   = "K"
symbol Ca  = "Ca"
symbol Sc  = "Sc"
symbol Ti  = "Ti"
symbol V   = "V"
symbol Cr  = "Cr"
symbol Mn  = "Mn"
symbol Fe  = "Fe"
symbol Co  = "Co"
symbol Ni  = "Ni"
symbol Cu  = "Cu"
symbol Zn  = "Zn"
symbol Ga  = "Ga"
symbol Ge  = "Ge"
symbol As  = "As"
symbol Se  = "Se"
symbol Br  = "Br"
symbol Kr  = "Kr"
symbol Rb  = "Rb"
symbol Sr  = "Sr"
symbol Y   = "Y"
symbol Zr  = "Zr"
symbol Nb  = "Nb"
symbol Mo  = "Mo"
symbol Tc  = "Tc"
symbol Ru  = "Ru"
symbol Rh  = "Rh"
symbol Pd  = "Pd"
symbol Ag  = "Ag"
symbol Cd  = "Cd"
symbol In  = "In"
symbol Sn  = "Sn"
symbol Sb  = "Sb"
symbol Te  = "Te"
symbol I   = "I"
symbol Xe  = "Xe"
symbol Cs  = "Cs"
symbol Ba  = "Ba"
symbol La  = "La"
symbol Ce  = "Ce"
symbol Pr  = "Pr"
symbol Nd  = "Nd"
symbol Pm  = "Pm"
symbol Sm  = "Sm"
symbol Eu  = "Eu"
symbol Gd  = "Gd"
symbol Tb  = "Tb"
symbol Dy  = "Dy"
symbol Ho  = "Ho"
symbol Er  = "Er"
symbol Tm  = "Tm"
symbol Yb  = "Yb"
symbol Lu  = "Lu"
symbol Hf  = "Hf"
symbol Ta  = "Ta"
symbol W   = "W"
symbol Re  = "Re"
symbol Os  = "Os"
symbol Ir  = "Ir"
symbol Pt  = "Pt"
symbol Au  = "Au"
symbol Hg  = "Hg"
symbol Tl  = "Tl"
symbol Pb  = "Pb"
symbol Bi  = "Bi"
symbol Po  = "Po"
symbol At  = "At"
symbol Rn  = "Rn"
symbol Fr  = "Fr"
symbol Ra  = "Ra"
symbol Ac  = "Ac"
symbol Th  = "Th"
symbol Pa  = "Pa"
symbol U   = "U"
symbol Np  = "Np"
symbol Pu  = "Pu"
symbol Am  = "Am"
symbol Cm  = "Cm"
symbol Bk  = "Bk"
symbol Cf  = "Cf"
symbol Es  = "Es"
symbol Fm  = "Fm"
symbol Md  = "Md"
symbol No  = "No"
symbol Lr  = "Lr"
symbol Rf  = "Rf"
symbol Db  = "Db"
symbol Sg  = "Sg"
symbol Bh  = "Bh"
symbol Hs  = "Hs"
symbol Mt  = "Mt"
symbol Ds  = "Ds"
symbol Rg  = "Rg"
symbol Cn  = "Cn"
symbol Nh  = "Nh"
symbol Fl  = "Fl"
symbol Mc  = "Mc"
symbol Lv  = "Lv"
symbol Ts  = "Ts"
symbol Og  = "Og"

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
--          Implementations
--------------------------------------------------------------------------------

public export %inline
Eq Elem where
  x == y = toIndex x == toIndex y

public export %inline
Ord Elem where
  compare x y = compare (toIndex x) (toIndex y)

export %inline
Show Elem where
  show = symbol
