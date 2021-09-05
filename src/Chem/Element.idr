module Chem.Element

import Chem.Types

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
                 | Rf | Db | Sg | Bh | Hs | Mt | Ds | Rg | Cn | Uut | Fl | Uup | Lv | Uus | Uuo

--------------------------------------------------------------------------------
--          Conversion from and to AtomicNr
--------------------------------------------------------------------------------

public export
atomicNr : Elem -> AtomicNr
atomicNr H   = 1
atomicNr He  = 2
atomicNr Li  = 3
atomicNr Be  = 4
atomicNr B   = 5
atomicNr C   = 6
atomicNr N   = 7
atomicNr O   = 8
atomicNr F   = 9
atomicNr Ne  = 10
atomicNr Na  = 11
atomicNr Mg  = 12
atomicNr Al  = 13
atomicNr Si  = 14
atomicNr P   = 15
atomicNr S   = 16
atomicNr Cl  = 17
atomicNr Ar  = 18
atomicNr K   = 19
atomicNr Ca  = 20
atomicNr Sc  = 21
atomicNr Ti  = 22
atomicNr V   = 23
atomicNr Cr  = 24
atomicNr Mn  = 25
atomicNr Fe  = 26
atomicNr Co  = 27
atomicNr Ni  = 28
atomicNr Cu  = 29
atomicNr Zn  = 30
atomicNr Ga  = 31
atomicNr Ge  = 32
atomicNr As  = 33
atomicNr Se  = 34
atomicNr Br  = 35
atomicNr Kr  = 36
atomicNr Rb  = 37
atomicNr Sr  = 38
atomicNr Y   = 39
atomicNr Zr  = 40
atomicNr Nb  = 41
atomicNr Mo  = 42
atomicNr Tc  = 43
atomicNr Ru  = 44
atomicNr Rh  = 45
atomicNr Pd  = 46
atomicNr Ag  = 47
atomicNr Cd  = 48
atomicNr In  = 49
atomicNr Sn  = 50
atomicNr Sb  = 51
atomicNr Te  = 52
atomicNr I   = 53
atomicNr Xe  = 54
atomicNr Cs  = 55
atomicNr Ba  = 56
atomicNr La  = 57
atomicNr Ce  = 58
atomicNr Pr  = 59
atomicNr Nd  = 60
atomicNr Pm  = 61
atomicNr Sm  = 62
atomicNr Eu  = 63
atomicNr Gd  = 64
atomicNr Tb  = 65
atomicNr Dy  = 66
atomicNr Ho  = 67
atomicNr Er  = 68
atomicNr Tm  = 69
atomicNr Yb  = 70
atomicNr Lu  = 71
atomicNr Hf  = 72
atomicNr Ta  = 73
atomicNr W   = 74
atomicNr Re  = 75
atomicNr Os  = 76
atomicNr Ir  = 77
atomicNr Pt  = 78
atomicNr Au  = 79
atomicNr Hg  = 80
atomicNr Tl  = 81
atomicNr Pb  = 82
atomicNr Bi  = 83
atomicNr Po  = 84
atomicNr At  = 85
atomicNr Rn  = 86
atomicNr Fr  = 87
atomicNr Ra  = 88
atomicNr Ac  = 89
atomicNr Th  = 90
atomicNr Pa  = 91
atomicNr U   = 92
atomicNr Np  = 93
atomicNr Pu  = 94
atomicNr Am  = 95
atomicNr Cm  = 96
atomicNr Bk  = 97
atomicNr Cf  = 98
atomicNr Es  = 99
atomicNr Fm  = 100
atomicNr Md  = 101
atomicNr No  = 102
atomicNr Lr  = 103
atomicNr Rf  = 104
atomicNr Db  = 105
atomicNr Sg  = 106
atomicNr Bh  = 107
atomicNr Hs  = 108
atomicNr Mt  = 109
atomicNr Ds  = 110
atomicNr Rg  = 111
atomicNr Cn  = 112
atomicNr Uut = 113
atomicNr Fl  = 114
atomicNr Uup = 115
atomicNr Lv  = 116
atomicNr Uus = 117
atomicNr Uuo = 118

public export
fromAtomicNr : AtomicNr -> Elem
fromAtomicNr 1   = H
fromAtomicNr 2   = He
fromAtomicNr 3   = Li
fromAtomicNr 4   = Be
fromAtomicNr 5   = B
fromAtomicNr 6   = C
fromAtomicNr 7   = N
fromAtomicNr 8   = O
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
fromAtomicNr 113 = Uut
fromAtomicNr 114 = Fl
fromAtomicNr 115 = Uup
fromAtomicNr 116 = Lv
fromAtomicNr 117 = Uus
fromAtomicNr 118 = Uuo

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

export
read : String -> Maybe Elem
read "H"   = Just H
read "He"  = Just He
read "Li"  = Just Li
read "Be"  = Just Be
read "B"   = Just B
read "C"   = Just C
read "N"   = Just N
read "O"   = Just O
read "F"   = Just F
read "Ne"  = Just Ne
read "Na"  = Just Na
read "Mg"  = Just Mg
read "Al"  = Just Al
read "Si"  = Just Si
read "P"   = Just P
read "S"   = Just S
read "Cl"  = Just Cl
read "Ar"  = Just Ar
read "K"   = Just K
read "Ca"  = Just Ca
read "Sc"  = Just Sc
read "Ti"  = Just Ti
read "V"   = Just V
read "Cr"  = Just Cr
read "Mn"  = Just Mn
read "Fe"  = Just Fe
read "Co"  = Just Co
read "Ni"  = Just Ni
read "Cu"  = Just Cu
read "Zn"  = Just Zn
read "Ga"  = Just Ga
read "Ge"  = Just Ge
read "As"  = Just As
read "Se"  = Just Se
read "Br"  = Just Br
read "Kr"  = Just Kr
read "Rb"  = Just Rb
read "Sr"  = Just Sr
read "Y"   = Just Y
read "Zr"  = Just Zr
read "Nb"  = Just Nb
read "Mo"  = Just Mo
read "Tc"  = Just Tc
read "Ru"  = Just Ru
read "Rh"  = Just Rh
read "Pd"  = Just Pd
read "Ag"  = Just Ag
read "Cd"  = Just Cd
read "In"  = Just In
read "Sn"  = Just Sn
read "Sb"  = Just Sb
read "Te"  = Just Te
read "I"   = Just I
read "Xe"  = Just Xe
read "Cs"  = Just Cs
read "Ba"  = Just Ba
read "La"  = Just La
read "Ce"  = Just Ce
read "Pr"  = Just Pr
read "Nd"  = Just Nd
read "Pm"  = Just Pm
read "Sm"  = Just Sm
read "Eu"  = Just Eu
read "Gd"  = Just Gd
read "Tb"  = Just Tb
read "Dy"  = Just Dy
read "Ho"  = Just Ho
read "Er"  = Just Er
read "Tm"  = Just Tm
read "Yb"  = Just Yb
read "Lu"  = Just Lu
read "Hf"  = Just Hf
read "Ta"  = Just Ta
read "W"   = Just W
read "Re"  = Just Re
read "Os"  = Just Os
read "Ir"  = Just Ir
read "Pt"  = Just Pt
read "Au"  = Just Au
read "Hg"  = Just Hg
read "Tl"  = Just Tl
read "Pb"  = Just Pb
read "Bi"  = Just Bi
read "Po"  = Just Po
read "At"  = Just At
read "Rn"  = Just Rn
read "Fr"  = Just Fr
read "Ra"  = Just Ra
read "Ac"  = Just Ac
read "Th"  = Just Th
read "Pa"  = Just Pa
read "U"   = Just U
read "Np"  = Just Np
read "Pu"  = Just Pu
read "Am"  = Just Am
read "Cm"  = Just Cm
read "Bk"  = Just Bk
read "Cf"  = Just Cf
read "Es"  = Just Es
read "Fm"  = Just Fm
read "Md"  = Just Md
read "No"  = Just No
read "Lr"  = Just Lr
read "Rf"  = Just Rf
read "Db"  = Just Db
read "Sg"  = Just Sg
read "Bh"  = Just Bh
read "Hs"  = Just Hs
read "Mt"  = Just Mt
read "Ds"  = Just Ds
read "Rg"  = Just Rg
read "Cn"  = Just Cn
read "Uut" = Just Uut
read "Fl"  = Just Fl
read "Uup" = Just Uup
read "Lv"  = Just Lv
read "Uus" = Just Uus
read "Uuo" = Just Uuo
read _     = Nothing

export
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
symbol Uut = "Uut"
symbol Fl  = "Fl"
symbol Uup = "Uup"
symbol Lv  = "Lv"
symbol Uus = "Uus"
symbol Uuo = "Uuo"

--------------------------------------------------------------------------------
--          Implementations
--------------------------------------------------------------------------------

public export
Eq Elem where
  (==) = (==) `on` atomicNr

public export
Ord Elem where
  compare = compare `on` atomicNr

export %inline
Show Elem where
  show = symbol

--------------------------------------------------------------------------------
--          Proofs
--------------------------------------------------------------------------------

-- proof that `fromAtomicNr` is the invers of `atomicNr`
elemAtomicNrIso : (e : Elem) -> e = fromAtomicNr (atomicNr e)
elemAtomicNrIso H   = Refl
elemAtomicNrIso He  = Refl
elemAtomicNrIso Li  = Refl
elemAtomicNrIso Be  = Refl
elemAtomicNrIso B   = Refl
elemAtomicNrIso C   = Refl
elemAtomicNrIso N   = Refl
elemAtomicNrIso O   = Refl
elemAtomicNrIso F   = Refl
elemAtomicNrIso Ne  = Refl
elemAtomicNrIso Na  = Refl
elemAtomicNrIso Mg  = Refl
elemAtomicNrIso Al  = Refl
elemAtomicNrIso Si  = Refl
elemAtomicNrIso P   = Refl
elemAtomicNrIso S   = Refl
elemAtomicNrIso Cl  = Refl
elemAtomicNrIso Ar  = Refl
elemAtomicNrIso K   = Refl
elemAtomicNrIso Ca  = Refl
elemAtomicNrIso Sc  = Refl
elemAtomicNrIso Ti  = Refl
elemAtomicNrIso V   = Refl
elemAtomicNrIso Cr  = Refl
elemAtomicNrIso Mn  = Refl
elemAtomicNrIso Fe  = Refl
elemAtomicNrIso Co  = Refl
elemAtomicNrIso Ni  = Refl
elemAtomicNrIso Cu  = Refl
elemAtomicNrIso Zn  = Refl
elemAtomicNrIso Ga  = Refl
elemAtomicNrIso Ge  = Refl
elemAtomicNrIso As  = Refl
elemAtomicNrIso Se  = Refl
elemAtomicNrIso Br  = Refl
elemAtomicNrIso Kr  = Refl
elemAtomicNrIso Rb  = Refl
elemAtomicNrIso Sr  = Refl
elemAtomicNrIso Y   = Refl
elemAtomicNrIso Zr  = Refl
elemAtomicNrIso Nb  = Refl
elemAtomicNrIso Mo  = Refl
elemAtomicNrIso Tc  = Refl
elemAtomicNrIso Ru  = Refl
elemAtomicNrIso Rh  = Refl
elemAtomicNrIso Pd  = Refl
elemAtomicNrIso Ag  = Refl
elemAtomicNrIso Cd  = Refl
elemAtomicNrIso In  = Refl
elemAtomicNrIso Sn  = Refl
elemAtomicNrIso Sb  = Refl
elemAtomicNrIso Te  = Refl
elemAtomicNrIso I   = Refl
elemAtomicNrIso Xe  = Refl
elemAtomicNrIso Cs  = Refl
elemAtomicNrIso Ba  = Refl
elemAtomicNrIso La  = Refl
elemAtomicNrIso Ce  = Refl
elemAtomicNrIso Pr  = Refl
elemAtomicNrIso Nd  = Refl
elemAtomicNrIso Pm  = Refl
elemAtomicNrIso Sm  = Refl
elemAtomicNrIso Eu  = Refl
elemAtomicNrIso Gd  = Refl
elemAtomicNrIso Tb  = Refl
elemAtomicNrIso Dy  = Refl
elemAtomicNrIso Ho  = Refl
elemAtomicNrIso Er  = Refl
elemAtomicNrIso Tm  = Refl
elemAtomicNrIso Yb  = Refl
elemAtomicNrIso Lu  = Refl
elemAtomicNrIso Hf  = Refl
elemAtomicNrIso Ta  = Refl
elemAtomicNrIso W   = Refl
elemAtomicNrIso Re  = Refl
elemAtomicNrIso Os  = Refl
elemAtomicNrIso Ir  = Refl
elemAtomicNrIso Pt  = Refl
elemAtomicNrIso Au  = Refl
elemAtomicNrIso Hg  = Refl
elemAtomicNrIso Tl  = Refl
elemAtomicNrIso Pb  = Refl
elemAtomicNrIso Bi  = Refl
elemAtomicNrIso Po  = Refl
elemAtomicNrIso At  = Refl
elemAtomicNrIso Rn  = Refl
elemAtomicNrIso Fr  = Refl
elemAtomicNrIso Ra  = Refl
elemAtomicNrIso Ac  = Refl
elemAtomicNrIso Th  = Refl
elemAtomicNrIso Pa  = Refl
elemAtomicNrIso U   = Refl
elemAtomicNrIso Np  = Refl
elemAtomicNrIso Pu  = Refl
elemAtomicNrIso Am  = Refl
elemAtomicNrIso Cm  = Refl
elemAtomicNrIso Bk  = Refl
elemAtomicNrIso Cf  = Refl
elemAtomicNrIso Es  = Refl
elemAtomicNrIso Fm  = Refl
elemAtomicNrIso Md  = Refl
elemAtomicNrIso No  = Refl
elemAtomicNrIso Lr  = Refl
elemAtomicNrIso Rf  = Refl
elemAtomicNrIso Db  = Refl
elemAtomicNrIso Sg  = Refl
elemAtomicNrIso Bh  = Refl
elemAtomicNrIso Hs  = Refl
elemAtomicNrIso Mt  = Refl
elemAtomicNrIso Ds  = Refl
elemAtomicNrIso Rg  = Refl
elemAtomicNrIso Cn  = Refl
elemAtomicNrIso Uut = Refl
elemAtomicNrIso Fl  = Refl
elemAtomicNrIso Uup = Refl
elemAtomicNrIso Lv  = Refl
elemAtomicNrIso Uus = Refl
elemAtomicNrIso Uuo = Refl

-- proof that `read` and `symbol` correlate as expected
readFromSymbol : (e : Elem) -> Just e = read (symbol e)
readFromSymbol H   = Refl
readFromSymbol He  = Refl
readFromSymbol Li  = Refl
readFromSymbol Be  = Refl
readFromSymbol B   = Refl
readFromSymbol C   = Refl
readFromSymbol N   = Refl
readFromSymbol O   = Refl
readFromSymbol F   = Refl
readFromSymbol Ne  = Refl
readFromSymbol Na  = Refl
readFromSymbol Mg  = Refl
readFromSymbol Al  = Refl
readFromSymbol Si  = Refl
readFromSymbol P   = Refl
readFromSymbol S   = Refl
readFromSymbol Cl  = Refl
readFromSymbol Ar  = Refl
readFromSymbol K   = Refl
readFromSymbol Ca  = Refl
readFromSymbol Sc  = Refl
readFromSymbol Ti  = Refl
readFromSymbol V   = Refl
readFromSymbol Cr  = Refl
readFromSymbol Mn  = Refl
readFromSymbol Fe  = Refl
readFromSymbol Co  = Refl
readFromSymbol Ni  = Refl
readFromSymbol Cu  = Refl
readFromSymbol Zn  = Refl
readFromSymbol Ga  = Refl
readFromSymbol Ge  = Refl
readFromSymbol As  = Refl
readFromSymbol Se  = Refl
readFromSymbol Br  = Refl
readFromSymbol Kr  = Refl
readFromSymbol Rb  = Refl
readFromSymbol Sr  = Refl
readFromSymbol Y   = Refl
readFromSymbol Zr  = Refl
readFromSymbol Nb  = Refl
readFromSymbol Mo  = Refl
readFromSymbol Tc  = Refl
readFromSymbol Ru  = Refl
readFromSymbol Rh  = Refl
readFromSymbol Pd  = Refl
readFromSymbol Ag  = Refl
readFromSymbol Cd  = Refl
readFromSymbol In  = Refl
readFromSymbol Sn  = Refl
readFromSymbol Sb  = Refl
readFromSymbol Te  = Refl
readFromSymbol I   = Refl
readFromSymbol Xe  = Refl
readFromSymbol Cs  = Refl
readFromSymbol Ba  = Refl
readFromSymbol La  = Refl
readFromSymbol Ce  = Refl
readFromSymbol Pr  = Refl
readFromSymbol Nd  = Refl
readFromSymbol Pm  = Refl
readFromSymbol Sm  = Refl
readFromSymbol Eu  = Refl
readFromSymbol Gd  = Refl
readFromSymbol Tb  = Refl
readFromSymbol Dy  = Refl
readFromSymbol Ho  = Refl
readFromSymbol Er  = Refl
readFromSymbol Tm  = Refl
readFromSymbol Yb  = Refl
readFromSymbol Lu  = Refl
readFromSymbol Hf  = Refl
readFromSymbol Ta  = Refl
readFromSymbol W   = Refl
readFromSymbol Re  = Refl
readFromSymbol Os  = Refl
readFromSymbol Ir  = Refl
readFromSymbol Pt  = Refl
readFromSymbol Au  = Refl
readFromSymbol Hg  = Refl
readFromSymbol Tl  = Refl
readFromSymbol Pb  = Refl
readFromSymbol Bi  = Refl
readFromSymbol Po  = Refl
readFromSymbol At  = Refl
readFromSymbol Rn  = Refl
readFromSymbol Fr  = Refl
readFromSymbol Ra  = Refl
readFromSymbol Ac  = Refl
readFromSymbol Th  = Refl
readFromSymbol Pa  = Refl
readFromSymbol U   = Refl
readFromSymbol Np  = Refl
readFromSymbol Pu  = Refl
readFromSymbol Am  = Refl
readFromSymbol Cm  = Refl
readFromSymbol Bk  = Refl
readFromSymbol Cf  = Refl
readFromSymbol Es  = Refl
readFromSymbol Fm  = Refl
readFromSymbol Md  = Refl
readFromSymbol No  = Refl
readFromSymbol Lr  = Refl
readFromSymbol Rf  = Refl
readFromSymbol Db  = Refl
readFromSymbol Sg  = Refl
readFromSymbol Bh  = Refl
readFromSymbol Hs  = Refl
readFromSymbol Mt  = Refl
readFromSymbol Ds  = Refl
readFromSymbol Rg  = Refl
readFromSymbol Cn  = Refl
readFromSymbol Uut = Refl
readFromSymbol Fl  = Refl
readFromSymbol Uup = Refl
readFromSymbol Lv  = Refl
readFromSymbol Uus = Refl
readFromSymbol Uuo = Refl
