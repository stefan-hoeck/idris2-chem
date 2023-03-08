module Profile.Text.Lex.Element

import Chem
import Profile
import Text.Lex.Element
import Text.Lex.Manual

%default total

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

strings : List String
strings = map symbol elements

charLists : List (List Char)
charLists = map unpack strings

doLex : List Char -> Maybe Elem
doLex cs = case lexElement cs @{Same} of
  Succ e [] => Just e
  _         => Nothing

export
bench : Benchmark Void
bench = Group "Text.Lex.Element" [
    Group "readAll" [
        Single "readElement" (basic (traverse readElement) strings)
      , Single "fromSymbol" (basic (traverse fromSymbol) strings)
      ]

  , Group "read single elements" [
        Single "readElement C" (basic readElement "C")
      , Single "fromSymbol C" (basic fromSymbol "C")
      , Single "readElement O" (basic readElement "O")
      , Single "fromSymbol O" (basic fromSymbol "O")
      , Single "readElement N" (basic readElement "N")
      , Single "fromSymbol N" (basic fromSymbol "N")
      , Single "readElement S" (basic readElement "S")
      , Single "fromSymbol S" (basic fromSymbol "S")
      , Single "readElement U" (basic readElement "U")
      , Single "fromSymbol U" (basic fromSymbol "U")
      ]

  , Group "lexAll" [
        Single "lexElement" (basic (traverse doLex) charLists)
      , Single "fromSymbol . pack" (basic (traverse (fromSymbol . pack)) charLists)
      ]

  , Group "single elements" [
        Single "lexElement C" (basic doLex ['C'])
      , Single "fromSymbol . pack C" (basic (fromSymbol . pack) ['C'])
      , Single "lexElement O" (basic doLex ['O'])
      , Single "fromSymbol . pack O" (basic (fromSymbol . pack) ['O'])
      , Single "lexElement N" (basic doLex ['N'])
      , Single "fromSymbol . pack N" (basic (fromSymbol . pack) ['N'])
      , Single "lexElement S" (basic doLex ['S'])
      , Single "fromSymbol . pack S" (basic (fromSymbol . pack) ['S'])
      , Single "lexElement U" (basic doLex ['U'])
      , Single "fromSymbol . pack U" (basic (fromSymbol . pack) ['U'])
      ]
  ]
