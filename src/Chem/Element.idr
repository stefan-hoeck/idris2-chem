module Chem.Element

import public Chem.Types
import Derive.Finite
import Derive.Prelude
import Derive.Refined

%language ElabReflection
%default total

--------------------------------------------------------------------------------
--          The Elements
--------------------------------------------------------------------------------

||| The chemical elements encoded as an enum type
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

%runElab derive "Elem" [Show, Eq, Ord, Finite]

export %inline
Interpolation Elem where
  interpolate = show

--------------------------------------------------------------------------------
--          Conversion from and to AtomicNr
--------------------------------------------------------------------------------

||| This is a proof that we can safely compute an atomic number
||| from each element's index
export
0 indexLemma : (e : Elem) -> IsAtomicNr (conIndexElem e + 1)

||| Compute the atomic number of an element
public export %inline
atomicNr : Elem -> AtomicNr
atomicNr e = MkAtomicNr (conIndexElem e + 1) @{indexLemma e}

||| Compute the element from an atomic number
public export
fromAtomicNr : AtomicNr -> Elem

||| Return the chemical symbol of an element.
public export %inline
symbol : Elem -> String
symbol = show

--------------------------------------------------------------------------------
--          Aromaticity
--------------------------------------------------------------------------------

||| Proof that only valid elements are marked as aromatic
public export
data ValidAromatic : Elem -> Bool -> Type where
  VAB    : ValidAromatic B  True
  VAC    : ValidAromatic C  True
  VAN    : ValidAromatic N  True
  VAO    : ValidAromatic O  True
  VAP    : ValidAromatic P  True
  VAS    : ValidAromatic S  True
  VASe   : ValidAromatic Se True
  VAAs   : ValidAromatic As True
  VARest : ValidAromatic e False

||| An element paired with a boolean flag indicating whether the atom
||| in question is part of an aromatic system.
public export
record AromElem where
  constructor MkAE
  elem : Elem
  arom : Bool
  {auto 0 prf : ValidAromatic elem arom}

%runElab derive "AromElem" [Show,Eq]

export
Interpolation AromElem where
  interpolate (MkAE e b) = if b then toLower (show e) else show e

export %inline
Cast AromElem Elem where cast = elem

--------------------------------------------------------------------------------
--          Isotope
--------------------------------------------------------------------------------

||| An element paired with an optional mass number.
|||
||| If the mass number is `Nothing`, a value of this type represents
||| a natural mixture of isotopes.
public export
record Isotope where
  constructor MkI
  elem : Elem
  mass : Maybe MassNr

%runElab derive "Isotope" [Show,Eq]

export %inline
Cast Isotope Elem where cast = elem

||| An element paired with an optional mass number plus a
||| boolean flag representing aromaticity.
|||
||| If the mass number is `Nothing`, a value of this type represents
||| a natural mixture of isotopes.
public export
record AromIsotope where
  constructor MkAI
  elem : Elem
  mass : Maybe MassNr
  arom : Bool
  {auto 0 prf : ValidAromatic elem arom}

%runElab derive "AromIsotope" [Show,Eq]

export %inline
Cast AromIsotope Elem where cast = elem

export %inline
Cast AromIsotope AromElem where cast (MkAI e m a) = MkAE e a

--------------------------------------------------------------------------------
--          Implementations
--------------------------------------------------------------------------------

-- the following lengthy and not very interesting implementations
-- are kept at the end of the file to get a better overview over the
-- exported functions and types

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
