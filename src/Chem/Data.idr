module Chem.Data

import Data.Array.Indexed
import Data.Vect
import Chem.Elem
import Chem.Types

%default total

--------------------------------------------------------------------------------
--          Element Data
--------------------------------------------------------------------------------

||| Additional data about the elements
public export
record ElemData where
  constructor EI
  mass      : MolecularMass
  exactMass : MolecularMass

||| Array holding additional information about each element.
export
arrElemData : IArray 118 ElemData
arrElemData =
  array
    [ EI 1.008 1.007825032
    , EI 4.002602 4.002603254
    , EI 6.94 7.01600455
    , EI 9.012182 9.0121822
    , EI 10.81 11.0093054
    , EI 12.011 12
    , EI 14.007 14.003074
    , EI 15.999 15.99491462
    , EI 18.9984032 18.99840322
    , EI 20.1797 19.99244018
    , EI 22.98976928 22.98976928
    , EI 24.305 23.9850417
    , EI 26.9815386 26.98153863
    , EI 28.085 27.97692653
    , EI 30.973762 30.97376163
    , EI 32.06 31.972071
    , EI 35.45 34.96885268
    , EI 39.948 39.96238312
    , EI 39.0983 38.96370668
    , EI 40.078 39.96259098
    , EI 44.955912 44.9559119
    , EI 47.867 47.9479463
    , EI 50.9415 50.9439595
    , EI 51.9961 51.9405075
    , EI 54.938045 54.9380451
    , EI 55.845 55.9349375
    , EI 58.933195 58.933195
    , EI 58.6934 57.9353429
    , EI 63.546 62.9295975
    , EI 65.38 63.9291422
    , EI 69.723 68.9255736
    , EI 72.630 73.9211778
    , EI 74.92160 74.9215965
    , EI 78.96 79.9165213
    , EI 79.904 78.9183371
    , EI 83.798 83.911507
    , EI 85.4678 84.91178974
    , EI 87.62 87.9056121
    , EI 88.90585 88.9058483
    , EI 91.224 89.9047044
    , EI 92.90638 92.9063781
    , EI 95.96 97.9054082
    , EI 97 97.907216
    , EI 101.07 101.9043493
    , EI 102.90550 102.905504
    , EI 106.42 105.903486
    , EI 107.8682 106.905097
    , EI 112.411 113.9033585
    , EI 114.818 114.903878
    , EI 118.710 119.9021947
    , EI 121.760 120.9038157
    , EI 127.60 129.9062244
    , EI 126.90447 126.904473
    , EI 131.293 131.9041535
    , EI 132.9054519 132.9054519
    , EI 137.327 137.9052472
    , EI 138.90547 138.9063533
    , EI 140.116 139.9054387
    , EI 140.90765 140.9076528
    , EI 144.242 141.9077233
    , EI 145 144.912749
    , EI 150.36 151.9197324
    , EI 151.964 152.9212303
    , EI 157.25 157.9241039
    , EI 158.92535 158.9253468
    , EI 162.500 163.9291748
    , EI 164.93032 164.9303221
    , EI 167.259 165.9302931
    , EI 168.93421 168.9342133
    , EI 173.054 173.9388621
    , EI 174.9668 174.9407718
    , EI 178.49 179.94655
    , EI 180.94788 180.9479958
    , EI 183.84 183.9509312
    , EI 186.207 186.9557531
    , EI 190.23 191.9614807
    , EI 192.217 192.9629264
    , EI 195.084 194.9647911
    , EI 196.966569 196.9665687
    , EI 200.592 201.970643
    , EI 204.38 204.9744275
    , EI 207.2 207.9766521
    , EI 208.98040 208.9803987
    , EI 209 208.9824304
    , EI 210 209.987148
    , EI 222 222.0175777
    , EI 223 223.0197359
    , EI 226 226.0254098
    , EI 227 227.0277521
    , EI 232.03806 232.0380553
    , EI 231.03588 231.035884
    , EI 238.02891 238.0507882
    , EI 237 237.0481734
    , EI 244 244.064204
    , EI 243 243.0613811
    , EI 247 247.070354
    , EI 247 247.070307
    , EI 251 251.079587
    , EI 252 252.08298
    , EI 257 257.095105
    , EI 258 258.098431
    , EI 259 259.10103
    , EI 262 262.10963
    , EI 267 261.10877
    , EI 270 262.11408
    , EI 271 263.11832
    , EI 270 264.1246
    , EI 277 265.13009
    , EI 276 268.13873
    , EI 281 271.14606
    , EI 282 272.15362
    , EI 285 285.17411
    , EI 285 284.17808
    , EI 289 289.18728
    , EI 289 288.19249
    , EI 293 292.19979
    , EI 294 294
    , EI 294 294
    ]

||| Proof that the con index of an element is less than the natural number 118.
|||
||| This allows us to use elements (actually, their constructor index, which is
||| the same at runtime) to safely index into the info arrays in this module.
export
0 conIndexLemma : (e : Elem) -> (cast (conIndexElem e) < the Nat 118) === True

||| Get additional information about an element.
export %inline
elemData : Elem -> ElemData
elemData e =
  atNat
    arrElemData
    (cast $ conIndexElem e)
    @{ltOpReflectsLT _ _ $ conIndexLemma e}

||| Extract the molecular mass of an element (averaged over the isotopes in
||| the natural mix).
export %inline
mass : Elem -> MolecularMass
mass = mass . elemData

||| Extract the exact molecular mass of an element's main isotope.
export %inline
exactMass : Elem -> MolecularMass
exactMass = exactMass . elemData

--------------------------------------------------------------------------------
--          Isotope Data
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
--          Proofs
--------------------------------------------------------------------------------

conIndexLemma H  = Refl
conIndexLemma He = Refl
conIndexLemma Li = Refl
conIndexLemma Be = Refl
conIndexLemma B  = Refl
conIndexLemma C  = Refl
conIndexLemma N  = Refl
conIndexLemma O  = Refl
conIndexLemma F  = Refl
conIndexLemma Ne = Refl
conIndexLemma Na = Refl
conIndexLemma Mg = Refl
conIndexLemma Al = Refl
conIndexLemma Si = Refl
conIndexLemma P  = Refl
conIndexLemma S  = Refl
conIndexLemma Cl = Refl
conIndexLemma Ar = Refl
conIndexLemma K  = Refl
conIndexLemma Ca = Refl
conIndexLemma Sc = Refl
conIndexLemma Ti = Refl
conIndexLemma V  = Refl
conIndexLemma Cr = Refl
conIndexLemma Mn = Refl
conIndexLemma Fe = Refl
conIndexLemma Co = Refl
conIndexLemma Ni = Refl
conIndexLemma Cu = Refl
conIndexLemma Zn = Refl
conIndexLemma Ga = Refl
conIndexLemma Ge = Refl
conIndexLemma As = Refl
conIndexLemma Se = Refl
conIndexLemma Br = Refl
conIndexLemma Kr = Refl
conIndexLemma Rb = Refl
conIndexLemma Sr = Refl
conIndexLemma Y  = Refl
conIndexLemma Zr = Refl
conIndexLemma Nb = Refl
conIndexLemma Mo = Refl
conIndexLemma Tc = Refl
conIndexLemma Ru = Refl
conIndexLemma Rh = Refl
conIndexLemma Pd = Refl
conIndexLemma Ag = Refl
conIndexLemma Cd = Refl
conIndexLemma In = Refl
conIndexLemma Sn = Refl
conIndexLemma Sb = Refl
conIndexLemma Te = Refl
conIndexLemma I  = Refl
conIndexLemma Xe = Refl
conIndexLemma Cs = Refl
conIndexLemma Ba = Refl
conIndexLemma La = Refl
conIndexLemma Ce = Refl
conIndexLemma Pr = Refl
conIndexLemma Nd = Refl
conIndexLemma Pm = Refl
conIndexLemma Sm = Refl
conIndexLemma Eu = Refl
conIndexLemma Gd = Refl
conIndexLemma Tb = Refl
conIndexLemma Dy = Refl
conIndexLemma Ho = Refl
conIndexLemma Er = Refl
conIndexLemma Tm = Refl
conIndexLemma Yb = Refl
conIndexLemma Lu = Refl
conIndexLemma Hf = Refl
conIndexLemma Ta = Refl
conIndexLemma W  = Refl
conIndexLemma Re = Refl
conIndexLemma Os = Refl
conIndexLemma Ir = Refl
conIndexLemma Pt = Refl
conIndexLemma Au = Refl
conIndexLemma Hg = Refl
conIndexLemma Tl = Refl
conIndexLemma Pb = Refl
conIndexLemma Bi = Refl
conIndexLemma Po = Refl
conIndexLemma At = Refl
conIndexLemma Rn = Refl
conIndexLemma Fr = Refl
conIndexLemma Ra = Refl
conIndexLemma Ac = Refl
conIndexLemma Th = Refl
conIndexLemma Pa = Refl
conIndexLemma U  = Refl
conIndexLemma Np = Refl
conIndexLemma Pu = Refl
conIndexLemma Am = Refl
conIndexLemma Cm = Refl
conIndexLemma Bk = Refl
conIndexLemma Cf = Refl
conIndexLemma Es = Refl
conIndexLemma Fm = Refl
conIndexLemma Md = Refl
conIndexLemma No = Refl
conIndexLemma Lr = Refl
conIndexLemma Rf = Refl
conIndexLemma Db = Refl
conIndexLemma Sg = Refl
conIndexLemma Bh = Refl
conIndexLemma Hs = Refl
conIndexLemma Mt = Refl
conIndexLemma Ds = Refl
conIndexLemma Rg = Refl
conIndexLemma Cn = Refl
conIndexLemma Nh = Refl
conIndexLemma Fl = Refl
conIndexLemma Mc = Refl
conIndexLemma Lv = Refl
conIndexLemma Ts = Refl
conIndexLemma Og = Refl
