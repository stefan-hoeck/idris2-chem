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
  constructor ED
  mass              : MolecularMass
  exactMass         : MolecularMass
  radiusCovalent    : Double
  radiusVDW         : Maybe Double
  ionization        : Maybe Double
  electronAffinity  : Maybe Double
  electronegativity : Maybe Double
  boilingpoint      : Maybe Double
  meltingpoint      : Maybe Double

||| Array holding additional information about each element.
export
arrElemData : IArray 118 ElemData

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

||| Returns the covalent radius (in Angstrom) of an element.
export %inline
radiusCovalent : Elem -> Double
radiusCovalent = radiusCovalent . elemData

||| Returns the van der Waals radius (in Angstrom) of an element.
export %inline
radiusVDW : Elem -> Maybe Double
radiusVDW = radiusVDW . elemData

||| Returns the ionization energy (in ev) of an element.
export %inline
ionization : Elem -> Maybe Double
ionization = ionization . elemData

||| Returns the electron affinity energy (in ev) of an element.
export %inline
electronAffinity : Elem -> Maybe Double
electronAffinity = electronAffinity . elemData

||| Returns the Pauling electronegativity of an element.
export %inline
electronegativity : Elem -> Maybe Double
electronegativity = electronegativity . elemData

||| Returns the boiling point (in Kelvin) of an element.
export %inline
boilingpoint : Elem -> Maybe Double
boilingpoint = boilingpoint . elemData

||| Returns the melting point (in Kelvin) of an element.
export %inline
meltingpoint : Elem -> Maybe Double
meltingpoint = meltingpoint . elemData

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

-- Do *not* remove the following line!
-- Generated Data

arrElemData =
  array
    [ ED {mass = 1.008, exactMass = 1.007825032, radiusCovalent = 0.32, radiusVDW = Just 1.2, ionization = Just 13.5984, electronAffinity = Just 0.75420375, electronegativity = Just 2.2, boilingpoint = Just 20.28, meltingpoint = Just 14.01}
    , ED {mass = 4.002602, exactMass = 4.002603254, radiusCovalent = 0.46, radiusVDW = Just 1.4, ionization = Just 24.5874, electronAffinity = Just 0.0, electronegativity = Nothing, boilingpoint = Just 4.216, meltingpoint = Just 0.95}
    , ED {mass = 6.94, exactMass = 7.01600455, radiusCovalent = 1.33, radiusVDW = Just 2.2, ionization = Just 5.3917, electronAffinity = Just 0.618049, electronegativity = Just 0.98, boilingpoint = Just 1615.0, meltingpoint = Just 453.7}
    , ED {mass = 9.012182, exactMass = 9.0121822, radiusCovalent = 1.02, radiusVDW = Just 1.9, ionization = Just 9.3227, electronAffinity = Just 0.0, electronegativity = Just 1.57, boilingpoint = Just 3243.0, meltingpoint = Just 1560.0}
    , ED {mass = 10.81, exactMass = 11.0093054, radiusCovalent = 0.85, radiusVDW = Just 1.8, ionization = Just 8.298, electronAffinity = Just 0.279723, electronegativity = Just 2.04, boilingpoint = Just 4275.0, meltingpoint = Just 2365.0}
    , ED {mass = 12.011, exactMass = 12.0, radiusCovalent = 0.75, radiusVDW = Just 1.7, ionization = Just 11.2603, electronAffinity = Just 1.262118, electronegativity = Just 2.55, boilingpoint = Just 5100.0, meltingpoint = Just 3825.0}
    , ED {mass = 14.007, exactMass = 14.003074, radiusCovalent = 0.71, radiusVDW = Just 1.6, ionization = Just 14.5341, electronAffinity = Just (-0.07), electronegativity = Just 3.04, boilingpoint = Just 77.344, meltingpoint = Just 63.15}
    , ED {mass = 15.999, exactMass = 15.99491462, radiusCovalent = 0.63, radiusVDW = Just 1.55, ionization = Just 13.6181, electronAffinity = Just 1.461112, electronegativity = Just 3.44, boilingpoint = Just 90.188, meltingpoint = Just 54.8}
    , ED {mass = 18.9984032, exactMass = 18.99840322, radiusCovalent = 0.64, radiusVDW = Just 1.5, ionization = Just 17.4228, electronAffinity = Just 3.4011887, electronegativity = Just 3.98, boilingpoint = Just 85.0, meltingpoint = Just 53.55}
    , ED {mass = 20.1797, exactMass = 19.99244018, radiusCovalent = 0.67, radiusVDW = Just 1.54, ionization = Just 21.5645, electronAffinity = Just 0.0, electronegativity = Nothing, boilingpoint = Just 27.1, meltingpoint = Just 24.55}
    , ED {mass = 22.98976928, exactMass = 22.98976928, radiusCovalent = 1.55, radiusVDW = Just 2.4, ionization = Just 5.1391, electronAffinity = Just 0.547926, electronegativity = Just 0.93, boilingpoint = Just 1156.0, meltingpoint = Just 371.0}
    , ED {mass = 24.305, exactMass = 23.9850417, radiusCovalent = 1.39, radiusVDW = Just 2.2, ionization = Just 7.6462, electronAffinity = Just 0.0, electronegativity = Just 1.31, boilingpoint = Just 1380.0, meltingpoint = Just 922.0}
    , ED {mass = 26.9815386, exactMass = 26.98153863, radiusCovalent = 1.26, radiusVDW = Just 2.1, ionization = Just 5.9858, electronAffinity = Just 0.43283, electronegativity = Just 1.61, boilingpoint = Just 2740.0, meltingpoint = Just 933.5}
    , ED {mass = 28.085, exactMass = 27.97692653, radiusCovalent = 1.16, radiusVDW = Just 2.1, ionization = Just 8.1517, electronAffinity = Just 1.389521, electronegativity = Just 1.9, boilingpoint = Just 2630.0, meltingpoint = Just 1683.0}
    , ED {mass = 30.973762, exactMass = 30.97376163, radiusCovalent = 1.11, radiusVDW = Just 1.95, ionization = Just 10.4867, electronAffinity = Just 0.7465, electronegativity = Just 2.19, boilingpoint = Just 553.0, meltingpoint = Just 317.3}
    , ED {mass = 32.06, exactMass = 31.972071, radiusCovalent = 1.03, radiusVDW = Just 1.8, ionization = Just 10.36, electronAffinity = Just 2.0771029, electronegativity = Just 2.58, boilingpoint = Just 717.82, meltingpoint = Just 392.2}
    , ED {mass = 35.45, exactMass = 34.96885268, radiusCovalent = 0.99, radiusVDW = Just 1.8, ionization = Just 12.9676, electronAffinity = Just 3.612724, electronegativity = Just 3.16, boilingpoint = Just 239.18, meltingpoint = Just 172.17}
    , ED {mass = 39.948, exactMass = 39.96238312, radiusCovalent = 0.96, radiusVDW = Just 1.88, ionization = Just 15.7596, electronAffinity = Just 0.0, electronegativity = Nothing, boilingpoint = Just 87.45, meltingpoint = Just 83.95}
    , ED {mass = 39.0983, exactMass = 38.96370668, radiusCovalent = 1.96, radiusVDW = Just 2.8, ionization = Just 4.3407, electronAffinity = Just 0.501459, electronegativity = Just 0.82, boilingpoint = Just 1033.0, meltingpoint = Just 336.8}
    , ED {mass = 40.078, exactMass = 39.96259098, radiusCovalent = 1.71, radiusVDW = Just 2.4, ionization = Just 6.1132, electronAffinity = Just 0.02455, electronegativity = Just 1.0, boilingpoint = Just 1757.0, meltingpoint = Just 1112.0}
    , ED {mass = 44.955912, exactMass = 44.9559119, radiusCovalent = 1.48, radiusVDW = Just 2.3, ionization = Just 6.5615, electronAffinity = Just 0.188, electronegativity = Just 1.36, boilingpoint = Just 3109.0, meltingpoint = Just 1814.0}
    , ED {mass = 47.867, exactMass = 47.9479463, radiusCovalent = 1.36, radiusVDW = Just 2.15, ionization = Just 6.8281, electronAffinity = Just 0.084, electronegativity = Just 1.54, boilingpoint = Just 3560.0, meltingpoint = Just 1935.0}
    , ED {mass = 50.9415, exactMass = 50.9439595, radiusCovalent = 1.34, radiusVDW = Just 2.05, ionization = Just 6.7462, electronAffinity = Just 0.525, electronegativity = Just 1.63, boilingpoint = Just 3650.0, meltingpoint = Just 2163.0}
    , ED {mass = 51.9961, exactMass = 51.9405075, radiusCovalent = 1.22, radiusVDW = Just 2.05, ionization = Just 6.7665, electronAffinity = Just 0.67584, electronegativity = Just 1.66, boilingpoint = Just 2945.0, meltingpoint = Just 2130.0}
    , ED {mass = 54.938045, exactMass = 54.9380451, radiusCovalent = 1.19, radiusVDW = Just 2.05, ionization = Just 7.434, electronAffinity = Just 0.0, electronegativity = Just 1.55, boilingpoint = Just 2235.0, meltingpoint = Just 1518.0}
    , ED {mass = 55.845, exactMass = 55.9349375, radiusCovalent = 1.16, radiusVDW = Just 2.05, ionization = Just 7.9024, electronAffinity = Just 0.151, electronegativity = Just 1.83, boilingpoint = Just 3023.0, meltingpoint = Just 1808.0}
    , ED {mass = 58.933195, exactMass = 58.933195, radiusCovalent = 1.11, radiusVDW = Just 2.0, ionization = Just 7.881, electronAffinity = Just 0.6633, electronegativity = Just 1.88, boilingpoint = Just 3143.0, meltingpoint = Just 1768.0}
    , ED {mass = 58.6934, exactMass = 57.9353429, radiusCovalent = 1.1, radiusVDW = Just 2.0, ionization = Just 7.6398, electronAffinity = Just 1.15716, electronegativity = Just 1.91, boilingpoint = Just 3005.0, meltingpoint = Just 1726.0}
    , ED {mass = 63.546, exactMass = 62.9295975, radiusCovalent = 1.12, radiusVDW = Just 2.0, ionization = Just 7.7264, electronAffinity = Just 1.23578, electronegativity = Just 1.9, boilingpoint = Just 2840.0, meltingpoint = Just 1356.6}
    , ED {mass = 65.38, exactMass = 63.9291422, radiusCovalent = 1.18, radiusVDW = Just 2.1, ionization = Just 9.3942, electronAffinity = Just 0.0, electronegativity = Just 1.65, boilingpoint = Just 1180.0, meltingpoint = Just 692.73}
    , ED {mass = 69.723, exactMass = 68.9255736, radiusCovalent = 1.24, radiusVDW = Just 2.1, ionization = Just 5.9993, electronAffinity = Just 0.41, electronegativity = Just 1.81, boilingpoint = Just 2478.0, meltingpoint = Just 302.92}
    , ED {mass = 72.63, exactMass = 73.9211778, radiusCovalent = 1.21, radiusVDW = Just 2.1, ionization = Just 7.8994, electronAffinity = Just 1.232712, electronegativity = Just 2.01, boilingpoint = Just 3107.0, meltingpoint = Just 1211.5}
    , ED {mass = 74.9216, exactMass = 74.9215965, radiusCovalent = 1.21, radiusVDW = Just 2.05, ionization = Just 9.7886, electronAffinity = Just 0.814, electronegativity = Just 2.18, boilingpoint = Just 876.0, meltingpoint = Just 1090.0}
    , ED {mass = 78.96, exactMass = 79.9165213, radiusCovalent = 1.16, radiusVDW = Just 1.9, ionization = Just 9.7524, electronAffinity = Just 2.02067, electronegativity = Just 2.55, boilingpoint = Just 958.0, meltingpoint = Just 494.0}
    , ED {mass = 79.904, exactMass = 78.9183371, radiusCovalent = 1.14, radiusVDW = Just 1.9, ionization = Just 11.8138, electronAffinity = Just 3.363588, electronegativity = Just 2.96, boilingpoint = Just 331.85, meltingpoint = Just 265.95}
    , ED {mass = 83.798, exactMass = 83.911507, radiusCovalent = 1.17, radiusVDW = Just 2.02, ionization = Just 13.9996, electronAffinity = Just 0.0, electronegativity = Just 3.0, boilingpoint = Just 120.85, meltingpoint = Just 116.0}
    , ED {mass = 85.4678, exactMass = 84.91178974, radiusCovalent = 2.1, radiusVDW = Just 2.9, ionization = Just 4.1771, electronAffinity = Just 0.485916, electronegativity = Just 0.82, boilingpoint = Just 961.0, meltingpoint = Just 312.63}
    , ED {mass = 87.62, exactMass = 87.9056121, radiusCovalent = 1.85, radiusVDW = Just 2.55, ionization = Just 5.6949, electronAffinity = Just 0.05206, electronegativity = Just 0.95, boilingpoint = Just 1655.0, meltingpoint = Just 1042.0}
    , ED {mass = 88.90585, exactMass = 88.9058483, radiusCovalent = 1.63, radiusVDW = Just 2.4, ionization = Just 6.2173, electronAffinity = Just 0.307, electronegativity = Just 1.22, boilingpoint = Just 3611.0, meltingpoint = Just 1795.0}
    , ED {mass = 91.224, exactMass = 89.9047044, radiusCovalent = 1.54, radiusVDW = Just 2.3, ionization = Just 6.6339, electronAffinity = Just 0.426, electronegativity = Just 1.33, boilingpoint = Just 4682.0, meltingpoint = Just 2128.0}
    , ED {mass = 92.90638, exactMass = 92.9063781, radiusCovalent = 1.47, radiusVDW = Just 2.15, ionization = Just 6.7589, electronAffinity = Just 0.893, electronegativity = Just 1.6, boilingpoint = Just 5015.0, meltingpoint = Just 2742.0}
    , ED {mass = 95.96, exactMass = 97.9054082, radiusCovalent = 1.38, radiusVDW = Just 2.1, ionization = Just 7.0924, electronAffinity = Just 0.7472, electronegativity = Just 2.16, boilingpoint = Just 4912.0, meltingpoint = Just 2896.0}
    , ED {mass = 97.0, exactMass = 97.907216, radiusCovalent = 1.28, radiusVDW = Just 2.05, ionization = Just 7.28, electronAffinity = Just 0.55, electronegativity = Just 1.9, boilingpoint = Just 4538.0, meltingpoint = Just 2477.0}
    , ED {mass = 101.07, exactMass = 101.9043493, radiusCovalent = 1.25, radiusVDW = Just 2.05, ionization = Just 7.3605, electronAffinity = Just 1.04638, electronegativity = Just 2.2, boilingpoint = Just 4425.0, meltingpoint = Just 2610.0}
    , ED {mass = 102.9055, exactMass = 102.905504, radiusCovalent = 1.25, radiusVDW = Just 2.0, ionization = Just 7.4589, electronAffinity = Just 1.14289, electronegativity = Just 2.28, boilingpoint = Just 3970.0, meltingpoint = Just 2236.0}
    , ED {mass = 106.42, exactMass = 105.903486, radiusCovalent = 1.2, radiusVDW = Just 2.05, ionization = Just 8.3369, electronAffinity = Just 0.56214, electronegativity = Just 2.2, boilingpoint = Just 3240.0, meltingpoint = Just 1825.0}
    , ED {mass = 107.8682, exactMass = 106.905097, radiusCovalent = 1.28, radiusVDW = Just 2.1, ionization = Just 7.5762, electronAffinity = Just 1.30447, electronegativity = Just 1.93, boilingpoint = Just 2436.0, meltingpoint = Just 1235.1}
    , ED {mass = 112.411, exactMass = 113.9033585, radiusCovalent = 1.36, radiusVDW = Just 2.2, ionization = Just 8.9938, electronAffinity = Just 0.0, electronegativity = Just 1.69, boilingpoint = Just 1040.0, meltingpoint = Just 594.26}
    , ED {mass = 114.818, exactMass = 114.903878, radiusCovalent = 1.42, radiusVDW = Just 2.2, ionization = Just 5.7864, electronAffinity = Just 0.404, electronegativity = Just 1.78, boilingpoint = Just 2350.0, meltingpoint = Just 429.78}
    , ED {mass = 118.71, exactMass = 119.9021947, radiusCovalent = 1.4, radiusVDW = Just 2.25, ionization = Just 7.3439, electronAffinity = Just 1.112066, electronegativity = Just 1.96, boilingpoint = Just 2876.0, meltingpoint = Just 505.12}
    , ED {mass = 121.76, exactMass = 120.9038157, radiusCovalent = 1.4, radiusVDW = Just 2.2, ionization = Just 8.6084, electronAffinity = Just 1.047401, electronegativity = Just 2.05, boilingpoint = Just 1860.0, meltingpoint = Just 903.91}
    , ED {mass = 127.6, exactMass = 129.9062244, radiusCovalent = 1.36, radiusVDW = Just 2.1, ionization = Just 9.0096, electronAffinity = Just 1.970875, electronegativity = Just 2.1, boilingpoint = Just 1261.0, meltingpoint = Just 722.72}
    , ED {mass = 126.90447, exactMass = 126.904473, radiusCovalent = 1.33, radiusVDW = Just 2.1, ionization = Just 10.4513, electronAffinity = Just 3.059038, electronegativity = Just 2.66, boilingpoint = Just 457.5, meltingpoint = Just 386.7}
    , ED {mass = 131.293, exactMass = 131.9041535, radiusCovalent = 1.31, radiusVDW = Just 2.16, ionization = Just 12.1298, electronAffinity = Just 0.0, electronegativity = Just 2.6, boilingpoint = Just 165.1, meltingpoint = Just 161.39}
    , ED {mass = 132.9054519, exactMass = 132.9054519, radiusCovalent = 2.32, radiusVDW = Just 3.0, ionization = Just 3.8939, electronAffinity = Just 0.471626, electronegativity = Just 0.79, boilingpoint = Just 944.0, meltingpoint = Just 301.54}
    , ED {mass = 137.327, exactMass = 137.9052472, radiusCovalent = 1.96, radiusVDW = Just 2.7, ionization = Just 5.2117, electronAffinity = Just 0.14462, electronegativity = Just 0.89, boilingpoint = Just 2078.0, meltingpoint = Just 1002.0}
    , ED {mass = 138.90547, exactMass = 138.9063533, radiusCovalent = 1.8, radiusVDW = Just 2.5, ionization = Just 5.5769, electronAffinity = Just 0.47, electronegativity = Just 1.1, boilingpoint = Just 3737.0, meltingpoint = Just 1191.0}
    , ED {mass = 140.116, exactMass = 139.9054387, radiusCovalent = 1.63, radiusVDW = Just 2.48, ionization = Just 5.5387, electronAffinity = Just 0.5, electronegativity = Just 1.12, boilingpoint = Just 3715.0, meltingpoint = Just 1071.0}
    , ED {mass = 140.90765, exactMass = 140.9076528, radiusCovalent = 1.76, radiusVDW = Just 2.47, ionization = Just 5.473, electronAffinity = Just 0.5, electronegativity = Just 1.13, boilingpoint = Just 3785.0, meltingpoint = Just 1204.0}
    , ED {mass = 144.242, exactMass = 141.9077233, radiusCovalent = 1.74, radiusVDW = Just 2.45, ionization = Just 5.525, electronAffinity = Just 0.5, electronegativity = Just 1.14, boilingpoint = Just 3347.0, meltingpoint = Just 1294.0}
    , ED {mass = 145.0, exactMass = 144.912749, radiusCovalent = 1.73, radiusVDW = Just 2.43, ionization = Just 5.582, electronAffinity = Just 0.5, electronegativity = Nothing, boilingpoint = Just 3273.0, meltingpoint = Just 1315.0}
    , ED {mass = 150.36, exactMass = 151.9197324, radiusCovalent = 1.72, radiusVDW = Just 2.42, ionization = Just 5.6437, electronAffinity = Just 0.5, electronegativity = Just 1.17, boilingpoint = Just 2067.0, meltingpoint = Just 1347.0}
    , ED {mass = 151.964, exactMass = 152.9212303, radiusCovalent = 1.68, radiusVDW = Just 2.4, ionization = Just 5.6704, electronAffinity = Just 0.5, electronegativity = Nothing, boilingpoint = Just 1800.0, meltingpoint = Just 1095.0}
    , ED {mass = 157.25, exactMass = 157.9241039, radiusCovalent = 1.69, radiusVDW = Just 2.38, ionization = Just 6.1498, electronAffinity = Just 0.5, electronegativity = Just 1.2, boilingpoint = Just 3545.0, meltingpoint = Just 1585.0}
    , ED {mass = 158.92535, exactMass = 158.9253468, radiusCovalent = 1.68, radiusVDW = Just 2.37, ionization = Just 5.8638, electronAffinity = Just 0.5, electronegativity = Nothing, boilingpoint = Just 3500.0, meltingpoint = Just 1629.0}
    , ED {mass = 162.5, exactMass = 163.9291748, radiusCovalent = 1.67, radiusVDW = Just 2.35, ionization = Just 5.9389, electronAffinity = Just 0.5, electronegativity = Just 1.22, boilingpoint = Just 2840.0, meltingpoint = Just 1685.0}
    , ED {mass = 164.93032, exactMass = 164.9303221, radiusCovalent = 1.66, radiusVDW = Just 2.33, ionization = Just 6.0215, electronAffinity = Just 0.5, electronegativity = Just 1.23, boilingpoint = Just 2968.0, meltingpoint = Just 1747.0}
    , ED {mass = 167.259, exactMass = 165.9302931, radiusCovalent = 1.65, radiusVDW = Just 2.32, ionization = Just 6.1077, electronAffinity = Just 0.5, electronegativity = Just 1.24, boilingpoint = Just 3140.0, meltingpoint = Just 1802.0}
    , ED {mass = 168.93421, exactMass = 168.9342133, radiusCovalent = 1.64, radiusVDW = Just 2.3, ionization = Just 6.1843, electronAffinity = Just 0.5, electronegativity = Just 1.25, boilingpoint = Just 2223.0, meltingpoint = Just 1818.0}
    , ED {mass = 173.054, exactMass = 173.9388621, radiusCovalent = 1.7, radiusVDW = Just 2.28, ionization = Just 6.2542, electronAffinity = Just 0.5, electronegativity = Nothing, boilingpoint = Just 1469.0, meltingpoint = Just 1092.0}
    , ED {mass = 174.9668, exactMass = 174.9407718, radiusCovalent = 1.62, radiusVDW = Just 2.27, ionization = Just 5.4259, electronAffinity = Just 0.5, electronegativity = Just 1.27, boilingpoint = Just 3668.0, meltingpoint = Just 1936.0}
    , ED {mass = 178.49, exactMass = 179.94655, radiusCovalent = 1.52, radiusVDW = Just 2.25, ionization = Just 6.8251, electronAffinity = Just 0.0, electronegativity = Just 1.3, boilingpoint = Just 4875.0, meltingpoint = Just 2504.0}
    , ED {mass = 180.94788, exactMass = 180.9479958, radiusCovalent = 1.46, radiusVDW = Just 2.2, ionization = Just 7.5496, electronAffinity = Just 0.322, electronegativity = Just 1.5, boilingpoint = Just 5730.0, meltingpoint = Just 3293.0}
    , ED {mass = 183.84, exactMass = 183.9509312, radiusCovalent = 1.37, radiusVDW = Just 2.1, ionization = Just 7.864, electronAffinity = Just 0.815, electronegativity = Just 2.36, boilingpoint = Just 5825.0, meltingpoint = Just 3695.0}
    , ED {mass = 186.207, exactMass = 186.9557531, radiusCovalent = 1.31, radiusVDW = Just 2.05, ionization = Just 7.8335, electronAffinity = Just 0.15, electronegativity = Just 1.9, boilingpoint = Just 5870.0, meltingpoint = Just 3455.0}
    , ED {mass = 190.23, exactMass = 191.9614807, radiusCovalent = 1.29, radiusVDW = Just 2.0, ionization = Just 8.4382, electronAffinity = Just 1.0778, electronegativity = Just 2.2, boilingpoint = Just 5300.0, meltingpoint = Just 3300.0}
    , ED {mass = 192.217, exactMass = 192.9629264, radiusCovalent = 1.22, radiusVDW = Just 2.0, ionization = Just 8.967, electronAffinity = Just 1.56436, electronegativity = Just 2.2, boilingpoint = Just 4700.0, meltingpoint = Just 2720.0}
    , ED {mass = 195.084, exactMass = 194.9647911, radiusCovalent = 1.23, radiusVDW = Just 2.05, ionization = Just 8.9588, electronAffinity = Just 2.1251, electronegativity = Just 2.28, boilingpoint = Just 4100.0, meltingpoint = Just 2042.1}
    , ED {mass = 196.966569, exactMass = 196.9665687, radiusCovalent = 1.24, radiusVDW = Just 2.1, ionization = Just 9.2255, electronAffinity = Just 2.30861, electronegativity = Just 2.54, boilingpoint = Just 3130.0, meltingpoint = Just 1337.58}
    , ED {mass = 200.592, exactMass = 201.970643, radiusCovalent = 1.33, radiusVDW = Just 2.05, ionization = Just 10.4375, electronAffinity = Just 0.0, electronegativity = Just 2.0, boilingpoint = Just 629.88, meltingpoint = Just 234.31}
    , ED {mass = 204.38, exactMass = 204.9744275, radiusCovalent = 1.44, radiusVDW = Just 2.2, ionization = Just 6.1082, electronAffinity = Just 0.377, electronegativity = Just 1.62, boilingpoint = Just 1746.0, meltingpoint = Just 577.0}
    , ED {mass = 207.2, exactMass = 207.9766521, radiusCovalent = 1.44, radiusVDW = Just 2.3, ionization = Just 7.4167, electronAffinity = Just 0.364, electronegativity = Just 2.33, boilingpoint = Just 2023.0, meltingpoint = Just 600.65}
    , ED {mass = 208.9804, exactMass = 208.9803987, radiusCovalent = 1.51, radiusVDW = Just 2.3, ionization = Just 7.2855, electronAffinity = Just 0.942363, electronegativity = Just 2.02, boilingpoint = Just 1837.0, meltingpoint = Just 544.59}
    , ED {mass = 209.0, exactMass = 208.9824304, radiusCovalent = 1.45, radiusVDW = Just 2.0, ionization = Just 8.414, electronAffinity = Just 1.9, electronegativity = Just 2.0, boilingpoint = Nothing, meltingpoint = Just 527.0}
    , ED {mass = 210.0, exactMass = 209.987148, radiusCovalent = 1.47, radiusVDW = Just 2.0, ionization = Just 0.0, electronAffinity = Just 2.8, electronegativity = Just 2.2, boilingpoint = Just 610.0, meltingpoint = Just 575.0}
    , ED {mass = 222.0, exactMass = 222.0175777, radiusCovalent = 1.42, radiusVDW = Just 2.0, ionization = Just 10.7485, electronAffinity = Just 0.0, electronegativity = Nothing, boilingpoint = Just 211.4, meltingpoint = Just 202.0}
    , ED {mass = 223.0, exactMass = 223.0197359, radiusCovalent = 2.23, radiusVDW = Just 2.0, ionization = Just 4.0727, electronAffinity = Nothing, electronegativity = Just 0.7, boilingpoint = Just 950.0, meltingpoint = Just 300.0}
    , ED {mass = 226.0, exactMass = 226.0254098, radiusCovalent = 2.01, radiusVDW = Just 2.0, ionization = Just 5.2784, electronAffinity = Nothing, electronegativity = Just 0.9, boilingpoint = Just 1413.0, meltingpoint = Just 973.0}
    , ED {mass = 227.0, exactMass = 227.0277521, radiusCovalent = 1.86, radiusVDW = Just 2.0, ionization = Just 5.17, electronAffinity = Nothing, electronegativity = Just 1.1, boilingpoint = Just 3470.0, meltingpoint = Just 1324.0}
    , ED {mass = 232.03806, exactMass = 232.0380553, radiusCovalent = 1.75, radiusVDW = Just 2.4, ionization = Just 6.3067, electronAffinity = Nothing, electronegativity = Just 1.3, boilingpoint = Just 5060.0, meltingpoint = Just 2028.0}
    , ED {mass = 231.03588, exactMass = 231.035884, radiusCovalent = 1.69, radiusVDW = Just 2.0, ionization = Just 5.89, electronAffinity = Nothing, electronegativity = Just 1.5, boilingpoint = Just 4300.0, meltingpoint = Just 1845.0}
    , ED {mass = 238.02891, exactMass = 238.0507882, radiusCovalent = 1.7, radiusVDW = Just 2.3, ionization = Just 6.1941, electronAffinity = Nothing, electronegativity = Just 1.38, boilingpoint = Just 4407.0, meltingpoint = Just 1408.0}
    , ED {mass = 237.0, exactMass = 237.0481734, radiusCovalent = 1.71, radiusVDW = Just 2.0, ionization = Just 6.2657, electronAffinity = Nothing, electronegativity = Just 1.36, boilingpoint = Just 4175.0, meltingpoint = Just 912.0}
    , ED {mass = 244.0, exactMass = 244.064204, radiusCovalent = 1.72, radiusVDW = Just 2.0, ionization = Just 6.026, electronAffinity = Nothing, electronegativity = Just 1.28, boilingpoint = Just 3505.0, meltingpoint = Just 913.0}
    , ED {mass = 243.0, exactMass = 243.0613811, radiusCovalent = 1.66, radiusVDW = Just 2.0, ionization = Just 5.9738, electronAffinity = Nothing, electronegativity = Just 1.3, boilingpoint = Just 2880.0, meltingpoint = Just 1449.0}
    , ED {mass = 247.0, exactMass = 247.070354, radiusCovalent = 1.66, radiusVDW = Just 2.0, ionization = Just 5.9914, electronAffinity = Nothing, electronegativity = Just 1.3, boilingpoint = Just 3383.0, meltingpoint = Just 1620.0}
    , ED {mass = 247.0, exactMass = 247.070307, radiusCovalent = 1.68, radiusVDW = Just 2.0, ionization = Just 6.1979, electronAffinity = Nothing, electronegativity = Just 1.3, boilingpoint = Just 983.0, meltingpoint = Just 1258.0}
    , ED {mass = 251.0, exactMass = 251.079587, radiusCovalent = 1.68, radiusVDW = Just 2.0, ionization = Just 6.2817, electronAffinity = Nothing, electronegativity = Just 1.3, boilingpoint = Just 1173.0, meltingpoint = Just 1172.0}
    , ED {mass = 252.0, exactMass = 252.08298, radiusCovalent = 1.65, radiusVDW = Just 2.0, ionization = Just 6.42, electronAffinity = Nothing, electronegativity = Just 1.3, boilingpoint = Nothing, meltingpoint = Just 1130.0}
    , ED {mass = 257.0, exactMass = 257.095105, radiusCovalent = 1.67, radiusVDW = Just 2.0, ionization = Just 6.5, electronAffinity = Nothing, electronegativity = Just 1.3, boilingpoint = Nothing, meltingpoint = Just 1800.0}
    , ED {mass = 258.0, exactMass = 258.098431, radiusCovalent = 1.73, radiusVDW = Just 2.0, ionization = Just 6.58, electronAffinity = Nothing, electronegativity = Just 1.3, boilingpoint = Nothing, meltingpoint = Just 1100.0}
    , ED {mass = 259.0, exactMass = 259.10103, radiusCovalent = 1.76, radiusVDW = Just 2.0, ionization = Just 6.65, electronAffinity = Nothing, electronegativity = Just 1.3, boilingpoint = Nothing, meltingpoint = Just 1100.0}
    , ED {mass = 262.0, exactMass = 262.10963, radiusCovalent = 1.61, radiusVDW = Just 2.0, ionization = Just 4.9, electronAffinity = Nothing, electronegativity = Nothing, boilingpoint = Nothing, meltingpoint = Just 1900.0}
    , ED {mass = 267.0, exactMass = 261.10877, radiusCovalent = 1.57, radiusVDW = Just 2.0, ionization = Just 6.0, electronAffinity = Nothing, electronegativity = Nothing, boilingpoint = Nothing, meltingpoint = Nothing}
    , ED {mass = 270.0, exactMass = 262.11408, radiusCovalent = 1.49, radiusVDW = Just 2.0, ionization = Nothing, electronAffinity = Nothing, electronegativity = Nothing, boilingpoint = Nothing, meltingpoint = Nothing}
    , ED {mass = 271.0, exactMass = 263.11832, radiusCovalent = 1.43, radiusVDW = Just 2.0, ionization = Nothing, electronAffinity = Nothing, electronegativity = Nothing, boilingpoint = Nothing, meltingpoint = Nothing}
    , ED {mass = 270.0, exactMass = 264.1246, radiusCovalent = 1.41, radiusVDW = Just 2.0, ionization = Nothing, electronAffinity = Nothing, electronegativity = Nothing, boilingpoint = Nothing, meltingpoint = Nothing}
    , ED {mass = 277.0, exactMass = 265.13009, radiusCovalent = 1.34, radiusVDW = Just 2.0, ionization = Nothing, electronAffinity = Nothing, electronegativity = Nothing, boilingpoint = Nothing, meltingpoint = Nothing}
    , ED {mass = 276.0, exactMass = 268.13873, radiusCovalent = 1.29, radiusVDW = Just 2.0, ionization = Nothing, electronAffinity = Nothing, electronegativity = Nothing, boilingpoint = Nothing, meltingpoint = Nothing}
    , ED {mass = 281.0, exactMass = 271.14606, radiusCovalent = 1.28, radiusVDW = Nothing, ionization = Nothing, electronAffinity = Nothing, electronegativity = Nothing, boilingpoint = Nothing, meltingpoint = Nothing}
    , ED {mass = 282.0, exactMass = 272.15362, radiusCovalent = 1.21, radiusVDW = Nothing, ionization = Nothing, electronAffinity = Nothing, electronegativity = Nothing, boilingpoint = Nothing, meltingpoint = Nothing}
    , ED {mass = 285.0, exactMass = 285.17411, radiusCovalent = 1.22, radiusVDW = Nothing, ionization = Nothing, electronAffinity = Nothing, electronegativity = Nothing, boilingpoint = Nothing, meltingpoint = Nothing}
    , ED {mass = 285.0, exactMass = 284.17808, radiusCovalent = 1.36, radiusVDW = Nothing, ionization = Nothing, electronAffinity = Nothing, electronegativity = Nothing, boilingpoint = Nothing, meltingpoint = Nothing}
    , ED {mass = 289.0, exactMass = 289.18728, radiusCovalent = 1.43, radiusVDW = Nothing, ionization = Nothing, electronAffinity = Nothing, electronegativity = Nothing, boilingpoint = Nothing, meltingpoint = Nothing}
    , ED {mass = 289.0, exactMass = 288.19249, radiusCovalent = 1.62, radiusVDW = Nothing, ionization = Nothing, electronAffinity = Nothing, electronegativity = Nothing, boilingpoint = Nothing, meltingpoint = Nothing}
    , ED {mass = 293.0, exactMass = 292.19979, radiusCovalent = 1.75, radiusVDW = Nothing, ionization = Nothing, electronAffinity = Nothing, electronegativity = Nothing, boilingpoint = Nothing, meltingpoint = Nothing}
    , ED {mass = 294.0, exactMass = 294.0, radiusCovalent = 1.65, radiusVDW = Nothing, ionization = Nothing, electronAffinity = Nothing, electronegativity = Nothing, boilingpoint = Nothing, meltingpoint = Nothing}
    , ED {mass = 294.0, exactMass = 294.0, radiusCovalent = 1.57, radiusVDW = Nothing, ionization = Nothing, electronAffinity = Nothing, electronegativity = Nothing, boilingpoint = Nothing, meltingpoint = Nothing}
    ]
