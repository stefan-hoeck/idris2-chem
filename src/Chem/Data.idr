module Chem.Data

import Data.Array
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

||| Additional data about the elements
public export
record IsotopeData where
  constructor ID
  massNr           : MassNr
  exactMass        : MolecularMass
  naturalAbundance : Abundance

export
arrIsotopeData : IArray 118 (List IsotopeData)

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

arrIsotopeData =
  array
    [ [ ID {massNr = 2, exactMass = 2.014101778, naturalAbundance = 1.15e-4}
      , ID {massNr = 1, exactMass = 1.007825032, naturalAbundance = 0.999885}
      ]

    , [ ID {massNr = 4, exactMass = 4.002603254, naturalAbundance = 0.99999863}
      , ID {massNr = 3, exactMass = 3.016029319, naturalAbundance = 1.37e-6}
      ]

    , [ ID {massNr = 7, exactMass = 7.01600455, naturalAbundance = 0.9241}
      , ID {massNr = 6, exactMass = 6.015122795, naturalAbundance = 0.0759}
      ]

    , [ ID {massNr = 9, exactMass = 9.0121822, naturalAbundance = 1.0} ]
    , [ ID {massNr = 11, exactMass = 11.0093054, naturalAbundance = 0.801}
      , ID {massNr = 10, exactMass = 10.012937, naturalAbundance = 0.199}
      ]

    , [ ID {massNr = 13, exactMass = 13.00335484, naturalAbundance = 0.0107}
      , ID {massNr = 12, exactMass = 12.0, naturalAbundance = 0.9893}
      ]

    , [ ID {massNr = 15, exactMass = 15.0001089, naturalAbundance = 0.00368}
      , ID {massNr = 14, exactMass = 14.003074, naturalAbundance = 0.99632}
      ]

    , [ ID {massNr = 18, exactMass = 17.999161, naturalAbundance = 0.00205}
      , ID {massNr = 17, exactMass = 16.9991317, naturalAbundance = 3.8e-4}
      , ID {massNr = 16, exactMass = 15.99491462, naturalAbundance = 0.99757}
      ]

    , [ ID {massNr = 19, exactMass = 18.99840322, naturalAbundance = 1.0} ]
    , [ ID {massNr = 22, exactMass = 21.99138511, naturalAbundance = 0.0925}
      , ID {massNr = 21, exactMass = 20.99384668, naturalAbundance = 0.0027}
      , ID {massNr = 20, exactMass = 19.99244018, naturalAbundance = 0.9048}
      ]

    , [ ID {massNr = 23, exactMass = 22.98976928, naturalAbundance = 1.0} ]
    , [ ID {massNr = 26, exactMass = 25.98259293, naturalAbundance = 0.1101}
      , ID {massNr = 25, exactMass = 24.98583692, naturalAbundance = 0.1}
      , ID {massNr = 24, exactMass = 23.9850417, naturalAbundance = 0.7899}
      ]

    , [ ID {massNr = 27, exactMass = 26.98153863, naturalAbundance = 1.0} ]
    , [ ID {massNr = 30, exactMass = 29.97377017, naturalAbundance = 0.030872}
      , ID {massNr = 29, exactMass = 28.9764947, naturalAbundance = 0.046832}
      , ID {massNr = 28, exactMass = 27.97692653, naturalAbundance = 0.922297}
      ]

    , [ ID {massNr = 31, exactMass = 30.97376163, naturalAbundance = 1.0} ]
    , [ ID {massNr = 36, exactMass = 35.96708076, naturalAbundance = 2.0e-4}
      , ID {massNr = 34, exactMass = 33.9678669, naturalAbundance = 0.0429}
      , ID {massNr = 33, exactMass = 32.97145876, naturalAbundance = 0.0076}
      , ID {massNr = 32, exactMass = 31.972071, naturalAbundance = 0.9493}
      ]

    , [ ID {massNr = 37, exactMass = 36.96590259, naturalAbundance = 0.2422}
      , ID {massNr = 35, exactMass = 34.96885268, naturalAbundance = 0.7578}
      ]

    , [ ID {massNr = 40, exactMass = 39.96238312, naturalAbundance = 0.996003}
      , ID {massNr = 38, exactMass = 37.9627324, naturalAbundance = 6.32e-4}
      , ID {massNr = 36, exactMass = 35.96754511, naturalAbundance = 0.003365}
      ]

    , [ ID {massNr = 41, exactMass = 40.96182576, naturalAbundance = 0.067302}
      , ID {massNr = 40, exactMass = 39.96399848, naturalAbundance = 1.17e-4}
      , ID {massNr = 39, exactMass = 38.96370668, naturalAbundance = 0.932581}
      ]

    , [ ID {massNr = 48, exactMass = 47.952534, naturalAbundance = 0.00187}
      , ID {massNr = 46, exactMass = 45.9536926, naturalAbundance = 4.0e-5}
      , ID {massNr = 44, exactMass = 43.9554818, naturalAbundance = 0.02086}
      , ID {massNr = 43, exactMass = 42.9587666, naturalAbundance = 0.00135}
      , ID {massNr = 42, exactMass = 41.95861801, naturalAbundance = 0.00647}
      , ID {massNr = 40, exactMass = 39.96259098, naturalAbundance = 0.96941}
      ]

    , [ ID {massNr = 45, exactMass = 44.9559119, naturalAbundance = 1.0} ]
    , [ ID {massNr = 50, exactMass = 49.9447912, naturalAbundance = 0.0518}
      , ID {massNr = 49, exactMass = 48.94787, naturalAbundance = 0.0541}
      , ID {massNr = 48, exactMass = 47.9479463, naturalAbundance = 0.7372}
      , ID {massNr = 47, exactMass = 46.9517631, naturalAbundance = 0.0744}
      , ID {massNr = 46, exactMass = 45.9526316, naturalAbundance = 0.0825}
      ]

    , [ ID {massNr = 51, exactMass = 50.9439595, naturalAbundance = 0.9975}
      , ID {massNr = 50, exactMass = 49.9471585, naturalAbundance = 0.0025}
      ]

    , [ ID {massNr = 54, exactMass = 53.9388804, naturalAbundance = 0.02365}
      , ID {massNr = 53, exactMass = 52.9406494, naturalAbundance = 0.09501}
      , ID {massNr = 52, exactMass = 51.9405075, naturalAbundance = 0.83789}
      , ID {massNr = 50, exactMass = 49.9460442, naturalAbundance = 0.04345}
      ]

    , [ ID {massNr = 55, exactMass = 54.9380451, naturalAbundance = 1.0} ]
    , [ ID {massNr = 58, exactMass = 57.9332756, naturalAbundance = 0.00282}
      , ID {massNr = 57, exactMass = 56.935394, naturalAbundance = 0.02119}
      , ID {massNr = 56, exactMass = 55.9349375, naturalAbundance = 0.91754}
      , ID {massNr = 54, exactMass = 53.9396105, naturalAbundance = 0.05845}
      ]

    , [ ID {massNr = 59, exactMass = 58.933195, naturalAbundance = 1.0} ]
    , [ ID {massNr = 64, exactMass = 63.927966, naturalAbundance = 0.009256}
      , ID {massNr = 62, exactMass = 61.9283451, naturalAbundance = 0.036345}
      , ID {massNr = 61, exactMass = 60.931056, naturalAbundance = 0.011399}
      , ID {massNr = 60, exactMass = 59.9307864, naturalAbundance = 0.262231}
      , ID {massNr = 58, exactMass = 57.9353429, naturalAbundance = 0.680769}
      ]

    , [ ID {massNr = 65, exactMass = 64.9277895, naturalAbundance = 0.3083}
      , ID {massNr = 63, exactMass = 62.9295975, naturalAbundance = 0.6917}
      ]

    , [ ID {massNr = 70, exactMass = 69.9253193, naturalAbundance = 0.0062}
      , ID {massNr = 68, exactMass = 67.9248442, naturalAbundance = 0.1875}
      , ID {massNr = 67, exactMass = 66.9271273, naturalAbundance = 0.041}
      , ID {massNr = 66, exactMass = 65.9260334, naturalAbundance = 0.279}
      , ID {massNr = 64, exactMass = 63.9291422, naturalAbundance = 0.4863}
      ]

    , [ ID {massNr = 71, exactMass = 70.9247013, naturalAbundance = 0.39892}
      , ID {massNr = 69, exactMass = 68.9255736, naturalAbundance = 0.60108}
      ]

    , [ ID {massNr = 76, exactMass = 75.9214026, naturalAbundance = 0.0761}
      , ID {massNr = 74, exactMass = 73.9211778, naturalAbundance = 0.3628}
      , ID {massNr = 73, exactMass = 72.9234589, naturalAbundance = 0.0773}
      , ID {massNr = 72, exactMass = 71.9220758, naturalAbundance = 0.2754}
      , ID {massNr = 70, exactMass = 69.9242474, naturalAbundance = 0.2084}
      ]

    , [ ID {massNr = 75, exactMass = 74.9215965, naturalAbundance = 1.0} ]
    , [ ID {massNr = 82, exactMass = 81.9166994, naturalAbundance = 0.0873}
      , ID {massNr = 80, exactMass = 79.9165213, naturalAbundance = 0.4961}
      , ID {massNr = 78, exactMass = 77.9173091, naturalAbundance = 0.2377}
      , ID {massNr = 77, exactMass = 76.919914, naturalAbundance = 0.0763}
      , ID {massNr = 76, exactMass = 75.9192136, naturalAbundance = 0.0937}
      , ID {massNr = 74, exactMass = 73.9224764, naturalAbundance = 0.0089}
      ]

    , [ ID {massNr = 81, exactMass = 80.9162906, naturalAbundance = 0.4931}
      , ID {massNr = 79, exactMass = 78.9183371, naturalAbundance = 0.5069}
      ]

    , [ ID {massNr = 86, exactMass = 85.91061073, naturalAbundance = 0.173}
      , ID {massNr = 84, exactMass = 83.911507, naturalAbundance = 0.57}
      , ID {massNr = 83, exactMass = 82.914136, naturalAbundance = 0.1149}
      , ID {massNr = 82, exactMass = 81.9134836, naturalAbundance = 0.1158}
      , ID {massNr = 80, exactMass = 79.916379, naturalAbundance = 0.0228}
      , ID {massNr = 78, exactMass = 77.9203648, naturalAbundance = 0.0035}
      ]

    , [ ID {massNr = 87, exactMass = 86.90918053, naturalAbundance = 0.2783}
      , ID {massNr = 85, exactMass = 84.91178974, naturalAbundance = 0.7217}
      ]

    , [ ID {massNr = 88, exactMass = 87.9056121, naturalAbundance = 0.8258}
      , ID {massNr = 87, exactMass = 86.9088771, naturalAbundance = 0.07}
      , ID {massNr = 86, exactMass = 85.9092602, naturalAbundance = 0.0986}
      , ID {massNr = 84, exactMass = 83.913425, naturalAbundance = 0.0056}
      ]

    , [ ID {massNr = 89, exactMass = 88.9058483, naturalAbundance = 1.0} ]
    , [ ID {massNr = 96, exactMass = 95.9082734, naturalAbundance = 0.028}
      , ID {massNr = 94, exactMass = 93.9063152, naturalAbundance = 0.1738}
      , ID {massNr = 92, exactMass = 91.9050408, naturalAbundance = 0.1715}
      , ID {massNr = 91, exactMass = 90.9056458, naturalAbundance = 0.1122}
      , ID {massNr = 90, exactMass = 89.9047044, naturalAbundance = 0.5145}
      ]

    , [ ID {massNr = 93, exactMass = 92.9063781, naturalAbundance = 1.0} ]
    , [ ID {massNr = 100, exactMass = 99.907477, naturalAbundance = 0.0963}
      , ID {massNr = 98, exactMass = 97.9054082, naturalAbundance = 0.2413}
      , ID {massNr = 97, exactMass = 96.9060215, naturalAbundance = 0.0955}
      , ID {massNr = 96, exactMass = 95.9046795, naturalAbundance = 0.1668}
      , ID {massNr = 95, exactMass = 94.9058421, naturalAbundance = 0.1592}
      , ID {massNr = 94, exactMass = 93.9050883, naturalAbundance = 0.0925}
      , ID {massNr = 92, exactMass = 91.906811, naturalAbundance = 0.1484}
      ]

    , []
    , [ ID {massNr = 104, exactMass = 103.905433, naturalAbundance = 0.1862}
      , ID {massNr = 102, exactMass = 101.9043493, naturalAbundance = 0.3155}
      , ID {massNr = 101, exactMass = 100.9055821, naturalAbundance = 0.1706}
      , ID {massNr = 100, exactMass = 99.9042195, naturalAbundance = 0.126}
      , ID {massNr = 99, exactMass = 98.9059393, naturalAbundance = 0.1276}
      , ID {massNr = 98, exactMass = 97.905287, naturalAbundance = 0.0187}
      , ID {massNr = 96, exactMass = 95.907598, naturalAbundance = 0.0554}
      ]

    , [ ID {massNr = 103, exactMass = 102.905504, naturalAbundance = 1.0} ]
    , [ ID {massNr = 110, exactMass = 109.905153, naturalAbundance = 0.1172}
      , ID {massNr = 108, exactMass = 107.903892, naturalAbundance = 0.2646}
      , ID {massNr = 106, exactMass = 105.903486, naturalAbundance = 0.2733}
      , ID {massNr = 105, exactMass = 104.905085, naturalAbundance = 0.2233}
      , ID {massNr = 104, exactMass = 103.904036, naturalAbundance = 0.1114}
      , ID {massNr = 102, exactMass = 101.905609, naturalAbundance = 0.0102}
      ]

    , [ ID {massNr = 109, exactMass = 108.904752, naturalAbundance = 0.48161}
      , ID {massNr = 107, exactMass = 106.905097, naturalAbundance = 0.51839}
      ]

    , [ ID {massNr = 116, exactMass = 115.904756, naturalAbundance = 0.0749}
      , ID {massNr = 114, exactMass = 113.9033585, naturalAbundance = 0.2873}
      , ID {massNr = 113, exactMass = 112.9044017, naturalAbundance = 0.1222}
      , ID {massNr = 112, exactMass = 111.9027578, naturalAbundance = 0.2413}
      , ID {massNr = 111, exactMass = 110.9041781, naturalAbundance = 0.128}
      , ID {massNr = 110, exactMass = 109.9030021, naturalAbundance = 0.1249}
      , ID {massNr = 108, exactMass = 107.904184, naturalAbundance = 0.0089}
      , ID {massNr = 106, exactMass = 105.906459, naturalAbundance = 0.0125}
      ]

    , [ ID {massNr = 115, exactMass = 114.903878, naturalAbundance = 0.9571}
      , ID {massNr = 113, exactMass = 112.904058, naturalAbundance = 0.0429}
      ]

    , [ ID {massNr = 124, exactMass = 123.9052739, naturalAbundance = 0.0579}
      , ID {massNr = 122, exactMass = 121.903439, naturalAbundance = 0.0463}
      , ID {massNr = 120, exactMass = 119.9021947, naturalAbundance = 0.3258}
      , ID {massNr = 119, exactMass = 118.903308, naturalAbundance = 0.0859}
      , ID {massNr = 118, exactMass = 117.901603, naturalAbundance = 0.2422}
      , ID {massNr = 117, exactMass = 116.902952, naturalAbundance = 0.0768}
      , ID {massNr = 116, exactMass = 115.901741, naturalAbundance = 0.1454}
      , ID {massNr = 115, exactMass = 114.903342, naturalAbundance = 0.0034}
      , ID {massNr = 114, exactMass = 113.902779, naturalAbundance = 0.0066}
      , ID {massNr = 112, exactMass = 111.904818, naturalAbundance = 0.0097}
      ]

    , [ ID {massNr = 123, exactMass = 122.904214, naturalAbundance = 0.4279}
      , ID {massNr = 121, exactMass = 120.9038157, naturalAbundance = 0.5721}
      ]

    , [ ID {massNr = 130, exactMass = 129.9062244, naturalAbundance = 0.3408}
      , ID {massNr = 128, exactMass = 127.9044631, naturalAbundance = 0.3174}
      , ID {massNr = 126, exactMass = 125.9033117, naturalAbundance = 0.1884}
      , ID {massNr = 125, exactMass = 124.9044307, naturalAbundance = 0.0707}
      , ID {massNr = 124, exactMass = 123.9028179, naturalAbundance = 0.0474}
      , ID {massNr = 123, exactMass = 122.90427, naturalAbundance = 0.0089}
      , ID {massNr = 122, exactMass = 121.9030439, naturalAbundance = 0.0255}
      , ID {massNr = 120, exactMass = 119.90402, naturalAbundance = 9.0e-4}
      ]

    , [ ID {massNr = 127, exactMass = 126.904473, naturalAbundance = 1.0} ]
    , [ ID {massNr = 136, exactMass = 135.907219, naturalAbundance = 0.0887}
      , ID {massNr = 134, exactMass = 133.9053945, naturalAbundance = 0.1044}
      , ID {massNr = 132, exactMass = 131.9041535, naturalAbundance = 0.2689}
      , ID {massNr = 131, exactMass = 130.9050824, naturalAbundance = 0.2118}
      , ID {massNr = 130, exactMass = 129.903508, naturalAbundance = 0.0408}
      , ID {massNr = 129, exactMass = 128.9047794, naturalAbundance = 0.2644}
      , ID {massNr = 128, exactMass = 127.9035313, naturalAbundance = 0.0192}
      , ID {massNr = 126, exactMass = 125.904274, naturalAbundance = 9.0e-4}
      , ID {massNr = 124, exactMass = 123.905893, naturalAbundance = 9.0e-4}
      ]

    , [ ID {massNr = 133, exactMass = 132.9054519, naturalAbundance = 1.0} ]
    , [ ID {massNr = 138, exactMass = 137.9052472, naturalAbundance = 0.71698}
      , ID {massNr = 137, exactMass = 136.9058274, naturalAbundance = 0.11232}
      , ID {massNr = 136, exactMass = 135.9045759, naturalAbundance = 0.07854}
      , ID {massNr = 135, exactMass = 134.9056886, naturalAbundance = 0.06592}
      , ID {massNr = 134, exactMass = 133.9045084, naturalAbundance = 0.02417}
      , ID {massNr = 132, exactMass = 131.9050613, naturalAbundance = 0.00101}
      , ID {massNr = 130, exactMass = 129.9063208, naturalAbundance = 0.00106}
      ]

    , [ ID {massNr = 139, exactMass = 138.9063533, naturalAbundance = 0.9991}
      , ID {massNr = 138, exactMass = 137.907112, naturalAbundance = 9.0e-4}
      ]

    , [ ID {massNr = 142, exactMass = 141.909244, naturalAbundance = 0.11114}
      , ID {massNr = 140, exactMass = 139.9054387, naturalAbundance = 0.8845}
      , ID {massNr = 138, exactMass = 137.905991, naturalAbundance = 0.00251}
      , ID {massNr = 136, exactMass = 135.907172, naturalAbundance = 0.00185}
      ]

    , [ ID {massNr = 141, exactMass = 140.9076528, naturalAbundance = 1.0} ]
    , [ ID {massNr = 150, exactMass = 149.920891, naturalAbundance = 0.056}
      , ID {massNr = 148, exactMass = 147.916893, naturalAbundance = 0.057}
      , ID {massNr = 146, exactMass = 145.9131169, naturalAbundance = 0.172}
      , ID {massNr = 145, exactMass = 144.9125736, naturalAbundance = 0.083}
      , ID {massNr = 144, exactMass = 143.9100873, naturalAbundance = 0.238}
      , ID {massNr = 143, exactMass = 142.9098143, naturalAbundance = 0.122}
      , ID {massNr = 142, exactMass = 141.9077233, naturalAbundance = 0.272}
      ]

    , []
    , [ ID {massNr = 154, exactMass = 153.9222093, naturalAbundance = 0.2275}
      , ID {massNr = 152, exactMass = 151.9197324, naturalAbundance = 0.2675}
      , ID {massNr = 150, exactMass = 149.9172755, naturalAbundance = 0.0738}
      , ID {massNr = 149, exactMass = 148.9171847, naturalAbundance = 0.1382}
      , ID {massNr = 148, exactMass = 147.9148227, naturalAbundance = 0.1124}
      , ID {massNr = 147, exactMass = 146.9148979, naturalAbundance = 0.1499}
      , ID {massNr = 144, exactMass = 143.911999, naturalAbundance = 0.0307}
      ]

    , [ ID {massNr = 153, exactMass = 152.9212303, naturalAbundance = 0.5219}
      , ID {massNr = 151, exactMass = 150.9198502, naturalAbundance = 0.4781}
      ]

    , [ ID {massNr = 160, exactMass = 159.9270541, naturalAbundance = 0.2186}
      , ID {massNr = 158, exactMass = 157.9241039, naturalAbundance = 0.2484}
      , ID {massNr = 157, exactMass = 156.9239601, naturalAbundance = 0.1565}
      , ID {massNr = 156, exactMass = 155.9221227, naturalAbundance = 0.2047}
      , ID {massNr = 155, exactMass = 154.922622, naturalAbundance = 0.148}
      , ID {massNr = 154, exactMass = 153.9208656, naturalAbundance = 0.0218}
      , ID {massNr = 152, exactMass = 151.919791, naturalAbundance = 0.002}
      ]

    , [ ID {massNr = 159, exactMass = 158.9253468, naturalAbundance = 1.0} ]
    , [ ID {massNr = 164, exactMass = 163.9291748, naturalAbundance = 0.2818}
      , ID {massNr = 163, exactMass = 162.9287312, naturalAbundance = 0.249}
      , ID {massNr = 162, exactMass = 161.9267984, naturalAbundance = 0.2551}
      , ID {massNr = 161, exactMass = 160.9269334, naturalAbundance = 0.1891}
      , ID {massNr = 160, exactMass = 159.9251975, naturalAbundance = 0.0234}
      , ID {massNr = 158, exactMass = 157.924409, naturalAbundance = 0.001}
      , ID {massNr = 156, exactMass = 155.924283, naturalAbundance = 6.0e-4}
      ]

    , [ ID {massNr = 165, exactMass = 164.9303221, naturalAbundance = 1.0} ]
    , [ ID {massNr = 170, exactMass = 169.9354643, naturalAbundance = 0.1493}
      , ID {massNr = 168, exactMass = 167.9323702, naturalAbundance = 0.2678}
      , ID {massNr = 167, exactMass = 166.9320482, naturalAbundance = 0.2293}
      , ID {massNr = 166, exactMass = 165.9302931, naturalAbundance = 0.3361}
      , ID {massNr = 164, exactMass = 163.9292, naturalAbundance = 0.0161}
      , ID {massNr = 162, exactMass = 161.928778, naturalAbundance = 0.0014}
      ]

    , [ ID {massNr = 169, exactMass = 168.9342133, naturalAbundance = 1.0} ]
    , [ ID {massNr = 176, exactMass = 175.9425717, naturalAbundance = 0.1276}
      , ID {massNr = 174, exactMass = 173.9388621, naturalAbundance = 0.3183}
      , ID {massNr = 173, exactMass = 172.9382108, naturalAbundance = 0.1613}
      , ID {massNr = 172, exactMass = 171.9363815, naturalAbundance = 0.2183}
      , ID {massNr = 171, exactMass = 170.9363258, naturalAbundance = 0.1428}
      , ID {massNr = 170, exactMass = 169.9347618, naturalAbundance = 0.0304}
      , ID {massNr = 168, exactMass = 167.933897, naturalAbundance = 0.0013}
      ]

    , [ ID {massNr = 176, exactMass = 175.9426863, naturalAbundance = 0.0259}
      , ID {massNr = 175, exactMass = 174.9407718, naturalAbundance = 0.9741}
      ]

    , [ ID {massNr = 180, exactMass = 179.94655, naturalAbundance = 0.3508}
      , ID {massNr = 179, exactMass = 178.9458161, naturalAbundance = 0.1362}
      , ID {massNr = 178, exactMass = 177.9436988, naturalAbundance = 0.2728}
      , ID {massNr = 177, exactMass = 176.9432207, naturalAbundance = 0.186}
      , ID {massNr = 176, exactMass = 175.9414086, naturalAbundance = 0.0526}
      , ID {massNr = 174, exactMass = 173.940046, naturalAbundance = 0.0016}
      ]

    , [ ID {massNr = 181, exactMass = 180.9479958, naturalAbundance = 0.99988}
      , ID {massNr = 180, exactMass = 179.9474648, naturalAbundance = 1.2e-4}
      ]

    , [ ID {massNr = 186, exactMass = 185.9543641, naturalAbundance = 0.2843}
      , ID {massNr = 184, exactMass = 183.9509312, naturalAbundance = 0.3064}
      , ID {massNr = 183, exactMass = 182.950223, naturalAbundance = 0.1431}
      , ID {massNr = 182, exactMass = 181.9482042, naturalAbundance = 0.265}
      , ID {massNr = 180, exactMass = 179.946704, naturalAbundance = 0.0012}
      ]

    , [ ID {massNr = 187, exactMass = 186.9557531, naturalAbundance = 0.626}
      , ID {massNr = 185, exactMass = 184.952955, naturalAbundance = 0.374}
      ]

    , [ ID {massNr = 192, exactMass = 191.9614807, naturalAbundance = 0.4078}
      , ID {massNr = 190, exactMass = 189.958447, naturalAbundance = 0.2626}
      , ID {massNr = 189, exactMass = 188.9581475, naturalAbundance = 0.1615}
      , ID {massNr = 188, exactMass = 187.9558382, naturalAbundance = 0.1324}
      , ID {massNr = 187, exactMass = 186.9557505, naturalAbundance = 0.0196}
      , ID {massNr = 186, exactMass = 185.9538382, naturalAbundance = 0.0159}
      , ID {massNr = 184, exactMass = 183.9524891, naturalAbundance = 2.0e-4}
      ]

    , [ ID {massNr = 193, exactMass = 192.9629264, naturalAbundance = 0.627}
      , ID {massNr = 191, exactMass = 190.960594, naturalAbundance = 0.373}
      ]

    , [ ID {massNr = 198, exactMass = 197.967893, naturalAbundance = 0.07163}
      , ID {massNr = 196, exactMass = 195.9649515, naturalAbundance = 0.25242}
      , ID {massNr = 195, exactMass = 194.9647911, naturalAbundance = 0.33832}
      , ID {massNr = 194, exactMass = 193.9626803, naturalAbundance = 0.32967}
      , ID {massNr = 192, exactMass = 191.961038, naturalAbundance = 0.00782}
      , ID {massNr = 190, exactMass = 189.959932, naturalAbundance = 1.4e-4}
      ]

    , [ ID {massNr = 197, exactMass = 196.9665687, naturalAbundance = 1.0} ]
    , [ ID {massNr = 204, exactMass = 203.9734939, naturalAbundance = 0.0687}
      , ID {massNr = 202, exactMass = 201.970643, naturalAbundance = 0.2986}
      , ID {massNr = 201, exactMass = 200.9703023, naturalAbundance = 0.1318}
      , ID {massNr = 200, exactMass = 199.968326, naturalAbundance = 0.231}
      , ID {massNr = 199, exactMass = 198.9682799, naturalAbundance = 0.1687}
      , ID {massNr = 198, exactMass = 197.966769, naturalAbundance = 0.0997}
      , ID {massNr = 196, exactMass = 195.965833, naturalAbundance = 0.0015}
      ]

    , [ ID {massNr = 205, exactMass = 204.9744275, naturalAbundance = 0.70476}
      , ID {massNr = 203, exactMass = 202.9723442, naturalAbundance = 0.29524}
      ]

    , [ ID {massNr = 208, exactMass = 207.9766521, naturalAbundance = 0.524}
      , ID {massNr = 207, exactMass = 206.9758969, naturalAbundance = 0.221}
      , ID {massNr = 206, exactMass = 205.9744653, naturalAbundance = 0.241}
      , ID {massNr = 204, exactMass = 203.9730436, naturalAbundance = 0.014}
      ]

    , [ ID {massNr = 209, exactMass = 208.9803987, naturalAbundance = 1.0} ]
    , []
    , []
    , []
    , []
    , []
    , []
    , [ ID {massNr = 232, exactMass = 232.0380553, naturalAbundance = 1.0} ]
    , [ ID {massNr = 231, exactMass = 231.035884, naturalAbundance = 1.0} ]
    , [ ID {massNr = 238, exactMass = 238.0507882, naturalAbundance = 0.992745}
      , ID {massNr = 235, exactMass = 235.0439299, naturalAbundance = 0.0072}
      , ID {massNr = 234, exactMass = 234.0409521, naturalAbundance = 5.5e-5}
      ]

    , []
    , []
    , []
    , []
    , []
    , []
    , []
    , []
    , []
    , []
    , []
    , []
    , []
    , []
    , []
    , []
    , []
    , []
    , []
    , []
    , []
    , []
    , []
    , []
    , []
    , []
    ]
