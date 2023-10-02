module Chem.AtomType

import Chem.Atom
import Chem.Elem
import Chem.Types
import Data.Maybe
import Data.SortedMap
import Derive.Prelude

%language ElabReflection
%default total

--------------------------------------------------------------------------------
--          Types
--------------------------------------------------------------------------------

||| CDK atom types
public export
record AtomType where
  constructor AT
  name          : String
  lonePairCount : Nat
  hybridization : Hybridization
  single        : Nat
  double        : Nat
  triple        : Nat

%runElab derive "AtomType" [Show,Eq]

||| Counts of bond types connected to an atom
public export
record Bonds where
  constructor BS
  single : Nat
  double : Nat
  triple : Nat

%runElab derive "Bonds" [Show,Eq,Ord]

||| Add single bonds from implicit hydrogens to the list of bonds
||| connected to an atom
export %inline
addH : HCount -> Bonds -> Bonds
addH h = {single $= (+ cast h.value)}

||| Placeholder for unknown atom types
|||
||| We use this instead of returning an error type such
||| as a `Maybe` or an `Either` because it facilitates
||| writing algorithms with a certain tolerance for invalid
||| molecules
export
unknown : AtomType
unknown = AT "unknown" 0 None 0 0 0

export
hasPiBonds : Bonds -> Bool
hasPiBonds (BS _ d t) = d > 0 || t > 0

export
Semigroup Bonds where
  BS s1 d1 t1 <+> BS s2 d2 t2 = BS (s1 + s2) (d1 + d2) (t1 + t2)

export
Monoid Bonds where
  neutral = BS 0 0 0

||| Perceiving atom types
|||
||| This is to be used if no implicit hydrogen atoms are given.
||| Implicit hydrogen count can then be determined from the atom type.
export
atomType : Elem -> Radical -> Charge -> Bonds -> AtomType

||| General purpose atom type perception
|||
||| This is to be used if no implicit hydrogen atoms are given
||| and these should be perceived from the atom type as well.
export %inline
atomTypeAndHydrogens : Elem -> Radical -> Charge -> Bonds -> (HCount, AtomType)
atomTypeAndHydrogens e r c bs =
  let at := atomType e r c bs
      h  := fromMaybe 0 $ refineHCount (cast at.single - cast bs.single)
   in (h,at)

||| Utility for those cases where the number of implict hydrogens
||| (if any) is already included in the number of bonds.
|||
||| This returns `unknown` if the number of single bonds do not
||| match exactly.
export
exactAtomType : Elem -> Radical -> Charge -> Bonds -> AtomType

--------------------------------------------------------------------------------
--          Implementation
--------------------------------------------------------------------------------

hash : Elem -> Charge -> Radical -> (single,double,triple : Nat) -> Bits32
hash e c r s d t =
  let he := cast (conIndexElem e)      * 100
      hc := (he + cast (c.value + 15)) * 10000
      ht := hc + cast (s * 1000 + d * 100 + t * 10) + cast (conIndexRadical r)
   in ht

-- convert information about an atom type to a hash for fast lookup
-- in a dictionary, plus the atom type itself
pair :
     (name      : String)
  -> (elem      : Elem)
  -> (charge    : Charge)
  -> (radical   : Radical)
  -> (bonds     : Bonds)
  -> (hybr      : Hybridization)
  -> (lonePairs : Nat)
  -> (Bits32,AtomType)
pair n e c r (BS s d t) h l = (hash e c r s d t, AT n l h s d t)

-- sorted map from hash to atom type
-- TODO: C.minus.planar
--       N.minus.planar
--       N.nitro
--       N.amide
--       N.thioamide
--       N.planar3
--       O.minus.co2
--       O.sp2.co2
--       O.planar3
--       S.planar3
--       S.only
--       S.thionyl
atMap : SortedMap Bits32 AtomType
atMap =
  SortedMap.fromList
    [ pair "Ag.neutral"             Ag 0    NoRadical (BS 0 0 0) None        0
    , pair "Ag.1"                   Ag 0    NoRadical (BS 1 0 0) None        0
    , pair "Ag.plus"                Ag 1    NoRadical (BS 0 0 0) None        0
    , pair "Al.3minus"              Al (-3) NoRadical (BS 6 0 0) None        0
    , pair "Al"                     Al 0    NoRadical (BS 3 0 0) SP3         0
    , pair "Al.3plus"               Al 3    NoRadical (BS 0 0 0) S           0
    , pair "Ar"                     Ar 0    NoRadical (BS 0 0 0) SP3         4
    , pair "As.minus"               As (-1) NoRadical (BS 6 0 0) None        0
    , pair "As.2"                   As 0    NoRadical (BS 1 1 0) SP2         1
    , pair "As"                     As 0    NoRadical (BS 3 0 0) SP3         1
    , pair "As.5"                   As 0    NoRadical (BS 3 1 0) SP3         0
    , pair "As.plus"                As 1    NoRadical (BS 4 0 0) SP3         0
    , pair "As.3plus"               As 3    NoRadical (BS 0 0 0) None        0
    , pair "Au.1"                   Au 0    NoRadical (BS 1 0 0) None        0
    , pair "B.minus"                B  (-1) NoRadical (BS 4 0 0) SP3         0
    , pair "B"                      B  0    NoRadical (BS 3 0 0) SP3         0
    , pair "B.3plus"                B  3    NoRadical (BS 4 0 0) SP3         0
    , pair "Ba.2plus"               Ba 2    NoRadical (BS 0 0 0) None        0
    , pair "Be.2minus"              Be (-2) NoRadical (BS 4 0 0) SP3         0
    , pair "Be.neutral"             Be 0    NoRadical (BS 0 0 0) None        0
    , pair "Br.minus"               Br (-1) NoRadical (BS 0 0 0) SP3         4
    , pair "Br"                     Br 0    NoRadical (BS 1 0 0) SP3         3
    , pair "Br.3"                   Br 0    NoRadical (BS 1 2 0) SP3         1
    , pair "Br.radical"             Br 0    Singlet   (BS 0 0 0) SP3         3
    , pair "Br.plus.sp2"            Br 1    NoRadical (BS 0 1 0) SP2         2
    , pair "Br.plus.sp3"            Br 1    NoRadical (BS 2 0 0) SP3         2
    , pair "Br.plus.radical"        Br 1    Singlet   (BS 1 0 0) SP3         2
    , pair "C.minus.sp1"            C  (-1) NoRadical (BS 0 0 1) SP          1
    , pair "C.minus.sp2"            C  (-1) NoRadical (BS 1 1 0) SP2         1
    , pair "C.minus.sp3"            C  (-1) NoRadical (BS 3 0 0) SP3         1
    , pair "C.radical.sp1"          C  0    Singlet   (BS 0 0 1) SP          0
    , pair "C.radical.sp2"          C  0    Singlet   (BS 1 1 0) SP2         0
    , pair "C.radical.planar"       C  0    Singlet   (BS 3 0 0) Planar      0
    , pair "C.plus.sp1"             C  1    NoRadical (BS 0 0 1) SP          0
    , pair "C.plus.sp2"             C  1    NoRadical (BS 1 1 0) SP2         0
    , pair "C.plus.planar"          C  1    NoRadical (BS 3 0 0) Planar      0
    , pair "Ca.1"                   Ca 0    NoRadical (BS 0 1 0) None        0
    , pair "Ca.2"                   Ca 0    NoRadical (BS 2 0 0) None        0
    , pair "Ca.2plus"               Ca 2    NoRadical (BS 0 0 0) S           0
    , pair "Cd.metallic"            Cd 0    NoRadical (BS 0 0 0) None        0
    , pair "Cd.2"                   Cd 0    NoRadical (BS 2 0 0) SP          0
    , pair "Cd.2plus"               Cd 2    NoRadical (BS 0 0 0) None        0
    , pair "Cl.minus"               Cl (-1) NoRadical (BS 0 0 0) SP3         4
    , pair "Cl"                     Cl 0    NoRadical (BS 1 0 0) SP3         3
    , pair "Cl.2"                   Cl 0    NoRadical (BS 1 1 0) SP3         2
    , pair "Cl.chlorate"            Cl 0    NoRadical (BS 1 2 0) SP2         0
    , pair "Cl.perchlorate"         Cl 0    NoRadical (BS 1 3 0) SP3         0
    , pair "Cl.radical"             Cl 0    Singlet   (BS 0 0 0) SP3         3
    , pair "Cl.plus.sp2"            Cl 1    NoRadical (BS 0 1 0) SP2         2
    , pair "Cl.plus.sp3"            Cl 1    NoRadical (BS 2 0 0) SP3         2
    , pair "Cl.plus.radical"        Cl 1    Singlet   (BS 1 0 0) SP3         2
    , pair "Cl.perchlorate.charged" Cl 3    NoRadical (BS 4 0 0) SP3         0
    , pair "Co.metallic"            Co 0    NoRadical (BS 0 0 0) None        0
    , pair "Co.1"                   Co 0    NoRadical (BS 1 0 0) None        0
    , pair "Co.2"                   Co 0    NoRadical (BS 2 0 0) None        0
    , pair "Co.4"                   Co 0    NoRadical (BS 4 0 0) None        0
    , pair "Co.6"                   Co 0    NoRadical (BS 6 0 0) None        0
    , pair "Co.plus"                Co 1    NoRadical (BS 0 0 0) None        0
    , pair "Co.plus.1"              Co 1    NoRadical (BS 1 0 0) None        0
    , pair "Co.plus.2"              Co 1    NoRadical (BS 2 0 0) None        0
    , pair "Co.plus.4"              Co 1    NoRadical (BS 4 0 0) None        0
    , pair "Co.plus.5"              Co 1    NoRadical (BS 5 0 0) None        0
    , pair "Co.plus.6"              Co 1    NoRadical (BS 6 0 0) None        0
    , pair "Co.2plus"               Co 2    NoRadical (BS 0 0 0) None        0
    , pair "Co.3plus"               Co 3    NoRadical (BS 0 0 0) None        0
    , pair "Cr.neutral"             Cr 0    NoRadical (BS 0 0 0) None        0
    , pair "Cr.4"                   Cr 0    NoRadical (BS 2 2 0) SP3         0
    , pair "Cr"                     Cr 0    NoRadical (BS 6 0 0) Octahedral  0
    , pair "Cr.3plus"               Cr 3    NoRadical (BS 0 0 0) None        0
    , pair "Cr.6plus"               Cr 6    NoRadical (BS 0 0 0) None        0
    , pair "Cu.metallic"            Cu 0    NoRadical (BS 0 0 0) None        0
    , pair "Cu.1"                   Cu 0    NoRadical (BS 1 0 0) None        0
    , pair "Cu.plus"                Cu 1    NoRadical (BS 0 0 0) None        0
    , pair "Cu.2plus"               Cu 2    NoRadical (BS 0 0 0) None        0
    , pair "F.minus"                F  (-1) NoRadical (BS 0 0 0) SP3         4
    , pair "F"                      F  0    NoRadical (BS 1 0 0) SP3         3
    , pair "F.radical"              F  0    Singlet   (BS 0 0 0) SP3         3
    , pair "F.plus.sp2"             F  1    NoRadical (BS 0 1 0) SP2         2
    , pair "F.plus.sp3"             F  1    NoRadical (BS 2 0 0) SP3         2
    , pair "F.plus.radical"         F  1    Singlet   (BS 1 0 0) SP3         2
    , pair "Fe.4minus"              Fe (-4) NoRadical (BS 6 0 0) None        0
    , pair "Fe.3minus"              Fe (-3) NoRadical (BS 6 0 0) None        0
    , pair "Fe.2minus"              Fe (-2) NoRadical (BS 6 0 0) None        0
    , pair "Fe.metallic"            Fe 0    NoRadical (BS 0 0 0) None        0
    , pair "Fe.2"                   Fe 0    NoRadical (BS 2 0 0) None        0
    , pair "Fe.3"                   Fe 0    NoRadical (BS 3 0 0) None        0
    , pair "Fe.4"                   Fe 0    NoRadical (BS 4 0 0) None        0
    , pair "Fe.5"                   Fe 0    NoRadical (BS 5 0 0) None        0
    , pair "Fe.6"                   Fe 0    NoRadical (BS 6 0 0) None        0
    , pair "Fe.plus"                Fe 1    NoRadical (BS 2 0 0) None        0
    , pair "Fe.2plus"               Fe 2    NoRadical (BS 0 0 0) None        0
    , pair "Fe.3plus"               Fe 3    NoRadical (BS 0 0 0) None        0
    , pair "Ga"                     Ga 0    NoRadical (BS 3 0 0) Octahedral  0
    , pair "Ga.3plus"               Ga 3    NoRadical (BS 0 0 0) Octahedral  0
    , pair "Gd.3plus"               Gd 3    NoRadical (BS 0 0 0) None        0
    , pair "Ge.3"                   Ge 0    NoRadical (BS 2 1 0) SP2         0
    , pair "Ge"                     Ge 0    NoRadical (BS 4 0 0) SP3         0
    , pair "H.minus"                H  (-1) NoRadical (BS 0 0 0) S           0
    , pair "H"                      H  0    NoRadical (BS 1 0 0) S           0
    , pair "H.radical"              H  0    Singlet   (BS 0 0 0) S           0
    , pair "H.plus"                 H  1    NoRadical (BS 0 0 0) S           0
    , pair "He"                     He 0    NoRadical (BS 0 0 0) S           1
    , pair "Hg.minus"               Hg (-1) NoRadical (BS 2 0 0) None        0
    , pair "Hg.metallic"            Hg 0    NoRadical (BS 0 0 0) None        0
    , pair "Hg.1"                   Hg 0    NoRadical (BS 0 1 0) None        0
    , pair "Hg.2"                   Hg 0    NoRadical (BS 2 0 0) None        0
    , pair "Hg.plus"                Hg 1    NoRadical (BS 1 0 0) None        0
    , pair "Hg.2plus"               Hg 2    NoRadical (BS 0 0 0) None        0
    , pair "I.minus"                I  (-1) NoRadical (BS 0 0 0) SP3         4
    , pair "I.minus.5"              I  (-1) NoRadical (BS 2 0 0) SP3D1       3
    , pair "I"                      I  0    NoRadical (BS 1 0 0) SP3         3
    , pair "I.3"                    I  0    NoRadical (BS 1 1 0) SP2         1
    , pair "I.5"                    I  0    NoRadical (BS 1 2 0) SP2         0
    , pair "I.sp3d2.3"              I  0    NoRadical (BS 3 0 0) SP3D2       2
    , pair "I.radical"              I  0    Singlet   (BS 0 0 0) SP3         3
    , pair "I.plus.sp2"             I  1    NoRadical (BS 0 1 0) SP2         2
    , pair "I.plus.sp3"             I  1    NoRadical (BS 2 0 0) SP3         2
    , pair "I.plus.radical"         I  1    Singlet   (BS 1 0 0) SP3         2
    , pair "In"                     In 0    NoRadical (BS 0 0 0) None        0
    , pair "In.1"                   In 0    NoRadical (BS 0 0 1) None        0
    , pair "In.3"                   In 0    NoRadical (BS 3 0 0) None        0
    , pair "In.3plus"               In 3    NoRadical (BS 0 0 0) None        0
    , pair "K.metallic"             K  0    NoRadical (BS 0 0 0) None        0
    , pair "K.neutral"              K  0    NoRadical (BS 1 0 0) None        0
    , pair "K.plus"                 K  1    NoRadical (BS 0 0 0) S           0
    , pair "Kr"                     Kr 0    NoRadical (BS 0 0 0) None        0
    , pair "Li.neutral"             Li 0    NoRadical (BS 0 0 0) None        0
    , pair "Li"                     Li 0    NoRadical (BS 1 0 0) S           0
    , pair "Li.plus"                Li 1    NoRadical (BS 0 0 0) None        0
    , pair "Mg.neutral.1"           Mg 0    NoRadical (BS 0 1 0) None        0
    , pair "Mg.neutral.2"           Mg 0    NoRadical (BS 2 0 0) None        0
    , pair "Mg.neutral"             Mg 0    NoRadical (BS 4 0 0) None        0
    , pair "Mg.2plus"               Mg 2    NoRadical (BS 0 0 0) S           0
    , pair "Mn.metallic"            Mn 0    NoRadical (BS 0 0 0) None        0
    , pair "Mn.2"                   Mn 0    NoRadical (BS 2 0 0) None        0
    , pair "Mn.2plus"               Mn 2    NoRadical (BS 0 0 0) None        0
    , pair "Mn.3plus"               Mn 3    NoRadical (BS 0 0 0) None        0
    , pair "Mo.metallic"            Mo 0    NoRadical (BS 0 0 0) None        0
    , pair "Mo.4"                   Mo 0    NoRadical (BS 2 2 0) None        0
    , pair "N.minus.sp2"            N  (-1) NoRadical (BS 0 1 0) SP2         2
    , pair "N.minus.sp3"            N  (-1) NoRadical (BS 2 0 0) SP3         2
    , pair "N.sp1"                  N  0    NoRadical (BS 0 0 1) SP          1
    , pair "N.sp1.2"                N  0    NoRadical (BS 0 1 1) SP          0
    , pair "N.sp2"                  N  0    NoRadical (BS 1 1 0) SP2         1
    , pair "N.sp2.3"                N  0    NoRadical (BS 1 2 0) SP2         0
    , pair "N.sp3"                  N  0    NoRadical (BS 3 0 0) SP3         1
    , pair "N.oxide"                N  0    NoRadical (BS 3 1 0) SP2         0
    , pair "N.sp2.radical"          N  0    Singlet   (BS 0 1 0) SP2         1
    , pair "N.sp3.radical"          N  0    Singlet   (BS 2 0 0) SP3         1
    , pair "N.plus.sp1"             N  1    NoRadical (BS 1 0 1) SP          0
    , pair "N.plus.sp2"             N  1    NoRadical (BS 2 1 0) SP2         0
    , pair "N.plus"                 N  1    NoRadical (BS 4 0 0) SP3         0
    , pair "N.plus.sp2.radical"     N  1    Singlet   (BS 1 1 0) SP2         0
    , pair "N.plus.sp3.radical"     N  1    Singlet   (BS 3 0 0) SP3         0
    , pair "Na.neutral"             Na 0    NoRadical (BS 0 0 0) None        0
    , pair "Na"                     Na 0    NoRadical (BS 1 0 0) S           0
    , pair "Na.plus"                Na 1    NoRadical (BS 0 0 0) S           0
    , pair "Ne"                     Ne 0    NoRadical (BS 0 0 0) None        0
    , pair "Ni.metallic"            Ni 0    NoRadical (BS 0 0 0) None        0
    , pair "Ni"                     Ni 0    NoRadical (BS 2 0 0) None        0
    , pair "Ni.plus"                Ni 1    NoRadical (BS 1 0 0) None        0
    , pair "Ni.2plus"               Ni 2    NoRadical (BS 0 0 0) None        0
    , pair "O.minus2"               O  (-2) NoRadical (BS 0 0 0) SP3         4
    , pair "O.minus"                O  (-1) NoRadical (BS 1 0 0) SP3         3
    , pair "O.sp2"                  O  0    NoRadical (BS 0 1 0) SP2         2
    , pair "O.sp3"                  O  0    NoRadical (BS 2 0 0) SP3         2
    , pair "O.sp3.radical"          O  0    Singlet   (BS 1 0 0) SP3         2
    , pair "O.plus.sp1"             O  1    NoRadical (BS 0 0 1) SP          1
    , pair "O.plus.sp2"             O  1    NoRadical (BS 1 1 0) SP2         1
    , pair "O.plus"                 O  1    NoRadical (BS 3 0 0) SP3         1
    , pair "O.plus.sp2.radical"     O  1    Singlet   (BS 0 1 0) SP2         1
    , pair "O.plus.radical"         O  1    Singlet   (BS 2 0 0) SP3         1
    , pair "P.ide"                  P  0    NoRadical (BS 0 0 1) SP          1
    , pair "P.irane"                P  0    NoRadical (BS 1 1 0) Planar      1
    , pair "P.ine"                  P  0    NoRadical (BS 3 0 0) SP3         1
    , pair "P.ate"                  P  0    NoRadical (BS 3 1 0) SP3         0
    , pair "P.ane"                  P  0    NoRadical (BS 5 0 0) SP3D1       0
    , pair "P.se.3"                 P  0    Singlet   (BS 0 0 0) SP3         0
    , pair "P.sp1.plus"             P  1    NoRadical (BS 0 2 0) SP          0
    , pair "P.anium"                P  1    NoRadical (BS 2 1 0) SP2         0
    , pair "P.ate.charged"          P  1    NoRadical (BS 4 0 0) SP3         0
    , pair "Pb.neutral"             Pb 0    NoRadical (BS 0 0 0) None        0
    , pair "Pb.1"                   Pb 0    NoRadical (BS 0 1 0) SP          0
    , pair "Pb.2plus"               Pb 2    NoRadical (BS 0 0 0) None        0
    , pair "Po"                     Po 0    NoRadical (BS 2 0 0) None        0
    , pair "Pt.2"                   Pt 0    NoRadical (BS 2 0 0) None        0
    , pair "Pt.4"                   Pt 0    NoRadical (BS 4 0 0) None        0
    , pair "Pt.6"                   Pt 0    NoRadical (BS 6 0 0) None        0
    , pair "Pt.2plus"               Pt 2    NoRadical (BS 0 0 0) None        0
    , pair "Pt.2plus.4"             Pt 2    NoRadical (BS 4 0 0) None        0
    , pair "Pu"                     Pu 0    NoRadical (BS 0 0 0) None        0
    , pair "Ra.neutral"             Ra 0    NoRadical (BS 0 0 0) None        0
    , pair "Rb.neutral"             Rb 0    NoRadical (BS 1 0 0) None        0
    , pair "Rb.plus"                Rb 1    NoRadical (BS 0 0 0) None        0
    , pair "Rn"                     Rn 0    NoRadical (BS 0 0 0) None        0
    , pair "Ru.3minus.6"            Ru (-3) NoRadical (BS 6 0 0) Octahedral  0
    , pair "Ru.2minus.6"            Ru (-2) NoRadical (BS 6 0 0) Octahedral  0
    , pair "Ru.6"                   Ru 0    NoRadical (BS 6 0 0) SP3D2       0
    , pair "S.2minus"               S  (-2) NoRadical (BS 0 0 0) None        4
    , pair "S.minus"                S  (-1) NoRadical (BS 1 0 0) SP3         3
    , pair "S.2"                    S  0    NoRadical (BS 0 1 0) SP2         2
    , pair "S.oxide"                S  0    NoRadical (BS 0 2 0) Planar      3
    , pair "S.trioxide"             S  0    NoRadical (BS 0 3 0) SP2         0
    , pair "S.inyl.2"               S  0    NoRadical (BS 1 0 1) SP2         0
    , pair "S.3"                    S  0    NoRadical (BS 2 0 0) SP3         2
    , pair "S.inyl"                 S  0    NoRadical (BS 2 1 0) SP2         0
    , pair "S.sp3.4"                S  0    NoRadical (BS 2 2 0) SP3         0
    , pair "S.anyl"                 S  0    NoRadical (BS 4 0 0) SP3D2       1
    , pair "S.sp3d1"                S  0    NoRadical (BS 4 1 0) SP3D1       0
    , pair "S.octahedral"           S  0    NoRadical (BS 6 0 0) SP3D2       0
    , pair "S.plus"                 S  1    NoRadical (BS 1 1 0) SP2         1
    , pair "S.inyl.charged"         S  1    NoRadical (BS 3 0 0) SP2         0
    , pair "S.onyl.charged"         S  2    NoRadical (BS 2 2 0) SP3         0
    , pair "Sb.3"                   Sb 0    NoRadical (BS 3 0 0) SP3         1
    , pair "Sb.4"                   Sb 0    NoRadical (BS 3 1 0) None        0
    , pair "Sc.3minus"              Sc (-3) NoRadical (BS 6 0 0) Octahedral  0
    , pair "Se.2minus"              Se (-2) NoRadical (BS 0 0 0) None        4
    , pair "Se.2"                   Se 0    NoRadical (BS 0 0 0) None        0
    , pair "Se.1"                   Se 0    NoRadical (BS 0 1 0) SP2         2
    , pair "Se.sp2.2"               Se 0    NoRadical (BS 0 2 0) SP2         1
    , pair "Se.3"                   Se 0    NoRadical (BS 2 0 0) SP3         2
    , pair "Se.sp3.3"               Se 0    NoRadical (BS 2 1 0) SP3         1
    , pair "Se.sp3.4"               Se 0    NoRadical (BS 2 2 0) SP3         0
    , pair "Se.sp3d1.4"             Se 0    NoRadical (BS 4 0 0) SP3D1       1
    , pair "Se.5"                   Se 0    NoRadical (BS 4 1 0) SP3D1       0
    , pair "Se.plus.3"              Se 1    NoRadical (BS 3 0 0) SP3         1
    , pair "Se.4plus"               Se 4    NoRadical (BS 0 0 0) None        0
    , pair "Si.2minus.6"            Si (-2) NoRadical (BS 6 0 0) SP3D2       0
    , pair "Si.2"                   Si 0    NoRadical (BS 0 2 0) SP          0
    , pair "Si.3"                   Si 0    NoRadical (BS 2 1 0) SP3         0
    , pair "Si.sp3"                 Si 0    NoRadical (BS 4 0 0) SP3         0
    , pair "Sn.sp3"                 Sn 0    NoRadical (BS 4 0 0) SP3         0
    , pair "Sr.2plus"               Sr 2    NoRadical (BS 0 0 0) None        0
    , pair "Te.3"                   Te 0    NoRadical (BS 2 0 0) SP3         2
    , pair "Te.4plus"               Te 4    NoRadical (BS 0 0 0) None        1
    , pair "Th"                     Th 0    NoRadical (BS 0 0 0) None        0
    , pair "Ti.3minus"              Ti (-3) NoRadical (BS 6 0 0) Octahedral  0
    , pair "Ti.2"                   Ti 0    NoRadical (BS 0 2 0) Octahedral  0
    , pair "Ti.sp3"                 Ti 0    NoRadical (BS 4 0 0) SP3         0
    , pair "Tl"                     Tl 0    NoRadical (BS 0 0 0) None        0
    , pair "Tl.1"                   Tl 0    NoRadical (BS 1 0 0) SP          1
    , pair "Tl.plus"                Tl 1    NoRadical (BS 0 0 0) None        0
    , pair "V.3minus.4"             V  (-3) NoRadical (BS 3 1 0) Tetrahedral 0
    , pair "V.3minus"               V  (-3) NoRadical (BS 6 0 0) Octahedral  0
    , pair "W.metallic"             W  0    NoRadical (BS 0 0 0) None        0
    , pair "Xe"                     Xe 0    NoRadical (BS 0 0 0) None        0
    , pair "Xe.3"                   Xe 0    NoRadical (BS 4 0 0) SP3D2       0
    , pair "Zn.metallic"            Zn 0    NoRadical (BS 0 0 0) None        0
    , pair "Zn.1"                   Zn 0    NoRadical (BS 0 1 0) None        0
    , pair "Zn"                     Zn 0    NoRadical (BS 2 0 0) None        0
    , pair "Zn.2plus"               Zn 2    NoRadical (BS 2 0 0) S           0
    ]

c_allene, c_sp, c_sp2, c_sp3 : AtomType
c_allene = AT "C.allene"  0 SP  0 2 0
c_sp     = AT "C.sp"      0 SP  1 0 1
c_sp2    = AT "C.sp2"     0 SP2 2 1 0
c_sp3    = AT "C.sp3"     0 SP3 4 0 0

-- performance optimized implementation for neutral carbons
atomType C NoRadical 0 bs =
  case bs of
    BS _ 0 0 => c_sp3
    BS _ 1 0 => c_sp2
    BS _ 0 1 => c_sp
    BS 0 2 0 => c_allene
    _        => unknown

-- in the general case, we try to find an atom type
-- by adding up to 4 single bonds to implicit hydrogen atoms
atomType e r c (BS s d t) =
  fromMaybe unknown $
        lookup (hash e c r s     d t) atMap
    <|> lookup (hash e c r (s+1) d t) atMap
    <|> lookup (hash e c r (s+2) d t) atMap
    <|> lookup (hash e c r (s+3) d t) atMap
    <|> lookup (hash e c r (s+4) d t) atMap


-- as with `radical` this is performance optimized for carbons
exactAtomType C NoRadical 0 bs =
  case bs of
    BS 4 0 0 => c_sp3
    BS 2 1 0 => c_sp2
    BS 1 0 3 => c_sp
    BS 0 2 0 => c_allene
    _        => unknown
exactAtomType e r c (BS s d t) =
  fromMaybe unknown $ lookup (hash e c r s d t) atMap
