module Text.Molfile.Writer.V3000

import Text.Molfile.Types
import Text.Molfile.Writer.Util

%default total

export
dispStereoV3 : BondStereo -> String
dispStereoV3 NoBondStereo = "0"
dispStereoV3 Up           = "1"
dispStereoV3 Either       = "2"
dispStereoV3 Down         = "3"

fin : Fin k -> String
fin x = " \{show $ S $ finToNat x}"

mv30line : List String -> String
mv30line = fastConcat . ("M  V30 "::)

counts : (na,nb : Nat) -> String
counts na nb = mv30line ["COUNTS ",show na," ",show nb," 0 0 0"]

coordsV3 : Vect 3 Coordinate -> String
coordsV3 [x,y,z] = " \{disp x} \{disp y} \{disp z} 0" -- zero is AAMAP
  where
    disp : Coordinate -> String
    disp 0 = "0"
    disp c = interpolate c

chrg : Charge -> String
chrg 0 = ""
chrg c = " CHG=\{c}"

rad : Radical -> String
rad NoRadical = ""
rad r         = " RAD=\{dispRadical r}"

mass : Isotope -> String
mass (MkI H (Just 2)) = ""
mass (MkI H (Just 3)) = ""
mass (MkI _ Nothing)  = ""
mass (MkI _ (Just m)) = " MASS=\{show m.value}"

atomsV3 :
     SnocList String
  -> Nat
  -> List (MolAtom' h t c)
  -> SnocList String
atomsV3 ss _ [] = ss :< mv30line ["END ATOM"]
atomsV3 ss n (MkAtom a c pos r _ _ _ l :: t) =
  let s := mv30line [show n, " ", dispIso a, coordsV3 pos, chrg c, rad r, mass a]
   in atomsV3 (ss:<s) (S n) t

cfg : BondStereo -> String
cfg NoBondStereo = ""
cfg x            = " CFG=\{dispStereoV3 x}"

bondsV3 :
     SnocList String
  -> Nat
  -> List (Edge k MolBond)
  -> SnocList String
bondsV3 ss n []                          = ss :< mv30line ["END BOND"]
bondsV3 ss n (E x y (MkBond b o s) :: t) =
  case b of
    True  =>
     let s := mv30line [show n, " \{o}", fin x, fin y, cfg s]
      in bondsV3 (ss:<s) (S n) t
    False =>
     let s := mv30line [show n, " \{o}", fin y, fin x, cfg s]
      in bondsV3 (ss:<s) (S n) t

export
molLines3000 : (name, info, comment : MolLine) -> MolGraph' h t c -> List String
molLines3000 n i c (G 0 _) = []
molLines3000 n i c (G o g) =
 let s1 := [<n.value,i.value,c.value,"00000999 V3000"]
     es := edges g
     s2 := s1 :< mv30line ["BEGIN CTAB"] :< counts o (length es)
     s3 := atomsV3 (s2:<mv30line ["BEGIN ATOM"]) 1 (labels g)
     s4 := bondsV3 (s3:<mv30line ["BEGIN BOND"]) 1 es
  in s4 <>> [mv30line ["END CTAB"], "M  END"]
