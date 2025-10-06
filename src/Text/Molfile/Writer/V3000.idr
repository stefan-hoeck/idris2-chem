module Text.Molfile.Writer.V3000

import Data.Linear.Traverse1
import Data.SortedMap
import Data.String
import Data.String.Builder
import Syntax.T1
import Text.Molfile.Types
import Text.Molfile.Writer.Util
import Text.Molfile.Writer.V2000

%hide Prelude.(>>)

%default total

export
dispStereoV3 : BondStereo -> String
dispStereoV3 NoBondStereo = "0"
dispStereoV3 Up           = "1"
dispStereoV3 Either       = "2"
dispStereoV3 Down         = "3"

parameters {auto b : Builder q}

  chrg : Charge -> F1' q
  chrg 0 = pure ()
  chrg c = putText " CHG=\{c}"

  rad : Radical -> F1' q
  rad NoRadical = pure ()
  rad r         = putText " RAD=\{dispRadical r}"

  mass : Isotope -> F1' q
  mass (MkI H (Just 2)) = linebreak
  mass (MkI H (Just 3)) = linebreak
  mass (MkI _ Nothing)  = linebreak
  mass (MkI _ (Just m)) = putTextLn " MASS=\{show m.value}"

  mv30 : F1' q
  mv30 = putText "M  V30 "

  begin, end : String -> F1' q
  begin s = mv30 >> putText "BEGIN " >> putTextLn s
  end   s = mv30 >> putText "END " >> putTextLn s

  fin : Fin k -> F1' q
  fin x = putText " \{show $ S $ finToNat x}"

  coordsV3 : Vect 3 Coordinate -> F1' q
  coordsV3 [x,y,z] =
    putText " \{dispCoordShort x} \{dispCoordShort y} \{dispCoordShort z} 0"

  counts : (na,nb,ng : Nat) -> F1' q
  counts na nb ng =
    mv30 >> putText "COUNTS " >>
    putShowSep na >> putShowSep nb >> putShow ng >>
    putTextLn " 0 0"

  atomV3 : Fin k -> Adj k MolBond (MolAtom' h t c) -> F1' q
  atomV3 n (A (MkAtom a c pos r _ _ _ l) _) =
    mv30 >> putShowSep (S $ finToNat n) >> putText (dispIso a) >>
    coordsV3 pos >> chrg c >> rad r >> mass a

  cfg : BondStereo -> F1' q
  cfg NoBondStereo = linebreak
  cfg x            = putTextLn " CFG=\{dispStereoV3 x}"

  bondsV3 : (Nat, Edge k MolBond) -> F1' q
  bondsV3 (n, E x y (MkBond b o s)) =
   let pre  := mv30 >> putShow (S n) >> putText " \{o}"
    in case b of
      True  => pre >> fin x >> fin y >> cfg s
      False => pre >> fin y >> fin x >> cfg s

  nats : List Nat -> F1' q
  nats ns =
    putText "(\{show $ length ns} " >> traverse1_ putShowSep ns >> putTextLn ")"

  groupV3 : (Nat,String,SnocList Nat) -> F1' q
  groupV3 (n,l,x) =
    mv30 >> putShow n >> putText " SUP 0 LABEL=\"\{l}\" ATOMS=" >> nats (x<>>[])

  export
  putMol3000 : List (Edge k MolBond) -> MolGraph' h t c -> F1' q
  putMol3000 es (G o g) = T1.do
    let gs := kvList $ foldrKV appendLbl empty g.graph
    putTextLn "00000999 V3000"
    begin "CTAB"
    counts o (length es) (length gs)
    begin "ATOM"
    traverseKV1_ atomV3 g.graph
    end   "ATOM"
    begin "BOND"
    traverse1_ bondsV3 $ zipWithIndex es
    end   "BOND"
    begin "SGROUP"
    traverse1_ groupV3 gs
    end   "SGROUP"
    end "CTAB"
