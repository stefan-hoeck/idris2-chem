module Test.Text.Molfile.Generators

import public Test.Chem.Generators
import public Test.Data.Graph.Generators
import public Text.Molfile

import Data.Vect

%default total

export
molLine : Gen MolLine
molLine =
  fromMaybe "" . refineMolLine <$> string (linear 0 80) printableAscii

export
molVersion : Gen MolVersion
molVersion = element [V2000, V3000]

export
chiralFlag : Gen ChiralFlag
chiralFlag = element [NonChiral, Chiral]

export
count : Gen Nat
count = nat (linear 0 999)

export
smallCount : Gen Nat
smallCount = nat (linear 0 30)

export
counts : Gen Counts
counts = [| MkCounts count count chiralFlag molVersion |]

export
smallCounts : Gen Counts
smallCounts = [| MkCounts smallCount smallCount chiralFlag molVersion |]

export
stereoParity : Gen StereoParity
stereoParity = element [NoStereo, OddStereo, EvenStereo, AnyStereo]

export
stereoCareBox : Gen StereoCareBox
stereoCareBox = element [IgnoreStereo, MatchStereo]

export
valence : Gen Valence
valence = fromMaybe 0 . refineValence <$> bits8 (linear 0 15)

export
h0Designator : Gen H0Designator
h0Designator = element [H0NotSpecified, NoHAllowed]

export
hydrogenCount : Gen HydrogenCount
hydrogenCount = fromMaybe 0 . refineHydrogenCount <$> bits8 (linear 0 5)

export
coordinate : Gen Coordinate
coordinate =
  fromMaybe 0 . refineCoordinate <$>
  integer (exponentialFrom 0 (-9999_9999) 99999_9999)

export
coords : Gen (Vect 3 Coordinate)
coords = vect 3 coordinate

u : Gen ()
u = pure ()

export
atom : Gen MolAtom
atom = [| MkAtom isotope charge coords radical u u u u |]

export
bondType : Gen BondType
bondType = element [Single,Dbl,Triple]

export
bondStereo : Gen BondStereo
bondStereo = element [NoBondStereo,Up,CisOrTrans,UpOrDown,Down]

export
bondTopo : Gen BondTopo
bondTopo = element [AnyTopology,Ring,Chain]

export
bond : Gen MolBond
bond = [| MkBond bool bondType bondStereo |]

export
bondEdge : Gen (Edge 999 MolBond)
bondEdge = edge bond

export
molFile : Gen Molfile
molFile =
  [| MkMolfile
       molLine
       molLine
       molLine
       (lgraph (linear 0 30) (linear 0 30) bond atom)
  |]
