module Test.Text.Molfile.Generators

import public Test.Chem.Generators
import public Test.Data.Graph.Generators
import public Text.Molfile
import public Text.Molfile.SDF

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
atom : Gen (Maybe AtomGroup) -> Gen MolAtom
atom nr =
  [| MkAtom isotope charge coords radical u u u nr |]

export
simpleAtom : Gen MolAtom
simpleAtom =
  [| MkAtom (map cast elem) (pure 0) coords (pure NoRadical) u u u (pure Nothing) |]

export
bondStereo : Gen BondStereo
bondStereo = element [NoBondStereo,Up,CisOrTrans,UpOrDown,Down]

export
bondTopo : Gen BondTopo
bondTopo = element [AnyTopology,Ring,Chain]

export
bond : Gen MolBond
bond = [| MkBond bool bondOrder bondStereo |]

export
bondEdge : Gen (Edge 999 MolBond)
bondEdge = edge bond

lbl : Gen String
lbl = string (linear 1 10) alphaNum

groups : Gen (List AtomGroup)
groups = withIndex [<] 1 <$> list (linear 0 4) lbl
  where
    withIndex : SnocList AtomGroup -> Nat -> List String -> List AtomGroup
    withIndex sa n []      = sa <>> []
    withIndex sa n (l::ls) = withIndex (sa :< G n l) (S n) ls

group : List AtomGroup -> Gen (Maybe AtomGroup)
group []     = pure Nothing
group (h::t) = maybe (element $ h :: Vect.fromList t)

export
molFile : Gen Molfile
molFile = do
  gs <- groups
  [| MkMolfile
       molLine
       molLine
       molLine
       (lgraph (linear 1 30) (linear 0 30) bond (atom $ group gs))
  |]

--------------------------------------------------------------------------------
-- SD Files
--------------------------------------------------------------------------------

export
sdHeader : Gen SDHeader
sdHeader = fromMaybe "" . refineSDHeader <$> string (linear 0 70) alphaNum

export
sdValue : Gen SDValue
sdValue = fromMaybe "" . refineSDValue <$> string (linear 0 300) printableAscii

export
structureData : Gen StructureData
structureData = [| SD sdHeader sdValue |]

export
sdFile : Gen SDFile
sdFile = [| SDF molFile (list (linear 0 5) structureData) |]
