module Test.Text.Molfile

import Chem
import Data.List.Quantifiers.Extra
import Data.Maybe
import Data.Refined
import Data.Vect
import Data.Refined.Bits32
import Data.Refined.Int32
import Data.Refined.Integer
import Hedgehog
import Test.Chem.Element
import Test.Data.Graph
import Test.Text.Molfile.Examples
import Text.Molfile
import Text.Parse.Manual

%default total

export
molLine : Gen MolLine
molLine = fromMaybe "" . refineMolLine <$> string (linear 0 80) printableAscii

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
atomSymbol : Gen AtomSymbol
atomSymbol = frequency
  [ (10, map El element)
  , (1,  element [L,A,Q,Ast,LP,RSharp])
  ]

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
  fromMaybe 0 . refineCoordinate <$> integer (exponentialFrom 0 (-9999_9999) 99999_9999)

export
coords : Gen (Vect 3 Coordinate)
coords = vect 3 coordinate

export
atom : Gen Atom
atom =
  [| MkAtom coords atomSymbol (pure Nothing) (pure $ the Charge 0)
            stereoParity hydrogenCount stereoCareBox valence
            h0Designator |]

export
bondType : Gen BondType
bondType = element [Single,Dbl,Triple,Aromatic,SngOrDbl
                   ,SngOrAromatic,DblOrAromatic,AnyBond]

export
bondStereo : Gen BondStereo
bondStereo = element [NoBondStereo,Up,CisOrTrans,UpOrDown,Down]

export
bondTopo : Gen BondTopo
bondTopo = element [AnyTopology,Ring,Chain]

export
bond : Gen Bond
bond = [| MkBond bool bondType bondStereo bondTopo |]

export
bondEdge : Gen (Edge 999 Bond)
bondEdge = edge bond

export
radical : Gen Radical
radical = element [NoRadical, Singlet, Doublet, Triplet]

export
molFile : Gen MolFile
molFile =
  [| MkMolFile
       molLine
       molLine
       molLine
       (lgraph (linear 0 30) (linear 0 30) bond atom)
  |]

--------------------------------------------------------------------------------
--          Properties
--------------------------------------------------------------------------------
--
rw :  Eq a
   => Show a
   => Gen a
   -> (tok   : Tok b MolFileError a)
   -> (write : a -> String)
   -> Hedgehog.Property
rw gen tok wt = property $ do
  v <- forAll gen
  let str : String
      str = wt v

  footnote ("Encoded: " ++ str)

  lineTok 0 tok str === Right v

propRead : String -> Property
propRead s = property1 $ case readMol {es = [MolParseErr]} Virtual s of
  Right v         => pure ()
  Left (Here err) => failWith Nothing "\{err}"

propReadRoundTrip : Property
propReadRoundTrip = property $ do
  m <- forAll molFile
  Right m === readMol {es = [MolParseErr]} Virtual (writeMol m)

export
props : Group
props = MkGroup "Molfile Properties"
  [ ("prop_count", rw counts counts counts)
  , ("prop_atom",  rw atom atom atom)
  , ("prop_bond",  rw bondEdge bond bond)
  , ("prop_large",  propRead mfLarge)
  , ("prop_medium",  propRead mfMedium)
  , ("prop_readRoundTrip",  propReadRoundTrip)
  ]
