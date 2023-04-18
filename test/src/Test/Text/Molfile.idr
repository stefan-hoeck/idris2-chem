module Test.Text.Molfile

import Chem
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
node : Gen Node
node = bits32 (linear 1 999)

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
bond = [| MkBond (pure 0) (pure 0) bondType bondStereo bondTopo |]

export
bondEdge : Gen (LEdge Bond)
bondEdge = adj <$> edge 998 bond
  where
    adj : LEdge Bond -> LEdge Bond
    adj (MkLEdge e@(MkEdge n1 n2 prf) (MkBond _ _ t s x)) =
      MkLEdge e (MkBond n1 n2 t s x)

export
radical : Gen Radical
radical = element [NoRadical, Singlet, Doublet, Triplet]

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
propRead s = property1 $ case readMol Virtual s of
  Right v       => pure ()
  Left (fc,err) => failWith Nothing $ printParseError s fc err

export
props : Group
props = MkGroup "Molfile Properties"
  [ ("prop_count", rw counts counts counts)
  , ("prop_atom",  rw atom atom atom)
  , ("prop_bond",  rw bondEdge bond bond)
  , ("prop_large",  propRead mfLarge)
  , ("prop_medium",  propRead mfMedium)
  ]
