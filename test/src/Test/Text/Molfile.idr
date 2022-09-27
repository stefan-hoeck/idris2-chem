module Test.Text.Molfile

import Chem.Element
import Chem.Types
import Data.Refined
import Data.String
import Data.Vect
import Hedgehog
import Test.Chem.Element
import Test.Chem.Types
import Text.Molfile.Float
import Text.Molfile.Reader
import Text.Molfile.Types
import Text.RW

%default total

export
molLine : Gen MolLine
molLine = fromMaybe "" . refine <$> string (linear 0 80) printableAscii

export
molVersion : Gen MolVersion
molVersion = element [V2000, V3000]

export
chiralFlag : Gen ChiralFlag
chiralFlag = element [NonChiral, Chiral]

export
count : Gen Count
count = fromMaybe 0 . refine <$> bits16 (linear 0 999)

export
smallCount : Gen Count
smallCount = fromMaybe 0 . refine <$> bits16 (linear 0 30)

export
counts : Gen Counts
counts = [| MkCounts count count chiralFlag molVersion |]

export
smallCounts : Gen Counts
smallCounts = [| MkCounts smallCount smallCount chiralFlag molVersion |]

export
atomSymbol : Gen AtomSymbol
atomSymbol = frequency [ (10, map El element)
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
valence =
  frequency
    [ (1, pure NoValence)
    , (10, fromMaybe NoValence . refineSo MkValence <$> bits8 (linear 0 14))
    ]

export
h0Designator : Gen H0Designator
h0Designator = element [H0NotSpecified, NoHAllowed]

export
atomCharge : Gen AtomCharge
atomCharge =
  frequency
    [ (1, pure DoubletRadical)
    , (10, fromMaybe DoubletRadical
         . refineSo MkCharge <$> int8 (linearFrom 0 (-3) 3))
    ]

export
invRetentionFlag : Gen InvRetentionFlag
invRetentionFlag = element [InvNotApplied, ConfigInverted, ConfigRetained]

export
exactChangeFlag : Gen ExactChangeFlag
exactChangeFlag = element [ChangeNotApplied, ExactChange]

export
massDiff : Gen MassDiff
massDiff = fromMaybe 0 . refine <$> int8 (linearFrom 0 (-3) 4)

export
hydrogenCount : Gen HydrogenCount
hydrogenCount =
  frequency
    [ (1, pure NoHC)
    , (10, fromMaybe NoHC . refineSo HC <$> bits8 (linear 0 4))
    ]

export
atomRef : Gen AtomRef
atomRef = fromMaybe 1 . refine <$> bits32 (linear 1 999)

export
coordinate : Gen Coordinate
coordinate =
  fromMaybe (MkFloat 0 0 Oh Oh) <$> 
  [| refine (int32 (linear (-9999) 99999)) (bits32 (linear 0 9999)) |]

export
atom : Gen Atom
atom =
  [| MkAtom coordinate coordinate coordinate atomSymbol massDiff atomCharge
            stereoParity hydrogenCount stereoCareBox valence
            h0Designator atomRef invRetentionFlag exactChangeFlag |]

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
reactingCenterStatus : Gen ReactingCenterStatus
reactingCenterStatus =
  element [ Unmarked, NotACenter, Center, NoChange, BondMadeBroken
          , BondOrderChange, BondMBAndOC, CenterBMB, CenterBOC, CenterBMBAndOC]

export
bond : Gen Bond
bond =
  [| MkBond atomRef atomRef bondType bondStereo bondTopo
            reactingCenterStatus |]

export
radical : Gen Radical
radical = element [NoRadical, Singlet, Doublet, Triplet]

genN8 : Gen a -> (f : (c : N8) -> Vect (cast c.value) (AtomRef,a) -> b) -> Gen b
genN8 ga f = do
  c  <- fromMaybe 1 . N8.refine <$> bits8 (linear 1 8)
  ps <- vect (cast c.value) [| MkPair atomRef ga |]
  pure $ f c ps

export
prop : Gen Text.Molfile.Types.Property
prop = frequency [ (10, genN8 charge Chg)
                 , (10, genN8 massNr Iso)
                 , (10, genN8 radical Rad)
                 ]

export
molFile : Gen MolFile
molFile = do
  n  <- molLine
  i  <- molLine
  c  <- molLine
  cs <- smallCounts
  as <- vect (cast cs.atoms.value) atom
  bs <- vect (cast cs.bonds.value) bond
  ps <- list (linear 0 30) prop
  pure (MkMolFile n i c cs as bs ps)

--------------------------------------------------------------------------------
--          Properties
--------------------------------------------------------------------------------

rw :  Eq a
   => Show a
   => Gen a
   -> (read : String -> Either String a)
   -> (write : a -> String)
   -> Hedgehog.Property
rw gen rd wt = property $ do
  v <- forAll gen
  let str : String
      str = wt v
  
  footnote ("Encoded: " ++ str)
  
  rd str === Right v


export
props : Group
props = MkGroup "Molfile Properties"
          [ ("prop_count", rw counts counts writeCounts)
          , ("prop_atom",  rw atom atom writeAtom)
          , ("prop_bond",  rw bond bond writeBond)
          , ("prop_mol",   rw molFile mol writeMol)
          ]
