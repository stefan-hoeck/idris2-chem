module Test.Text.Molfile

import Chem.Element
import Chem.Types
import Data.Refined
import Data.String
import Data.Vect
import Hedgehog
import Test.Chem.Element
import Text.Molfile.Float
import Text.Molfile.Reader
import Text.Molfile.Types

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
counts : Gen Counts
counts = [| MkCounts count count count chiralFlag molVersion |]

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
atomRef = fromMaybe 0 . refine <$> bits32 (linear 0 999)

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

--------------------------------------------------------------------------------
--          Properties
--------------------------------------------------------------------------------

rw :  Eq a
   => Show a
   => Gen a
   -> (read : String -> Maybe a)
   -> (write : a -> String)
   -> Hedgehog.Property
rw gen read write = property $ do
  v <- forAll gen
  let str : String
      str = write v
  
  footnote ("Encoded: " ++ str)
  
  read str === Just v


export
props : Group
props = MkGroup "Molfile Properties"
          [ ("prop_atom", rw atom atom writeAtom)
          , ("prop_bond", rw bond bond writeBond)
          ]

--------------------------------------------------------------------------------
--          Proofs
--------------------------------------------------------------------------------

molVersionRW : (v : MolVersion) -> Just v = MolVersion.read (write v)
molVersionRW V2000 = Refl
molVersionRW V3000 = Refl

chiralFlagRW : (v : ChiralFlag) -> Just v = ChiralFlag.read (write v)
chiralFlagRW NonChiral = Refl
chiralFlagRW Chiral    = Refl

atomSymbolRW : (v : AtomSymbol) -> Just v = AtomSymbol.read (write v)
atomSymbolRW L        = Refl
atomSymbolRW A        = Refl
atomSymbolRW Q        = Refl
atomSymbolRW Ast      = Refl
atomSymbolRW LP       = Refl
atomSymbolRW RSharp   = Refl
atomSymbolRW (El H)   = Refl
atomSymbolRW (El He)  = Refl
atomSymbolRW (El Li)  = Refl
atomSymbolRW (El Be)  = Refl
atomSymbolRW (El B)   = Refl
atomSymbolRW (El C)   = Refl
atomSymbolRW (El N)   = Refl
atomSymbolRW (El O)   = Refl
atomSymbolRW (El F)   = Refl
atomSymbolRW (El Ne)  = Refl
atomSymbolRW (El Na)  = Refl
atomSymbolRW (El Mg)  = Refl
atomSymbolRW (El Al)  = Refl
atomSymbolRW (El Si)  = Refl
atomSymbolRW (El P)   = Refl
atomSymbolRW (El S)   = Refl
atomSymbolRW (El Cl)  = Refl
atomSymbolRW (El Ar)  = Refl
atomSymbolRW (El K)   = Refl
atomSymbolRW (El Ca)  = Refl
atomSymbolRW (El Sc)  = Refl
atomSymbolRW (El Ti)  = Refl
atomSymbolRW (El V)   = Refl
atomSymbolRW (El Cr)  = Refl
atomSymbolRW (El Mn)  = Refl
atomSymbolRW (El Fe)  = Refl
atomSymbolRW (El Co)  = Refl
atomSymbolRW (El Ni)  = Refl
atomSymbolRW (El Cu)  = Refl
atomSymbolRW (El Zn)  = Refl
atomSymbolRW (El Ga)  = Refl
atomSymbolRW (El Ge)  = Refl
atomSymbolRW (El As)  = Refl
atomSymbolRW (El Se)  = Refl
atomSymbolRW (El Br)  = Refl
atomSymbolRW (El Kr)  = Refl
atomSymbolRW (El Rb)  = Refl
atomSymbolRW (El Sr)  = Refl
atomSymbolRW (El Y)   = Refl
atomSymbolRW (El Zr)  = Refl
atomSymbolRW (El Nb)  = Refl
atomSymbolRW (El Mo)  = Refl
atomSymbolRW (El Tc)  = Refl
atomSymbolRW (El Ru)  = Refl
atomSymbolRW (El Rh)  = Refl
atomSymbolRW (El Pd)  = Refl
atomSymbolRW (El Ag)  = Refl
atomSymbolRW (El Cd)  = Refl
atomSymbolRW (El In)  = Refl
atomSymbolRW (El Sn)  = Refl
atomSymbolRW (El Sb)  = Refl
atomSymbolRW (El Te)  = Refl
atomSymbolRW (El I)   = Refl
atomSymbolRW (El Xe)  = Refl
atomSymbolRW (El Cs)  = Refl
atomSymbolRW (El Ba)  = Refl
atomSymbolRW (El La)  = Refl
atomSymbolRW (El Ce)  = Refl
atomSymbolRW (El Pr)  = Refl
atomSymbolRW (El Nd)  = Refl
atomSymbolRW (El Pm)  = Refl
atomSymbolRW (El Sm)  = Refl
atomSymbolRW (El Eu)  = Refl
atomSymbolRW (El Gd)  = Refl
atomSymbolRW (El Tb)  = Refl
atomSymbolRW (El Dy)  = Refl
atomSymbolRW (El Ho)  = Refl
atomSymbolRW (El Er)  = Refl
atomSymbolRW (El Tm)  = Refl
atomSymbolRW (El Yb)  = Refl
atomSymbolRW (El Lu)  = Refl
atomSymbolRW (El Hf)  = Refl
atomSymbolRW (El Ta)  = Refl
atomSymbolRW (El W)   = Refl
atomSymbolRW (El Re)  = Refl
atomSymbolRW (El Os)  = Refl
atomSymbolRW (El Ir)  = Refl
atomSymbolRW (El Pt)  = Refl
atomSymbolRW (El Au)  = Refl
atomSymbolRW (El Hg)  = Refl
atomSymbolRW (El Tl)  = Refl
atomSymbolRW (El Pb)  = Refl
atomSymbolRW (El Bi)  = Refl
atomSymbolRW (El Po)  = Refl
atomSymbolRW (El At)  = Refl
atomSymbolRW (El Rn)  = Refl
atomSymbolRW (El Fr)  = Refl
atomSymbolRW (El Ra)  = Refl
atomSymbolRW (El Ac)  = Refl
atomSymbolRW (El Th)  = Refl
atomSymbolRW (El Pa)  = Refl
atomSymbolRW (El U)   = Refl
atomSymbolRW (El Np)  = Refl
atomSymbolRW (El Pu)  = Refl
atomSymbolRW (El Am)  = Refl
atomSymbolRW (El Cm)  = Refl
atomSymbolRW (El Bk)  = Refl
atomSymbolRW (El Cf)  = Refl
atomSymbolRW (El Es)  = Refl
atomSymbolRW (El Fm)  = Refl
atomSymbolRW (El Md)  = Refl
atomSymbolRW (El No)  = Refl
atomSymbolRW (El Lr)  = Refl
atomSymbolRW (El Rf)  = Refl
atomSymbolRW (El Db)  = Refl
atomSymbolRW (El Sg)  = Refl
atomSymbolRW (El Bh)  = Refl
atomSymbolRW (El Hs)  = Refl
atomSymbolRW (El Mt)  = Refl
atomSymbolRW (El Ds)  = Refl
atomSymbolRW (El Rg)  = Refl
atomSymbolRW (El Cn)  = Refl
atomSymbolRW (El Uut) = Refl
atomSymbolRW (El Fl)  = Refl
atomSymbolRW (El Uup) = Refl
atomSymbolRW (El Lv)  = Refl
atomSymbolRW (El Uus) = Refl
atomSymbolRW (El Uuo) = Refl

stereoParityRW : (v : StereoParity) -> Just v = StereoParity.read (write v)
stereoParityRW NoStereo   = Refl
stereoParityRW OddStereo  = Refl
stereoParityRW EvenStereo = Refl
stereoParityRW AnyStereo  = Refl

stereoCareBoxRW : (v : StereoCareBox) -> Just v = StereoCareBox.read (write v)
stereoCareBoxRW IgnoreStereo = Refl
stereoCareBoxRW MatchStereo  = Refl

h0DesignatorRW : (v : H0Designator) -> Just v = H0Designator.read (write v)
h0DesignatorRW H0NotSpecified = Refl
h0DesignatorRW NoHAllowed     = Refl

invRetentionFlagRW : (v : InvRetentionFlag) -> Just v = InvRetentionFlag.read (write v)
invRetentionFlagRW InvNotApplied  = Refl
invRetentionFlagRW ConfigInverted = Refl
invRetentionFlagRW ConfigRetained = Refl

exactChangeFlagRW : (v : ExactChangeFlag) -> Just v = ExactChangeFlag.read (write v)
exactChangeFlagRW ChangeNotApplied = Refl
exactChangeFlagRW ExactChange      = Refl

bondTypeRW : (v : BondType) -> Just v = BondType.read (write v)
bondTypeRW Single        = Refl
bondTypeRW Dbl           = Refl
bondTypeRW Triple        = Refl
bondTypeRW Aromatic      = Refl
bondTypeRW SngOrDbl      = Refl
bondTypeRW SngOrAromatic = Refl
bondTypeRW DblOrAromatic = Refl
bondTypeRW AnyBond       = Refl

bondStereoRW : (v : BondStereo) -> Just v = BondStereo.read (write v)
bondStereoRW NoBondStereo = Refl
bondStereoRW Up           = Refl
bondStereoRW CisOrTrans   = Refl
bondStereoRW UpOrDown     = Refl
bondStereoRW Down         = Refl

bondTopoRW : (v : BondTopo) -> Just v = BondTopo.read (write v)
bondTopoRW AnyTopology = Refl
bondTopoRW Ring        = Refl
bondTopoRW Chain       = Refl

reactingCenterStatusRW : (v : ReactingCenterStatus) -> Just v = ReactingCenterStatus.read (write v)
reactingCenterStatusRW Unmarked        = Refl
reactingCenterStatusRW NotACenter      = Refl
reactingCenterStatusRW Center          = Refl
reactingCenterStatusRW NoChange        = Refl
reactingCenterStatusRW BondMadeBroken  = Refl
reactingCenterStatusRW BondOrderChange = Refl
reactingCenterStatusRW BondMBAndOC     = Refl
reactingCenterStatusRW CenterBMB       = Refl
reactingCenterStatusRW CenterBOC       = Refl
reactingCenterStatusRW CenterBMBAndOC  = Refl
