||| Some of the refined types in here should probably
||| go to their own dedicated module
module Text.Molfile.Types

import Chem.Element
import Chem.Types
import public Data.Refined
import Data.Nat
import Data.String
import Data.Vect
import Generics.Derive
import Language.Reflection.Refined
import Text.Molfile.Float
import Text.RW

--------------------------------------------------------------------------------
--          Pragmas
--------------------------------------------------------------------------------

%default total

%language ElabReflection

%hide Language.Reflection.TT.Count

--------------------------------------------------------------------------------
--          V2000 Mol Lines
--------------------------------------------------------------------------------

public export %inline
isMolLine : String -> Bool
isMolLine s = length s <= 80 && all isPrintableAscii s

||| An uninterpreted line in a v2000 mol file
public export
record MolLine where
  constructor MkMolLine
  value : String
  0 prf : So (isMolLine value)

%runElab refinedString "MolLine"

export %hint %inline
readMolLine : Read MolLine
readMolLine = mkRead refine "MolLine"

export %hint %inline
writeMolLine : Write MolLine
writeMolLine = MkWrite value

--------------------------------------------------------------------------------
--          Counts Line
--------------------------------------------------------------------------------

------------------------------
-- MolVersion

public export
data MolVersion = V2000 | V3000

%runElab derive "MolVersion" [Generic,Meta,Eq,Ord,Show]

namespace MolVersion
  rd : String -> Maybe MolVersion
  rd "v2000" = Just V2000
  rd "v3000" = Just V3000
  rd "V2000" = Just V2000
  rd "V3000" = Just V3000
  rd _       = Nothing

  wt : MolVersion -> String
  wt V2000 = "v2000"
  wt V3000 = "v3000"

  export %hint %inline
  readImpl : Read MolVersion
  readImpl = mkRead rd "MolVersion"

  export %hint %inline
  writeImpl : Write MolVersion
  writeImpl = MkWrite wt

------------------------------
-- ChiralFlag

public export
data ChiralFlag = NonChiral | Chiral

%runElab derive "ChiralFlag" [Generic,Meta,Eq,Ord,Show]

namespace ChiralFlag
  rd : String -> Maybe ChiralFlag
  rd "0" = Just NonChiral
  rd "1" = Just Chiral
  rd _   = Nothing

  wt : ChiralFlag -> String
  wt NonChiral = "0"
  wt Chiral    = "1"

  export %hint %inline
  readImpl : Read ChiralFlag
  readImpl = mkRead rd "ChiralFlag"

  export %hint %inline
  writeImpl : Write ChiralFlag
  writeImpl = MkWrite wt


------------------------------
-- Count

public export
record Count where
  constructor MkCount
  value : Bits16
  0 prf : So (value <= 999)

%runElab rwNat "Count" `(Bits16)


public export
record Counts where
  constructor MkCounts
  atoms     : Count
  bonds     : Count
  chiral    : ChiralFlag
  version   : MolVersion

%runElab derive "Counts" [Generic,Meta,Eq,Show]

--------------------------------------------------------------------------------
--          Atoms
--------------------------------------------------------------------------------

------------------------------
-- AtomSymbol

||| Ast    -> Asterisk
||| RSharp -> R# (RGroupLabel)
public export
data AtomSymbol = L | A | Q | Ast | LP | RSharp | El Elem

%runElab derive "AtomSymbol" [Generic,Eq]

export
Show AtomSymbol where
  show L      = "L"
  show A      = "A"
  show Q      = "Q"
  show Ast    = "*"
  show LP     = "LP"
  show RSharp = "R#"
  show (El x) = symbol x

namespace AtomSymbol
  rd : String -> Maybe AtomSymbol
  rd "L"  = Just L
  rd "A"  = Just A
  rd "Q"  = Just Q
  rd "*"  = Just Ast
  rd "LP" = Just LP
  rd "R#" = Just RSharp
  rd s    = El <$> fromSymbol s

  export %hint %inline
  readImpl : Read AtomSymbol
  readImpl = mkRead rd "AtomSymbol"

  export %hint %inline
  writeImpl : Write AtomSymbol
  writeImpl = MkWrite show

------------------------------
-- StereoParity

||| Atom Stereo parity encoded in V2000 CTAB
public export
data StereoParity = NoStereo
                  | OddStereo
                  | EvenStereo
                  | AnyStereo

%runElab derive "StereoParity" [Generic,Meta,Eq,Ord,Show]

namespace StereoParity
  rd : String -> Maybe StereoParity
  rd "0" = Just NoStereo
  rd "1" = Just OddStereo
  rd "2" = Just EvenStereo
  rd "3" = Just AnyStereo
  rd _   = Nothing

  wt : StereoParity -> String
  wt NoStereo   = "0"
  wt OddStereo  = "1"
  wt EvenStereo = "2"
  wt AnyStereo  = "3"

  export %hint %inline
  readImpl : Read StereoParity
  readImpl = mkRead rd "StereoParity"

  export %hint %inline
  writeImpl : Write StereoParity
  writeImpl = MkWrite wt

------------------------------
-- StereoCareBox

||| Stereo care box encoded in V2000
public export
data  StereoCareBox = IgnoreStereo | MatchStereo

%runElab derive "StereoCareBox" [Generic,Meta,Eq,Ord,Show]

namespace StereoCareBox
  rd : String -> Maybe StereoCareBox
  rd "0" = Just IgnoreStereo
  rd "1" = Just MatchStereo
  rd _   = Nothing

  wt : StereoCareBox -> String
  wt IgnoreStereo = "0"
  wt MatchStereo  = "1"

  export %hint %inline
  readImpl : Read StereoCareBox
  readImpl = mkRead rd "StereoCareBox"

  export %hint %inline
  writeImpl : Write StereoCareBox
  writeImpl = MkWrite wt

------------------------------
-- Valence

||| Valence of atoms
|||
||| NOTE: In a V2000 molfile 15 is zero valence,
||| while 0 means no marking
public export
data Valence : Type where 
  NoValence : Valence
  MkValence : (n : Bits8) -> (0 prf : So (n <= 14)) -> Valence

valenceCode : Valence -> Bits8
valenceCode NoValence       = 0
valenceCode (MkValence 0 _) = 15
valenceCode (MkValence n _) = n

public export %inline
Eq Valence where
  (==) = (==) `on` valenceCode

public export %inline
Ord Valence where
  compare = compare `on` valenceCode

public export %inline
Show Valence where
  show = show . valenceCode

namespace Valence
  rd : String -> Maybe Valence
  rd "0"  = Just NoValence
  rd "15" = Just $ MkValence 0 Oh
  rd s    = readNat s >>= refineSo MkValence

  wt : Valence -> String
  wt NoValence       = "0"
  wt (MkValence 0 _) = "15"
  wt (MkValence n _) = show n

  export %hint %inline
  readImpl : Read Valence
  readImpl = mkRead rd "Valence"

  export %hint %inline
  writeImpl : Write Valence
  writeImpl = MkWrite wt

------------------------------
-- H0Designator

||| Reduntant hydrogen count flag
public export
data H0Designator = H0NotSpecified | NoHAllowed

%runElab derive "H0Designator" [Generic,Meta,Eq,Ord,Show]

namespace H0Designator
  rd : String -> Maybe H0Designator
  rd "0" = Just H0NotSpecified
  rd "1" = Just NoHAllowed
  rd _   = Nothing

  wt : H0Designator -> String
  wt H0NotSpecified = "0"
  wt NoHAllowed     = "1"

  export %hint %inline
  readImpl : Read H0Designator
  readImpl = mkRead rd "H0Designator"

  export %hint %inline
  writeImpl : Write H0Designator
  writeImpl = MkWrite wt

------------------------------
-- AtomCharge

public export
data AtomCharge : Type where 
  DoubletRadical : AtomCharge
  MkCharge : (v : Int8) -> (0 prf : So (abs v <= 3)) -> AtomCharge

chargeCode : AtomCharge -> Int8
chargeCode DoubletRadical = 4
chargeCode (MkCharge 0 _) = 0
chargeCode (MkCharge n _) = 4 - n

public export %inline
Eq AtomCharge where
  (==) = (==) `on` chargeCode

public export %inline
Ord AtomCharge where
  compare = compare `on` chargeCode

export
Show AtomCharge where
  show DoubletRadical   = "DoubletRadical"
  show (MkCharge v prf) = show v

namespace AtomCharge
  rd : String -> Maybe AtomCharge
  rd "0" = Just $ MkCharge 0 Oh
  rd "1" = Just $ MkCharge 3 Oh
  rd "2" = Just $ MkCharge 2 Oh
  rd "3" = Just $ MkCharge 1 Oh
  rd "4" = Just $ DoubletRadical
  rd "5" = Just $ MkCharge (-1) Oh
  rd "6" = Just $ MkCharge (-2) Oh
  rd "7" = Just $ MkCharge (-3) Oh
  rd _   = Nothing

  export %hint %inline
  readImpl : Read AtomCharge
  readImpl = mkRead rd "AtomCharge"

  export %hint %inline
  writeImpl : Write AtomCharge
  writeImpl = MkWrite (show . chargeCode)

------------------------------
-- InvRetentionFlag

public export
data InvRetentionFlag = InvNotApplied
                      | ConfigInverted
                      | ConfigRetained

%runElab derive "InvRetentionFlag" [Generic,Meta,Eq,Ord,Show]

namespace InvRetentionFlag
  rd : String -> Maybe InvRetentionFlag
  rd "0" = Just InvNotApplied
  rd "1" = Just ConfigInverted
  rd "2" = Just ConfigRetained
  rd _   = Nothing

  wt : InvRetentionFlag -> String
  wt InvNotApplied  = "0"
  wt ConfigInverted = "1"
  wt ConfigRetained = "2"

  export %hint %inline
  readImpl : Read InvRetentionFlag
  readImpl = mkRead rd "InvRetentionFlag"

  export %hint %inline
  writeImpl : Write InvRetentionFlag
  writeImpl = MkWrite wt

------------------------------
-- ExactChangeFlag

public export
data ExactChangeFlag = ChangeNotApplied | ExactChange

%runElab derive "ExactChangeFlag" [Generic,Meta,Eq,Ord,Show]

namespace ExactChangeFlag
  rd : String -> Maybe ExactChangeFlag
  rd "0" = Just ChangeNotApplied
  rd "1" = Just ExactChange
  rd _   = Nothing

  wt : ExactChangeFlag -> String
  wt ChangeNotApplied  = "0"
  wt ExactChange       = "1"

  export %hint %inline
  readImpl : Read ExactChangeFlag
  readImpl = mkRead rd "ExactChangeFlag"

  export %hint %inline
  writeImpl : Write ExactChangeFlag
  writeImpl = MkWrite wt

------------------------------
-- MassDiff

||| Mass difference encoded in V2000 CTAB
public export
record MassDiff where
  constructor MkMassDiff
  value : Int8
  0 prf : So ((-3) <= value && value <= 4)

%runElab rwInt "MassDiff" `(Int8)

------------------------------
-- Hydrogen Count

public export
data HydrogenCount : Type where
  NoHC : HydrogenCount
  HC   : (v : Bits8) -> (0 prf : So (v <= 4)) -> HydrogenCount

hcCode : HydrogenCount -> Bits8
hcCode NoHC     = 0
hcCode (HC v _) = v + 1

public export %inline
Eq HydrogenCount where
  (==) = (==) `on` hcCode

public export %inline
Ord HydrogenCount where
  compare = compare `on` hcCode

export
Show HydrogenCount where
  show NoHC     = "NoHC"
  show (HC v _) = show v

namespace HydrogenCount
  rd : String -> Maybe HydrogenCount
  rd "0" = Just $ NoHC
  rd s   = readNat s >>= refineSo HC . (\x => x - 1)

  export %hint %inline
  readImpl : Read HydrogenCount
  readImpl = mkRead rd "HydrogenCount"

  export %hint %inline
  writeImpl : Write HydrogenCount
  writeImpl = MkWrite (show . hcCode)

------------------------------
-- AtomRef

||| Restricted to a max of three digit unsigned numbers
public export
record AtomRef where
  constructor MkAtomRef
  value : Bits32
  0 prf : So (0 <= value && value <= 999)

%runElab rwInt "AtomRef" `(Bits32)

public export
Coordinate : Type
Coordinate = Float (-9999) 99999 4

||| Data on a single V2000 Atom Line
public export
record Atom where
  constructor MkAtom
  x                : Coordinate
  y                : Coordinate
  z                : Coordinate
  symbol           : AtomSymbol
  massDiff         : MassDiff
  charge           : AtomCharge
  stereoParity     : StereoParity
  hydrogenCount    : HydrogenCount
  stereoCareBox    : StereoCareBox
  valence          : Valence
  h0designator     : H0Designator
  atomMapping      : AtomRef
  invRetentionFlag : InvRetentionFlag
  exactChangeFlag  : ExactChangeFlag

%runElab derive "Atom" [Generic,Meta,Eq,Show]

--------------------------------------------------------------------------------
--          Bonds
--------------------------------------------------------------------------------

------------------------------
-- BondType

||| 4 to 8 only for SSS queries
public export
data BondType =
    Single
  | Dbl
  | Triple
  | Aromatic
  | SngOrDbl
  | SngOrAromatic
  | DblOrAromatic
  | AnyBond

%runElab derive "BondType" [Generic,Meta,Eq,Show]

namespace BondType
  rd : String -> Maybe BondType
  rd "1" = Just Single
  rd "2" = Just Dbl
  rd "3" = Just Triple
  rd "4" = Just Aromatic
  rd "5" = Just SngOrDbl
  rd "6" = Just SngOrAromatic
  rd "7" = Just DblOrAromatic
  rd "8" = Just AnyBond
  rd _   = Nothing

  wt : BondType -> String
  wt Single        = "1"
  wt Dbl           = "2"
  wt Triple        = "3"
  wt Aromatic      = "4"
  wt SngOrDbl      = "5"
  wt SngOrAromatic = "6"
  wt DblOrAromatic = "7"
  wt AnyBond       = "8"

  export %hint %inline
  readImpl : Read BondType
  readImpl = mkRead rd "BondType"

  export %hint %inline
  writeImpl : Write BondType
  writeImpl = MkWrite wt

------------------------------
-- BondStereo

||| Stereoinformation represented in molfiles
public export
data BondStereo = NoBondStereo | Up | CisOrTrans | UpOrDown | Down

%runElab derive "BondStereo" [Generic,Meta,Eq,Show]

namespace BondStereo
  rd : String -> Maybe BondStereo
  rd "0" = Just NoBondStereo
  rd "1" = Just Up
  rd "3" = Just CisOrTrans
  rd "4" = Just UpOrDown
  rd "6" = Just Down
  rd _   = Nothing

  wt : BondStereo -> String
  wt NoBondStereo = "0"
  wt Up           = "1"
  wt CisOrTrans   = "3"
  wt UpOrDown     = "4"
  wt Down         = "6"

  export %hint %inline
  readImpl : Read BondStereo
  readImpl = mkRead rd "BondStereo"

  export %hint %inline
  writeImpl : Write BondStereo
  writeImpl = MkWrite wt

------------------------------
-- BondTopo

||| Bond topology encoded in CTAB V2000
public export
data BondTopo = AnyTopology | Ring | Chain

%runElab derive "BondTopo" [Generic,Meta,Eq,Show]

namespace BondTopo
  rd : String -> Maybe BondTopo
  rd "0" = Just AnyTopology
  rd "1" = Just Ring
  rd "2" = Just Chain
  rd _   = Nothing

  wt : BondTopo -> String
  wt AnyTopology = "0"
  wt Ring        = "1"
  wt Chain       = "2"

  export %hint %inline
  readImpl : Read BondTopo
  readImpl = mkRead rd "BondTopo"

  export %hint %inline
  writeImpl : Write BondTopo
  writeImpl = MkWrite wt

------------------------------
-- ReactingCenterStatus

public export
data ReactingCenterStatus =
    Unmarked
  | NotACenter      -- -1
  | Center          -- 1
  | NoChange        -- 2
  | BondMadeBroken  -- 4
  | BondOrderChange -- 8
  | BondMBAndOC     -- 12
  | CenterBMB       -- 5
  | CenterBOC       -- 9
  | CenterBMBAndOC  -- 13

namespace ReactingCenterStatus
  rd : String -> Maybe ReactingCenterStatus
  rd "0"  = Just Unmarked
  rd "-1" = Just NotACenter
  rd "1"  = Just Center
  rd "2"  = Just NoChange
  rd "4"  = Just BondMadeBroken
  rd "8"  = Just BondOrderChange
  rd "12" = Just BondMBAndOC
  rd "5"  = Just CenterBMB
  rd "9"  = Just CenterBOC
  rd "13" = Just CenterBMBAndOC
  rd _    = Nothing

  wt : ReactingCenterStatus -> String
  wt Unmarked        = "0"
  wt NotACenter      = "-1"
  wt Center          = "1"
  wt NoChange        = "2"
  wt BondMadeBroken  = "4"
  wt BondOrderChange = "8"
  wt BondMBAndOC     = "12"
  wt CenterBMB       = "5"
  wt CenterBOC       = "9"
  wt CenterBMBAndOC  = "13"

  export %hint %inline
  readImpl : Read ReactingCenterStatus
  readImpl = mkRead rd "ReactingCenterStatus"

  export %hint %inline
  writeImpl : Write ReactingCenterStatus
  writeImpl = MkWrite wt

%runElab derive "ReactingCenterStatus" [Generic,Meta,Eq,Show]

public export
record Bond where
  constructor MkBond
  atom1                : AtomRef
  atom2                : AtomRef
  type                 : BondType
  stereo               : BondStereo
  topology             : BondTopo
  reactingCenterStatus : ReactingCenterStatus

%runElab derive "Bond" [Generic,Meta,Eq,Show]

--------------------------------------------------------------------------------
--          Properties
--------------------------------------------------------------------------------

------------------------------
-- N8

public export
record N8 where
  constructor MkN8
  value : Bits8
  0 prf : So (1 <= value && value <= 8)

%runElab rwNat "N8" `(Bits8)

------------------------------
-- Radical

public export
data Radical = NoRadical | Singlet | Doublet | Triplet

%runElab derive "Radical" [Generic,Meta,Show,Eq,Ord]

namespace Radical
  rd : String -> Maybe Radical
  rd "0" = Just NoRadical
  rd "1" = Just Singlet
  rd "2" = Just Doublet
  rd "3" = Just Triplet
  rd _   = Nothing

  wt : Radical -> String
  wt NoRadical = "0"
  wt Singlet   = "1"
  wt Doublet   = "2"
  wt Triplet   = "3"

  export %hint %inline
  readImpl : Read Radical
  readImpl = mkRead rd "Radical"

  export %hint %inline
  writeImpl : Write Radical
  writeImpl = MkWrite wt

------------------------------
-- Property

public export
data Property : Type where
  Chg : (c : N8) -> (pairs : Vect (cast c.value) (AtomRef,Charge)) -> Property
  Iso : (c : N8) -> (pairs : Vect (cast c.value) (AtomRef,MassNr)) -> Property
  Rad : (c : N8) -> (pairs : Vect (cast c.value) (AtomRef,Radical)) -> Property

public export
Eq Property where
  Chg c1 ps1 == Chg c2 ps2 = c1 == c2 && toList ps1 == toList ps2
  Iso c1 ps1 == Iso c2 ps2 = c1 == c2 && toList ps1 == toList ps2
  Rad c1 ps1 == Rad c2 ps2 = c1 == c2 && toList ps1 == toList ps2
  _          == _          = False

public export
Show Property where
  showPrec p (Chg c pairs) = showCon p "Chg" $ showArg c ++ showArg pairs
  showPrec p (Iso c pairs) = showCon p "Iso" $ showArg c ++ showArg pairs
  showPrec p (Rad c pairs) = showCon p "Rad" $ showArg c ++ showArg pairs

wpair : (a -> String) -> (AtomRef,a) -> String
wpair w (ar,va) = padLeft 4 ' ' (write ar) ++ padLeft 4 ' ' (w va)

writeN8 : (c : N8) -> Vect (cast c.value) (AtomRef,a) -> (a -> String) -> String
writeN8 c ps wa = padLeft 3 ' ' (write c) ++ foldMap (wpair wa) ps

rpairs : {n : _} -> Read a => String -> Either String (Vect n (AtomRef,a))
rpairs s = go n 9
  where go : (k : Nat) -> (pos : Int) -> Either String (Vect k (AtomRef, a))
        go 0     pos = if cast pos == length s then Right [] else Left "Unexpected end of line"
        go (S k) pos = do
          ar <- readE {a = AtomRef} . ltrim $ strSubstr pos 4 s
          va <- readE {a} . ltrim $ strSubstr (pos + 4) 4 s
          t  <- go k $ pos + 8
          pure $ (ar,va) :: t

readN8 :  Read a
       => (f : (c : N8) -> Vect (cast c.value) (AtomRef,a) -> b)
       -> String
       -> Either String b
readN8 f s = do
  c  <- readE {a = N8} . ltrim $ strSubstr 6 3 s
  ps <- rpairs s
  pure $ f c ps

namespace Property
  wt : Property -> String
  wt (Chg c pairs) = "M  CHG" ++ writeN8 c pairs write
  wt (Iso c pairs) = "M  ISO" ++ writeN8 c pairs write
  wt (Rad c pairs) = "M  RAD" ++ writeN8 c pairs write

  rd : String -> Either String Property
  rd s = case strSubstr 0 6 s of
    "M  CHG" => readN8 Chg s
    "M  ISO" => readN8 Iso s
    "M  RAD" => readN8 Rad s
    s        => Left $ #"Not a valid Property: \#{s}"#

  export %hint %inline
  readImpl : Read Property
  readImpl = mkReadE rd

  export %hint %inline
  writeImpl : Write Property
  writeImpl = MkWrite wt

--------------------------------------------------------------------------------
--          MolFile
--------------------------------------------------------------------------------

public export
record MolFile where
  constructor MkMolFile
  name    : MolLine
  info    : MolLine
  comment : MolLine
  counts  : Counts
  atoms   : Vect (cast counts.atoms.value) Atom
  bonds   : Vect (cast counts.bonds.value) Bond
  props   : List Property

public export
Eq MolFile where
  MkMolFile n1 i1 c1 cs1 as1 bs1 ps1 == MkMolFile n2 i2 c2 cs2 as2 bs2 ps2 =
    n1 == n2 && i1 == i2 && c1 == c2 && cs1 == cs2 &&
    toList as1 == toList as2 && toList bs1 == toList bs2 && ps1 == ps2

export
Show MolFile where
  showPrec p (MkMolFile n i c cs as bs ps) =
    showCon p "MkMolFile" $  showArg n ++ showArg i ++ showArg c ++ showArg cs
                          ++ showArg as ++ showArg bs ++ showArg ps
