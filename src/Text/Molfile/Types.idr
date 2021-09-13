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

--------------------------------------------------------------------------------
--          Counts Line
--------------------------------------------------------------------------------

------------------------------
-- MolVersion

public export
data MolVersion = V2000 | V3000

%runElab derive "MolVersion" [Generic,Meta,Eq,Ord,Show]

namespace MolVersion
  public export
  read : String -> Maybe MolVersion
  read "v2000" = Just V2000
  read "v3000" = Just V3000
  read "V2000" = Just V2000
  read "V3000" = Just V3000
  read _       = Nothing

  public export
  write : MolVersion -> String
  write V2000 = "v2000"
  write V3000 = "v3000"

------------------------------
-- ChiralFlag

public export
data ChiralFlag = NonChiral | Chiral

%runElab derive "ChiralFlag" [Generic,Meta,Eq,Ord,Show]

namespace ChiralFlag
  public export
  read : String -> Maybe ChiralFlag
  read "0" = Just NonChiral
  read "1" = Just Chiral
  read _   = Nothing

  public export
  write : ChiralFlag -> String
  write NonChiral = "0"
  write Chiral    = "1"


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
  public export
  read : String -> Maybe AtomSymbol
  read "L"  = Just L
  read "A"  = Just A
  read "Q"  = Just Q
  read "*"  = Just Ast
  read "LP" = Just LP
  read "R#" = Just RSharp
  read s    = El <$> read s

  public export %inline
  write : AtomSymbol -> String
  write = show

  public export
  fromString :  (s : String)
             -> {auto 0 _ : IsJust (AtomSymbol.read s)}
             -> AtomSymbol
  fromString s = fromJust $ read s

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
  public export
  read : String -> Maybe StereoParity
  read "0" = Just NoStereo
  read "1" = Just OddStereo
  read "2" = Just EvenStereo
  read "3" = Just AnyStereo
  read _   = Nothing

  public export
  write : StereoParity -> String
  write NoStereo   = "0"
  write OddStereo  = "1"
  write EvenStereo = "2"
  write AnyStereo  = "3"

------------------------------
-- StereoCareBox

||| Stereo care box encoded in V2000
public export
data  StereoCareBox = IgnoreStereo | MatchStereo

%runElab derive "StereoCareBox" [Generic,Meta,Eq,Ord,Show]

namespace StereoCareBox
  public export
  read : String -> Maybe StereoCareBox
  read "0" = Just IgnoreStereo
  read "1" = Just MatchStereo
  read _   = Nothing

  public export
  write : StereoCareBox -> String
  write IgnoreStereo = "0"
  write MatchStereo  = "1"

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
  public export
  read : String -> Maybe Valence
  read "0"  = Just NoValence
  read "15" = Just $ MkValence 0 Oh
  read s    = readNat s >>= refineSo MkValence

  public export %inline
  write : Valence -> String
  write NoValence       = "0"
  write (MkValence 0 _) = "15"
  write (MkValence n _) = show n

------------------------------
-- H0Designator

||| Reduntant hydrogen count flag
public export
data H0Designator = H0NotSpecified | NoHAllowed

%runElab derive "H0Designator" [Generic,Meta,Eq,Ord,Show]

namespace H0Designator
  public export
  read : String -> Maybe H0Designator
  read "0" = Just H0NotSpecified
  read "1" = Just NoHAllowed
  read _   = Nothing

  public export
  write : H0Designator -> String
  write H0NotSpecified = "0"
  write NoHAllowed     = "1"

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
  public export
  read : String -> Maybe AtomCharge
  read "0" = Just $ MkCharge 0 Oh
  read "1" = Just $ MkCharge 3 Oh
  read "2" = Just $ MkCharge 2 Oh
  read "3" = Just $ MkCharge 1 Oh
  read "4" = Just $ DoubletRadical
  read "5" = Just $ MkCharge (-1) Oh
  read "6" = Just $ MkCharge (-2) Oh
  read "7" = Just $ MkCharge (-3) Oh
  read _   = Nothing

  public export %inline
  write : AtomCharge -> String
  write = show . chargeCode

------------------------------
-- InvRetentionFlag

public export
data InvRetentionFlag = InvNotApplied
                      | ConfigInverted
                      | ConfigRetained

%runElab derive "InvRetentionFlag" [Generic,Meta,Eq,Ord,Show]

namespace InvRetentionFlag
  public export
  read : String -> Maybe InvRetentionFlag
  read "0" = Just InvNotApplied
  read "1" = Just ConfigInverted
  read "2" = Just ConfigRetained
  read _   = Nothing

  public export
  write : InvRetentionFlag -> String
  write InvNotApplied  = "0"
  write ConfigInverted = "1"
  write ConfigRetained = "2"

------------------------------
-- ExactChangeFlag

public export
data ExactChangeFlag = ChangeNotApplied | ExactChange

%runElab derive "ExactChangeFlag" [Generic,Meta,Eq,Ord,Show]

namespace ExactChangeFlag
  public export
  read : String -> Maybe ExactChangeFlag
  read "0" = Just ChangeNotApplied
  read "1" = Just ExactChange
  read _   = Nothing

  public export
  write : ExactChangeFlag -> String
  write ChangeNotApplied  = "0"
  write ExactChange       = "1"

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
  public export
  read : String -> Maybe HydrogenCount
  read "0" = Just $ NoHC
  read s   = readNat s >>= refineSo HC . (\x => x - 1)

  public export %inline
  write : HydrogenCount -> String
  write = show . hcCode

------------------------------
-- AtomRef

||| Restricted to a max of three digit unsigned numbers
public export
record AtomRef where
  constructor MkAtomRef
  value : Bits32
  0 prf : So (1 <= value && value <= 999)

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
  public export
  read : String -> Maybe BondType
  read "1" = Just Single
  read "2" = Just Dbl
  read "3" = Just Triple
  read "4" = Just Aromatic
  read "5" = Just SngOrDbl
  read "6" = Just SngOrAromatic
  read "7" = Just DblOrAromatic
  read "8" = Just AnyBond
  read _   = Nothing

  public export
  write : BondType -> String
  write Single        = "1"
  write Dbl           = "2"
  write Triple        = "3"
  write Aromatic      = "4"
  write SngOrDbl      = "5"
  write SngOrAromatic = "6"
  write DblOrAromatic = "7"
  write AnyBond       = "8"

------------------------------
-- BondStereo

||| Stereoinformation represented in molfiles
public export
data BondStereo = NoBondStereo | Up | CisOrTrans | UpOrDown | Down

%runElab derive "BondStereo" [Generic,Meta,Eq,Show]

namespace BondStereo
  public export
  read : String -> Maybe BondStereo
  read "0" = Just NoBondStereo
  read "1" = Just Up
  read "3" = Just CisOrTrans
  read "4" = Just UpOrDown
  read "6" = Just Down
  read _   = Nothing

  public export
  write : BondStereo -> String
  write NoBondStereo = "0"
  write Up           = "1"
  write CisOrTrans   = "3"
  write UpOrDown     = "4"
  write Down         = "6"

------------------------------
-- BondTopo

||| Bond topology encoded in CTAB V2000
public export
data BondTopo = AnyTopology | Ring | Chain

%runElab derive "BondTopo" [Generic,Meta,Eq,Show]

namespace BondTopo
  public export
  read : String -> Maybe BondTopo
  read "0" = Just AnyTopology
  read "1" = Just Ring
  read "2" = Just Chain
  read _   = Nothing

  public export
  write : BondTopo -> String
  write AnyTopology = "0"
  write Ring        = "1"
  write Chain       = "2"

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
  public export
  read : String -> Maybe ReactingCenterStatus
  read "0"  = Just Unmarked
  read "-1" = Just NotACenter
  read "1"  = Just Center
  read "2"  = Just NoChange
  read "4"  = Just BondMadeBroken
  read "8"  = Just BondOrderChange
  read "12" = Just BondMBAndOC
  read "5"  = Just CenterBMB
  read "9"  = Just CenterBOC
  read "13" = Just CenterBMBAndOC
  read _    = Nothing

  public export
  write : ReactingCenterStatus -> String
  write Unmarked        = "0"
  write NotACenter      = "-1"
  write Center          = "1"
  write NoChange        = "2"
  write BondMadeBroken  = "4"
  write BondOrderChange = "8"
  write BondMBAndOC     = "12"
  write CenterBMB       = "5"
  write CenterBOC       = "9"
  write CenterBMBAndOC  = "13"

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
  public export
  read : String -> Maybe Radical
  read "0" = Just NoRadical
  read "1" = Just Singlet
  read "2" = Just Doublet
  read "3" = Just Triplet
  read _   = Nothing

  public export
  write : Radical -> String
  write NoRadical = "0"
  write Singlet   = "1"
  write Doublet   = "2"
  write Triplet   = "3"

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

rpairs : {n : _} -> (String -> Maybe a) -> String -> Maybe (Vect n (AtomRef,a))
rpairs r s = go n 9
  where go : (k : Nat) -> (pos : Int) -> Maybe (Vect k (AtomRef, a))
        go 0     pos = if cast pos == length s then Just [] else Nothing
        go (S k) pos = do
          ar <- AtomRef.read . ltrim $ strSubstr pos 4 s
          va <- r . ltrim $ strSubstr (pos + 4) 4 s
          t  <- go k $ pos + 8
          pure $ (ar,va) :: t

readN8 :  (f : (c : N8) -> Vect (cast c.value) (AtomRef,a) -> b)
       -> (read : String -> Maybe a)
       -> String
       -> Maybe b
readN8 f read s = do
  c  <- N8.read . ltrim $ strSubstr 6 3 s
  ps <- rpairs read s
  pure $ f c ps

namespace Property
  public export
  write : Property -> String
  write (Chg c pairs) = "M  CHG" ++ writeN8 c pairs write
  write (Iso c pairs) = "M  ISO" ++ writeN8 c pairs write
  write (Rad c pairs) = "M  RAD" ++ writeN8 c pairs write

  public export
  read : String -> Maybe Property
  read s = case strSubstr 0 6 s of
    "M  CHG" => readN8 Chg read s
    "M  ISO" => readN8 Iso read s
    "M  RAD" => readN8 Rad read s
    _        => Nothing

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
