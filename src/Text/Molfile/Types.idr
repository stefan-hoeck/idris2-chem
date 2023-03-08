||| Some of the refined types in here should probably
||| go to their own dedicated module
module Text.Molfile.Types

import Chem
import Decidable.HDec.Integer
import Data.Nat
import Data.String
import Data.Vect
import Derive.Prelude
import Derive.Refined
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

public export
0 IsMolLine : String -> Type
IsMolLine = StrLen (<= 80) && Str (All Printable)

||| An uninterpreted line in a v2000 mol file
public export
record MolLine where
  constructor MkMolLine
  value : String
  {auto 0 prf : IsMolLine value}

export %inline
Interpolation MolLine where
  interpolate = value

namespace MolLine
  %runElab derive "MolLine" [Show,Eq,Ord,RefinedString]

-- namespace MolLine
--   public export
--   readMsg : String -> Either String MolLine
--   readMsg = mkReadE refine "MolLine"

--------------------------------------------------------------------------------
--          Counts Line
--------------------------------------------------------------------------------

------------------------------
-- MolVersion

public export
data MolVersion = V2000 | V3000

export %inline
Interpolation MolVersion where
  interpolate V2000 = "v2000"
  interpolate V3000 = "v3000"

%runElab derive "MolVersion" [Eq,Ord,Show]

------------------------------
-- ChiralFlag

public export
data ChiralFlag = NonChiral | Chiral

%runElab derive "ChiralFlag" [Eq,Ord,Show]

export %inline
Interpolation ChiralFlag where
  interpolate NonChiral = "0"
  interpolate Chiral    = "1"

public export
record Counts where
  constructor MkCounts
  atoms     : Nat
  bonds     : Nat
  chiral    : ChiralFlag
  version   : MolVersion

%runElab derive "Counts" [Eq,Show]

--------------------------------------------------------------------------------
--          Atoms
--------------------------------------------------------------------------------

------------------------------
-- AtomSymbol

||| Ast    -> Asterisk
||| RSharp -> R# (RGroupLabel)
public export
data AtomSymbol = L | A | Q | Ast | LP | RSharp | El Elem

export
Interpolation AtomSymbol where
  interpolate (El x) = symbol x
  interpolate L      = "L"
  interpolate A      = "A"
  interpolate Q      = "Q"
  interpolate Ast    = "*"
  interpolate LP     = "LP"
  interpolate RSharp = "R#"

%runElab derive "AtomSymbol" [Show, Eq]

-- namespace AtomSymbol
--   public export
--   read : String -> Maybe AtomSymbol
--   read s = case fromSymbol s of
--     -- choosing the right order here makes this
--     -- considerably faster in the most common case
--     Just el => Just (El el)
--     Nothing => case s of
--       "L"  => Just L
--       "A"  => Just A
--       "Q"  => Just Q
--       "*"  => Just Ast
--       "LP" => Just LP
--       "R#" => Just RSharp
--       _    => Nothing
--
--   public export
--   readMsg : String -> Either String AtomSymbol
--   readMsg = mkReadE read "AtomSymbol"
--
-- ------------------------------
-- -- StereoParity

||| Atom Stereo parity encoded in V2000 CTAB
public export
data StereoParity =
    NoStereo
  | OddStereo
  | EvenStereo
  | AnyStereo

%runElab derive "StereoParity" [Eq,Ord,Show]

export %inline
Interpolation StereoParity where
  interpolate NoStereo   = "0"
  interpolate OddStereo  = "1"
  interpolate EvenStereo = "2"
  interpolate AnyStereo  = "3"

-- namespace StereoParity
--   public export
--   read : String -> Maybe StereoParity
--   read "0" = Just NoStereo
--   read "1" = Just OddStereo
--   read "2" = Just EvenStereo
--   read "3" = Just AnyStereo
--   read _   = Nothing
--
--
--   public export
--   readMsg : String -> Either String StereoParity
--   readMsg = mkReadE read "StereoParity"

------------------------------
-- StereoCareBox

||| Stereo care box encoded in V2000
public export
data  StereoCareBox = IgnoreStereo | MatchStereo

export %inline
Interpolation StereoCareBox where
  interpolate IgnoreStereo = "0"
  interpolate MatchStereo  = "1"

%runElab derive "StereoCareBox" [Eq,Ord,Show]
--
-- namespace StereoCareBox
--   public export
--   read : String -> Maybe StereoCareBox
--   read "0" = Just IgnoreStereo
--   read "1" = Just MatchStereo
--   read _   = Nothing
--
--
--   public export
--   readMsg : String -> Either String StereoCareBox
--   readMsg = mkReadE read "StereoCareBox"
--
------------------------------
-- Valence

||| Valence of atoms
|||
||| NOTE: In a V2000 molfile 15 is zero valence,
||| while 0 means no marking
public export
record Valence where
  constructor MkValence
  value : Bits8
  {auto 0 prf : value <= 15}

export %inline
Interpolation Valence where
  interpolate = show . value

namespace Valence
  %runElab derive "Valence" [Show,Eq,Ord,RefinedInteger]

-- namespace Valence
--   public export
--   read : String -> Maybe Valence
--   read "0"  = Just NoValence
--   read "15" = Just $ MkValence 0 Oh
--   read s    = readInt s >>= refineSo MkValence
--
--   public export
--   readMsg : String -> Either String Valence
--   readMsg = mkReadE read "Valence"
--
------------------------------
-- H0Designator

||| Reduntant hydrogen count flag
public export
data H0Designator = H0NotSpecified | NoHAllowed

export %inline
Interpolation H0Designator where
  interpolate H0NotSpecified = "0"
  interpolate NoHAllowed     = "1"

%runElab derive "H0Designator" [Eq,Ord,Show]
--
-- namespace H0Designator
--   public export
--   read : String -> Maybe H0Designator
--   read "0" = Just H0NotSpecified
--   read "1" = Just NoHAllowed
--   read _   = Nothing
--
--   public export
--   readMsg : String -> Either String H0Designator
--   readMsg = mkReadE read "H0Designator"
--
------------------------------
-- AtomCharge

||| 0 if uncharged, 1-3 if positive, 4 if doublet radical
||| 5-7 if negative
public export
record AtomCharge where
  constructor MkAtomCharge
  value : Bits8
  {auto 0 prf : value < 8}

export %inline
Interpolation AtomCharge where
  interpolate = show . value

%runElab derive "AtomCharge" [Show,Eq,Ord,RefinedInteger]

-- namespace AtomCharge
--   public export
--   read : String -> Maybe AtomCharge
--   read "0" = Just $ MkCharge 0 Oh
--   read "1" = Just $ MkCharge 3 Oh
--   read "2" = Just $ MkCharge 2 Oh
--   read "3" = Just $ MkCharge 1 Oh
--   read "4" = Just $ DoubletRadical
--   read "5" = Just $ MkCharge (-1) Oh
--   read "6" = Just $ MkCharge (-2) Oh
--   read "7" = Just $ MkCharge (-3) Oh
--   read _   = Nothing
--
--   public export
--   readMsg : String -> Either String AtomCharge
--   readMsg = mkReadE read "AtomCharge"
--
--
------------------------------
-- InvRetentionFlag

public export
data InvRetentionFlag =
  InvNotApplied | ConfigInverted | ConfigRetained

export %inline
Interpolation InvRetentionFlag where
  interpolate InvNotApplied  = "0"
  interpolate ConfigInverted = "1"
  interpolate ConfigRetained = "2"

%runElab derive "InvRetentionFlag" [Eq,Ord,Show]

-- namespace InvRetentionFlag
--   public export
--   read : String -> Maybe InvRetentionFlag
--   read "0" = Just InvNotApplied
--   read "1" = Just ConfigInverted
--   read "2" = Just ConfigRetained
--   read _   = Nothing
--
--
--   public export
--   readMsg : String -> Either String InvRetentionFlag
--   readMsg = mkReadE read "InvRetentionFlag"
--
------------------------------
-- ExactChangeFlag

public export
data ExactChangeFlag = ChangeNotApplied | ExactChange

export %inline
Interpolation ExactChangeFlag where
  interpolate ChangeNotApplied  = "0"
  interpolate ExactChange       = "1"

%runElab derive "ExactChangeFlag" [Eq,Ord,Show]

-- namespace ExactChangeFlag
--   public export
--   read : String -> Maybe ExactChangeFlag
--   read "0" = Just ChangeNotApplied
--   read "1" = Just ExactChange
--   read _   = Nothing
--
--   public export
--   readMsg : String -> Either String ExactChangeFlag
--   readMsg = mkReadE read "ExactChangeFlag"
--
------------------------------
-- MassDiff

||| Mass difference encoded in V2000 CTAB
public export
record MassDiff where
  constructor MkMassDiff
  value : Int8
  {auto 0 prf : FromTo (-3) 4 value}

export %inline
Interpolation MassDiff where
  interpolate = show . value

namespace MassDiff
  %runElab derive "MassDiff" [Show,Eq,Ord,RefinedInteger]

------------------------------
-- Hydrogen Count

||| HCount plus 1: 0 means "not explicitly given"
||| 1 means "explicitly 0" and so on.
public export
record HydrogenCount where
  constructor MkHC
  value : Bits8
  {auto 0 prf : value <= 5}

export %inline
Interpolation HydrogenCount where
  interpolate = show . value

namespace HydrogenCount
  %runElab derive "HydrogenCount" [Show,Eq,Ord,RefinedInteger]

-- namespace HydrogenCount
--   public export
--   read : String -> Maybe HydrogenCount
--   read "0" = Just $ NoHC
--   read s   = readInt s >>= refineSo HC . (\x => x - 1)
--
--   public export
--   readMsg : String -> Either String HydrogenCount
--   readMsg = mkReadE read "HydrogenCount"

------------------------------
-- AtomRef

||| Restricted to a max of three digit unsigned numbers
public export
record AtomRef where
  constructor MkAtomRef
  value : Bits32
  {auto 0 prf : value <= 999}

export %inline
Interpolation AtomRef where
  interpolate = show . value

namespace AtomRef
  %runElab derive "AtomRef" [Show,Eq,Ord,RefinedInteger]

public export
0 Coordinate : Type
Coordinate = Float (-9999) 99999 4

||| Data on a single V2000 Atom Line
public export
record Atom where
  constructor MkAtom
  position         : Vect 3 Coordinate
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

%runElab derive "Atom" [Eq,Show]

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

export %inline
Interpolation BondType where
  interpolate Single        = "1"
  interpolate Dbl           = "2"
  interpolate Triple        = "3"
  interpolate Aromatic      = "4"
  interpolate SngOrDbl      = "5"
  interpolate SngOrAromatic = "6"
  interpolate DblOrAromatic = "7"
  interpolate AnyBond       = "8"

%runElab derive "BondType" [Eq,Show,Ord]

-- namespace BondType
--   public export
--   read : String -> Maybe BondType
--   read "1" = Just Single
--   read "2" = Just Dbl
--   read "3" = Just Triple
--   read "4" = Just Aromatic
--   read "5" = Just SngOrDbl
--   read "6" = Just SngOrAromatic
--   read "7" = Just DblOrAromatic
--   read "8" = Just AnyBond
--   read _   = Nothing
--
--
--   public export
--   readMsg : String -> Either String BondType
--   readMsg = mkReadE read "BondType"
--
------------------------------
-- BondStereo

||| Stereoinformation represented in molfiles
public export
data BondStereo = NoBondStereo | Up | CisOrTrans | UpOrDown | Down

export %inline
Interpolation BondStereo where
  interpolate NoBondStereo = "0"
  interpolate Up           = "1"
  interpolate CisOrTrans   = "3"
  interpolate UpOrDown     = "4"
  interpolate Down         = "6"

%runElab derive "BondStereo" [Ord, Eq, Show]

-- namespace BondStereo
--   public export
--   read : String -> Maybe BondStereo
--   read "0" = Just NoBondStereo
--   read "1" = Just Up
--   read "3" = Just CisOrTrans
--   read "4" = Just UpOrDown
--   read "6" = Just Down
--   read _   = Nothing
--
--   public export
--   readMsg : String -> Either String BondStereo
--   readMsg = mkReadE read "BondStereo"
--
------------------------------
-- BondTopo

||| Bond topology encoded in CTAB V2000
public export
data BondTopo = AnyTopology | Ring | Chain

export %inline
Interpolation BondTopo where
  interpolate AnyTopology = "0"
  interpolate Ring        = "1"
  interpolate Chain       = "2"

%runElab derive "BondTopo" [Eq,Show,Ord]

-- namespace BondTopo
--   public export
--   read : String -> Maybe BondTopo
--   read "0" = Just AnyTopology
--   read "1" = Just Ring
--   read "2" = Just Chain
--   read _   = Nothing
--
--
--   public export
--   readMsg : String -> Either String BondTopo
--   readMsg = mkReadE read "BondTopo"
--
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

%runElab derive "ReactingCenterStatus" [Eq,Show]

export %inline
Interpolation ReactingCenterStatus where
  interpolate Unmarked        = "0"
  interpolate NotACenter      = "-1"
  interpolate Center          = "1"
  interpolate NoChange        = "2"
  interpolate BondMadeBroken  = "4"
  interpolate BondOrderChange = "8"
  interpolate BondMBAndOC     = "12"
  interpolate CenterBMB       = "5"
  interpolate CenterBOC       = "9"
  interpolate CenterBMBAndOC  = "13"

-- namespace ReactingCenterStatus
--   public export
--   read : String -> Maybe ReactingCenterStatus
--   read "0"  = Just Unmarked
--   read "-1" = Just NotACenter
--   read "1"  = Just Center
--   read "2"  = Just NoChange
--   read "4"  = Just BondMadeBroken
--   read "8"  = Just BondOrderChange
--   read "12" = Just BondMBAndOC
--   read "5"  = Just CenterBMB
--   read "9"  = Just CenterBOC
--   read "13" = Just CenterBMBAndOC
--   read _    = Nothing
--
--   public export
--   readMsg : String -> Either String ReactingCenterStatus
--   readMsg = mkReadE read "ReactingCenterStatus"

public export
record Bond where
  constructor MkBond
  atom1                : AtomRef
  atom2                : AtomRef
  type                 : BondType
  stereo               : BondStereo
  topology             : BondTopo
  reactingCenterStatus : ReactingCenterStatus

%runElab derive "Bond" [Eq,Show]

--------------------------------------------------------------------------------
--          Properties
--------------------------------------------------------------------------------

------------------------------
-- N8

public export
record N8 where
  constructor MkN8
  value : Nat
  {auto 0 prf : ((1 `LTE`) && (`LTE` 8)) value}

export %inline
Interpolation N8 where
  interpolate = show . value

namespace N8
  %runElab derive "N8" [Show,Eq,Ord,RefinedInteger]

------------------------------
-- Radical

public export
data Radical = NoRadical | Singlet | Doublet | Triplet

export %inline
Interpolation Radical where
  interpolate NoRadical = "0"
  interpolate Singlet   = "1"
  interpolate Doublet   = "2"
  interpolate Triplet   = "3"

%runElab derive "Radical" [Show,Eq,Ord]
--
-- namespace Radical
--   public export
--   read : String -> Maybe Radical
--   read "0" = Just NoRadical
--   read "1" = Just Singlet
--   read "2" = Just Doublet
--   read "3" = Just Triplet
--   read _   = Nothing
--
--   public export
--   readMsg : String -> Either String Radical
--   readMsg = mkReadE read "Radical"
--
------------------------------
-- Property

public export
data Property : Type where
  Chg : (n : N8) -> Vect n.value (AtomRef,Charge)  -> Property
  Iso : (n : N8) -> Vect n.value (AtomRef,MassNr)  -> Property
  Rad : (n : N8) -> Vect n.value (AtomRef,Radical) -> Property

%runElab derive "Property" [Show]

--   export %inline
--   Interpolation Property
--     interpolate (Chg c pairs) = "M  CHG" ++ writeN8 c pairs write
--     interpolate (Iso c pairs) = "M  ISO" ++ writeN8 c pairs write
--     interpolate (Rad c pairs) = "M  RAD" ++ writeN8 c pairs write

public export
Eq Property where
  Chg c1 ps1 == Chg c2 ps2 = c1 == c2 && toList ps1 == toList ps2
  Iso c1 ps1 == Iso c2 ps2 = c1 == c2 && toList ps1 == toList ps2
  Rad c1 ps1 == Rad c2 ps2 = c1 == c2 && toList ps1 == toList ps2
  _          == _          = False

-- wpair : (a -> String) -> (AtomRef,a) -> String
-- wpair w (ar,va) = padLeft 4 ' ' (write ar) ++ padLeft 4 ' ' (w va)
--
-- writeN8 : (c : N8) -> Vect (cast c.value) (AtomRef,a) -> (a -> String) -> String
-- writeN8 c ps wa = padLeft 3 ' ' (write c) ++ foldMap (wpair wa) ps
--
-- rpairs :  {n : _}
--        -> (re : String -> Either String a)
--        -> String
--        -> Either String (Vect n (AtomRef,a))
-- rpairs re s = go n 9
--   where go : (k : Nat) -> (pos : Int) -> Either String (Vect k (AtomRef, a))
--         go 0     pos = if cast pos == length s then Right [] else Left "Unexpected end of line"
--         go (S k) pos = do
--           ar <- readMsg . ltrim $ strSubstr pos 4 s
--           va <- re . ltrim $ strSubstr (pos + 4) 4 s
--           t  <- go k $ pos + 8
--           pure $ (ar,va) :: t
--
-- readN8 :  (re : String -> Either String a)
--        -> (f : (c : N8) -> Vect (cast c.value) (AtomRef,a) -> b)
--        -> String
--        -> Either String b
-- readN8 re f s = do
--   c  <- readMsg . ltrim $ strSubstr 6 3 s
--   ps <- rpairs re s
--   pure $ f c ps
--
-- namespace Property
--
--   public export
--   readMsg : String -> Either String Property
--   readMsg s = case strSubstr 0 6 s of
--     "M  CHG" => readN8 readMsg Chg s
--     "M  ISO" => readN8 readMsg Iso s
--     "M  RAD" => readN8 readMsg Rad s
--     s        => Left $ #"Not a valid Property: \#{s}"#
--
-- --------------------------------------------------------------------------------
-- --          MolFile
-- --------------------------------------------------------------------------------
--
-- public export
-- record MolFile where
--   constructor MkMolFile
--   name    : MolLine
--   info    : MolLine
--   comment : MolLine
--   counts  : Counts
--   atoms   : Vect (cast counts.atoms.value) Atom
--   bonds   : Vect (cast counts.bonds.value) Bond
--   props   : List Property
--
-- %runElab derive "MolFile" [Show]
--
-- public export
-- Eq MolFile where
--   MkMolFile n1 i1 c1 cs1 as1 bs1 ps1 == MkMolFile n2 i2 c2 cs2 as2 bs2 ps2 =
--     n1 == n2 && i1 == i2 && c1 == c2 && cs1 == cs2 &&
--     toList as1 == toList as2 && toList bs1 == toList bs2 && ps1 == ps2
