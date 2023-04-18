||| Some of the refined types in here should probably
||| go to their own dedicated module
module Text.Molfile.Types

import Derive.Prelude
import Derive.Refined
import public Data.Refined.String
import public Data.Refined.Integer
import public Chem
import public Data.List.Quantifiers
import public Data.Nat
import public Data.String
import public Data.Vect

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
IsMolLine = Len (<= 80) && Str (All Printable)

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


------------------------------
-- StereoParity

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

||| We encode coordinates as a sufficiently precise integer
||| to prevent loss of precision during parsing.
public export
record Coordinate where
  constructor MkCoordinate
  value : Integer
  {auto 0 prf : FromTo (-9999_9999) 99999_9999 value}

public export
Precision : Integer
Precision = 10000

disp : Integer -> String
disp i =
  show (i `div` Precision) ++ "." ++ padLeft 4 '0' (show (i `mod` Precision))

export
Interpolation Coordinate where
  interpolate s = padLeft 10 ' ' $
    if s.value < 0 then "-" ++ disp (abs s.value) else disp s.value

namespace Coordinate
  %runElab derive "Coordinate" [Show,Eq,Ord,RefinedInteger]

||| Data on a single V2000 Atom Line
public export
record Atom where
  constructor MkAtom
  position         : Vect 3 Coordinate
  symbol           : AtomSymbol
  massNr           : Maybe MassNr
  charge           : Charge
  stereoParity     : StereoParity
  hydrogenCount    : HydrogenCount
  stereoCareBox    : StereoCareBox
  valence          : Valence
  h0designator     : H0Designator

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

public export
record Bond where
  constructor MkBond
  fst                  : Node
  snd                  : Node
  type                 : BondType
  stereo               : BondStereo
  topology             : BondTopo

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

--------------------------------------------------------------------------------
--          MolFile
--------------------------------------------------------------------------------

public export
record MolFile where
  constructor MkMolFile
  name    : MolLine
  info    : MolLine
  comment : MolLine
  graph   : Graph Bond Atom

%runElab derive "MolFile" [Show,Eq]
