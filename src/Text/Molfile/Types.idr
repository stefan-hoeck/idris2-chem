||| Some of the refined types in here should probably
||| go to their own dedicated module
module Text.Molfile.Types

import Derive.Prelude
import Derive.Refined
import public Data.Refined.String
import public Data.Refined.Integer
import public Chem
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
  interpolate V2000 = "V2000"
  interpolate V3000 = "V3000"

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

public export %inline
Cast Elem AtomSymbol where cast = El


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

export %inline
Cast Coordinate Double where
  cast x = cast x.value / cast Precision

disp : Integer -> String
disp i =
  show (i `div` Precision) ++ "." ++ padLeft 4 '0' (show (i `mod` Precision))

export
Interpolation Coordinate where
  interpolate s = padLeft 10 ' ' $
    if s.value < 0 then "-" ++ disp (abs s.value) else disp s.value

namespace Coordinate
  %runElab derive "Coordinate" [Show,Eq,Ord,RefinedInteger]

||| Convenience alias for `Vect 3 Coordinates`
public export
0 Coordinates : Type
Coordinates = Vect 3 Coordinate

public export
record AtomGroup where
  constructor G
  nr    : Nat
  lbl   : String

%runElab derive "AtomGroup" [Show,Eq]

||| Regular atom loaded from a .mol file.
|||
||| Note: .mol files support additional atom symbols
||| (for instance, for queries), but for real-world molecules,
||| this is the type to use.
|||
||| The type parameters are used for implicit hydrogens and atom types,
||| which are `()` for freshly loaded `MolAtom`s but more specific after
||| atom type perception.
public export
0 MolAtom' : (h,t,c : Type) -> Type
MolAtom' h t c = Atom Isotope Charge Coordinates Radical h t c (Maybe AtomGroup)

||| Regular atom loaded from a .mol file.
|||
||| Note: .mol files support additional atom symbols
||| (for instance, for queries), but for real-world molecules,
||| this is the type to use.
public export
0 MolAtom : Type
MolAtom = MolAtom' () () ()

||| .mol-file atom with perceived atom type and computed
||| implicit hydrogen count
public export
0 MolAtomAT : Type
MolAtomAT = MolAtom' HCount AtomType ()

public export
Cast Elem MolAtom where
  cast el = MkAtom (cast el) 0 [0,0,0] NoRadical () () () Nothing

--------------------------------------------------------------------------------
--          Bonds
--------------------------------------------------------------------------------

------------------------------
-- BondType

public export
data QueryBondType : Type where
  BT            : BondOrder -> QueryBondType
  Arom          : QueryBondType
  SngOrDbl      : QueryBondType
  SngOrAromatic : QueryBondType
  DblOrAromatic : QueryBondType
  AnyBond       : QueryBondType

export %inline
Interpolation QueryBondType where
  interpolate (BT b)        = interpolate b
  interpolate Arom          = "4"
  interpolate SngOrDbl      = "5"
  interpolate SngOrAromatic = "6"
  interpolate DblOrAromatic = "7"
  interpolate AnyBond       = "8"

%runElab derive "QueryBondType" [Eq,Show,Ord]

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
record MolBond where
  constructor MkBond
  ||| Flag indicating whether the bond goes from the
  ||| atom with the smaller index to the one with the larger index
  ||| or vice versa.
  |||
  ||| We need this to figure out in which direction wedged bonds should
  ||| point.
  firstSmaller : Bool
  type         : BondOrder
  stereo       : BondStereo

%runElab derive "MolBond" [Eq,Show]

export %inline
Cast MolBond BondOrder where cast = type

export %inline
Cast BondOrder MolBond where cast t = MkBond False t NoBondStereo

export %inline
Cast MolBond BondStereo where cast = stereo

export %inline
Cast BondStereo MolBond where cast = MkBond False Single

--------------------------------------------------------------------------------
--          MolFile
--------------------------------------------------------------------------------

public export
data SGroupType = SUP | Other

%runElab derive "SGroupType" [Show,Eq]

public export
0 MolGraph' : (h,t,c : Type) -> Type
MolGraph' h t c = Graph MolBond (MolAtom' h t c)

public export
0 MolGraph : Type
MolGraph = MolGraph' () () ()

||| .mol-file graph with perceived atom types and computed
||| implicit hydrogen counts
public export
0 MolGraphAT : Type
MolGraphAT = MolGraph' HCount AtomType ()

public export
record Molfile' (h,t,c : Type) where
  constructor MkMolfile
  name    : MolLine
  info    : MolLine
  comment : MolLine
  graph   : MolGraph' h t c

%runElab derive "Molfile'" [Show,Eq]

export %inline
emptyMolFile : Molfile' h t c
emptyMolFile = MkMolfile "" "" "" (G 0 empty)

public export
0 Molfile : Type
Molfile = Molfile' () () ()

public export
0 MolfileAT : Type
MolfileAT = Molfile' HCount AtomType ()
