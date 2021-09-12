||| Some of the refined types in here should probably
||| go to their own dedicated module
module Text.Molfile.Types

import Chem.Element

import Data.DPair
import Data.Nat
import Data.String
import Data.Vect

import Generics.Derive

import Data.String

import public Language.Reflection.Refined.Util
import Language.Reflection.Refined

%default total
%language ElabReflection

--------------------------------------------------------------------------------
--          Refined Integers
--------------------------------------------------------------------------------

public export
readNat : Num a => String -> Maybe a
readNat = go 0
  where go : a -> String -> Maybe a
        go res s = case strM s of
          StrNil       => Just res
          StrCons c cs =>
            if isDigit c
               then go (fromInteger (cast (ord c - 48)) + res * 10)
                    (assert_smaller s cs)
               else Nothing

public export
readInt : Num a => Neg a => String -> Maybe a
readInt s = case strM s of
  StrCons '-' t => negate <$> readNat t
  _             => readNat s

public export
readRefinedInt :  {f : a -> Bool}
               -> Num a
               => Neg a
               => String
               -> Maybe (Subset a $ \n => So (f n))
readRefinedInt s =
  readInt s >>= \n =>
    case choose (f n) of
      Left oh => Just $ Element n oh
      Right _ => Nothing

--------------------------------------------------------------------------------
--          Limited Length Strings
--------------------------------------------------------------------------------

public export
record StringN (n : Nat) where
  constructor MkStringN
  value : String
  0 prf : LTE (length value) n

public export
Eq (StringN n) where
  (==) = (==) `on` value

public export
Ord (StringN n) where
  compare = compare `on` value

export
Show (StringN n) where
  show = show . value

namespace StringN
  public export
  refine : {n : _} -> String -> Maybe (StringN n)
  refine s = case isLTE (length s) n of
    Yes prf => Just $ MkStringN s prf
    No _    => Nothing

  public export
  fromString :  {n : _}
             -> (s : String)
             -> {auto 0 _ : IsJust (refine {n} s)}
             -> StringN n
  fromString s = fromJust $ refine s

--------------------------------------------------------------------------------
--          Fixed Width Numbers
--------------------------------------------------------------------------------

||| An unsigned integer limited by an upper bound.
public export
record Digits (n : Bits32) where
  constructor MkDigits
  value : Bits32
  0 prf : So (value < n)

public export
Eq (Digits n) where
  (==) = (==) `on` value

public export
Ord (Digits n) where
  compare = compare `on` value

export
Show (Digits n) where
  show = show . value

namespace Digits
  public export
  refine : {n : _} -> Bits32 -> Maybe (Digits n)
  refine v = case choose (v < n) of
    Left oh => Just $ MkDigits v oh
    Right _ => Nothing

  public export
  fromInteger :  {n : _}
              -> (v : Integer)
              -> {auto 0 _ : IsJust (Digits.refine {n} (cast v)) }
              -> Digits n
  fromInteger v = fromJust $ refine {n} (cast v)

  ||| Convert a string to a fixed-width number.
  public export
  read : {n : _} -> String -> Maybe (Digits n)
  read "" = refine 0
  read s  = readInt s >>= refine

||| Fixed-width floating point numbers
public export
record Float (minPre,maxPre : Int32) (maxPost : Bits32) where
  constructor MkFloat
  pre       : Int32
  post      : Bits32
  0 prePrf  : So (minPre  <= pre  && pre  <= maxPre)
  0 postPrf : So (post <= maxPost)

public export
Eq (Float a b c) where
  (==) = (==) `on` (\v => (v.pre,v.post))

public export
Ord (Float a b c) where
  compare = compare `on` (\v => (v.pre,v.post))

namespace Float
  public export
  read :  {minPre,maxPre : _}
       -> {maxPost : _}
       -> String
       -> Maybe (Float minPre maxPre maxPost)
  read s = do
    (pre,post) <- case split ('.' ==) (unpack s) of
                    ('+' :: pre) ::: [post] => Just (pre,post)
                    pre          ::: [post] => Just (pre,post)
                    _                       => Nothing
    Element pr prf1 <- readRefinedInt (pack pre)
    Element po prf2 <- readRefinedInt (pack post)
    pure (MkFloat pr po prf1 prf2)

  public export
  write : Float a b c -> String
  write f = show f.pre ++ "." ++ show f.post

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
  read "V2000" = Just V2000
  read "v2000" = Just V2000
  read "V3000" = Just V3000
  read "v3000" = Just V3000
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


public export
record Counts where
  constructor MkCounts
  atoms     : Digits 999
  bonds     : Digits 999
  atomLists : Digits 999
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
  read s    = (\(Element v oh) => MkValence v oh) <$> readRefinedInt s

  public export %inline
  write : Valence -> String
  write = show

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

%runElab refinedInt8 "MassDiff"

public export
readMassDiff : String -> Maybe MassDiff
readMassDiff s = (\(Element v p) => MkMassDiff v p) <$> readRefinedInt s

------------------------------
-- Hydrogen Count

||| Hydrogen Count
public export
record HydrogenCount where
  constructor MkHydrogenCount
  value : Bits8
  0 prf : So (value <= 4)

%runElab refinedBits8 "HydrogenCount"

public export
readHydrogenCount : String -> Maybe HydrogenCount
readHydrogenCount s = (\(Element v p) => MkHydrogenCount v p) <$> readRefinedInt s

------------------------------
-- AtomRef

||| Restricted to a max of three digit unsigned numbers
public export
record AtomRef where
  constructor MkAtomRef
  value : Bits32
  0 prf : So (value <= 999)

%runElab refinedBits32 "AtomRef"

public export
readAtomRef : String -> Maybe AtomRef
readAtomRef s = (\(Element v p) => MkAtomRef v p) <$> readRefinedInt s

public export
Coordinate : Type
Coordinate = Float (-9999) 99999 9999

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
  | CenterBMBAandOC -- 13

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
  read "13" = Just CenterBMBAandOC
  read _    = Nothing

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
  write CenterBMBAandOC = "13"

public export
record Bond where
  constructor MkBond
  atom1                : AtomRef
  atom2                : AtomRef
  type                 : BondType
  stereo               : BondStereo
  unused               : String
  topology             : BondTopo
  reactingCenterStatus : ReactingCenterStatus

--------------------------------------------------------------------------------
--          Properties
--------------------------------------------------------------------------------
-- -- CTAB Properties -------------------------------------------------------------
-- --  NOTE: All lines not understood by the interpreted are ignored
-- --        (Page 47 | BIOVIA Databases 2020 - CT File Formats)
-- --
-- --  **IgnoreLines - S  SKPnnn...**
-- --
-- --   where nnn is the number of following lines to be ignored
-- --
-- --   **AtomAlias - A aaa\nx...**AtomSymbolList
-- --
-- --   aaa: Atom number, x: Text describing the alias
-- --   NOTE: The x... is on the line after the atom number
-- --
-- --   **AtomValue - V  aaa v....**
-- --
-- --   aaa: Atom number, v:
-- --   Stores some value text (only text, no interpretation)
-- --
-- --   **GroupAbbrevation - G  aaappp\nx...**
-- --
-- --   Page 49 | BIOVIA Databases 2020 - CT File Formats:
-- --   aaa, ppp: Atom number, x: alias as text
-- --     Abbreviation is required for compatibility with previous versions of ISIS/Desktop, which allowed
-- --     abbreviations with only one attachment. The attachment is denoted by two atom numbers, aaa and
-- --     ppp. All of the atoms on the aaa side of the bond formed by aaa-ppp are abbreviated. The coordinates
-- --     of the abbreviation are the coordinates of aaa. The text of the abbreviation is on the following line (x...).
-- --
-- --   _The following are standard property lines of the form "M  xxx ..."_
-- --   _There are two spaces between the M and xxx._
-- --
-- --   **Charge - M  CHGnn8 aaa vvv**
-- --
-- --   Page 49 | BIOVIA Databases 2020 - CT File Formats:
-- --   aaa: atom number, vvv:
-- --     15 to +15. Default of 0 = uncharged atom. When present, this property
-- --     supersedes all charge and radical values in the atom block, forcing a 0 charge
-- --     on all atoms not listed in an M CHG or M RAD line.
-- --
-- --   **Radical - M  RADnn8 aaa vvv**
-- --
-- --   Page 49 | BIOVIA Databases 2020 - CT File Formats:
-- --   aaa: atom number, vvv:
-- --     Default of 0 = no radical, 1 = singlet (:), 2 = doublet ( . or ^), 3 = triplet (^^). When
-- --     present, this property supersedes all charge and radical values in the atom
-- --     block, forcing a 0 (zero) charge and radical on all atoms not listed in an MCHG or
-- --     MRAD line.
-- --
-- --   **Isotope - M  ISOnn8 aaa vvv**
-- --
-- --   Page 49 | BIOVIA Databases 2020 - CT File Formats:
-- --   aaa: atom number, vvv:
-- --     Absolute mass of the atom isotope as a positive integer. When present, this property
-- --     supersedes all isotope values in the atom block. Default (no entry) means natural abundance.
-- --     The difference between this absolute mass value and the natural abundance value specified in
-- --     the PTABLE.DAT file must be within the range of -18 to +12.
-- --
-- --   **RingBondCount - M  RBCnn8 aaa vvv**
-- --
-- --   Page 49 | BIOVIA Databases 2020 - CT File Formats:
-- --   aaa: atom number, vvv:
-- --      Number of ring bonds allowed: default of 0 = off, -1 = no ring bonds (r0),-2 = as drawn (r*); 2 =
-- --      (r2), 3 = (r3), 4 or more = (r4).
-- --
-- --   **SubstitutionCount - M  SUBnn8 aaa vvv**
-- --
-- --   Page 49 | BIOVIA Databases 2020 - CT File Formats:
-- --   aaa: atom number, vvv:
-- --      of substitutions allowed: default of 0 = off, -1 = no substitution (s0),-2 = as drawn (s*);
-- --      1, 2, 3, 4, 5 = (s1) through (s5), 6 or more = (s6).
-- --
-- --   **UnsaturatedCount - M  UNSnn8 aaa vvv**
-- --
-- --   Page 49 | BIOVIA Databases 2020 - CT File Formats:
-- --   aaa: atom number, vvv:
-- --      At least one multiple bond: default of 0 = off, 1 = on.
-- --
-- --   **LinkAtom - M  UNSnn8 aaa vvv**
-- --
-- --   Page 50 | BIOVIA Databases 2020 - CT File Formats:
-- --   aaa: atom number, vvv: count
-- --      Link atom (aaa) and its substituents, other than bbb and ccc, can
-- --      be repeated 1 to vvv times, (vvv > = 2). The bbb and ccc
-- --      parameters can be 0 (zero) for link nodes on atoms with
-- --      attachment point information.
-- --
-- --   **AtomList - M ALS aaannn e 11112222333344445555...**
-- --
-- --   Page 50 | BIOVIA Databases 2020 - CT File Formats:
-- --   aaa: Atom number, value
-- --   nnn: number of entries on line (16 maximum)
-- --   e: Exclusion, value is T if a ’NOT’ list, F if a normal list.
-- --   1111: Atom symbol of list entry in field of width 4
-- --
-- --   Note: This line contains the atom symbol rather than the atom number used in the atom list block,
-- --   and is independent of the Ptable. (For information about the Ptable, see BIOVIA Chemical
-- --   Representation.). Any data found in this item supersedes data from the atom list block. The number
-- --   of entries can exceed the fixed limit of 5 in the atom list block entry.
-- --
-- --   **AttachementPoint - M APOnn2 aaa vvv ...**
-- --
-- --  Page 50 | BIOVIA Databases 2020 - CT File Formats:
-- --  aaa: atom number, vvv: count
-- --     Indicates whether atom aaa of the Rgroup member is the first attachment point
-- --     (vvv = 1), second attachment point (vvv = 2), both attachment points (vvv = 3);
-- --     default of 0 = no attachment.
-- --
-- --  NOTE: Rgroup & Sgroup properties are ignored
-- data MolProperties = AtomAlias AtomReference Alias
--                    | AtomValue AtomReference ValueText
--                    | GroupAbbrevation AtomReference AtomReference Alias
--                    | SkipNextN ThreeDigitInt [Text]
--                    | PCharge AtomReference ChargeProperty
--                    | PRadical AtomReference RadicalProperty
--                    | PIsotope AtomReference IsotopeProperty
--                    | RingBondCount AtomReference RingBondCountProperty
--                    | SubstitutionCount AtomReference SubstitutionCountProperty
--                    | UnsaturatedCount AtomReference UnsaturationProperty
--                    | LinkAtom AtomReference LinkAtomRepetition LinkAtomReference LinkAtomReference
--                    | AtomList AtomReference AtomSymbolList
--   deriving(Show, Eq)
-- 
-- -- Property Types
-- -- | Identifies which "class" of property is present
-- --   Only the lines starting with M are encoded in a single
-- --   line, the others arent
-- data PropertyEntry = OneLine OneLineTag Text
--                    | TwoLine TwoLineTag [Text]
--                    | IgnoreLines ThreeDigitInt [Text]
--                    | UnknownProperty Text
-- 
-- 
-- -- | Representation of the initial character information of
-- --   a property line in a molfile. Used for determining the
-- --   number of lines belonging to a tag
-- data PropertyTagFirst = SkipNTag ThreeDigitInt
--                       | OneLineTag OneLineTag
--                       | TwoLinesTag TwoLineTag
--                       | UnrecognizedTag
--   deriving(Show, Eq)
-- 
-- -- | References entries requiring two lines
-- data TwoLineTag = AA -- Atom alias
--                 | VA -- Atom Value
--                 | AG -- Group Abreviation
--   deriving(Show, Eq)
-- 
-- -- | References entries spanning one line
-- data OneLineTag = CHG
--                 | RAD
--                 | ISO
--                 | RBC
--                 | SUB
--                 | UNS
--                 | LIN
--                 | ALS
--   deriving(Show, Eq)
-- 
-- -- | Number of available entries of a nn8 line
-- type NN8 = Refined (FromTo 1 8) Int
-- 
-- -- | Number of available entries of a LIN line
-- type LIN = Refined (FromTo 1 4) Int
-- 
-- -- | ALS number of entries
-- type N16 = Refined (FromTo 1 16) Int
-- 
-- -- | Due to having the possibility of multiple entries for a single,
-- --   this datatype can be used to group
-- -- TODO
-- 
-- -- | Representing alias text
-- --   TODO: Limitations of aliases not known (multiple lines or just 80 chars?)
-- type Alias = Text
-- 
-- -- | Representing value text
-- --   TODO: Limitations of aliases not known (multiple lines or just 80 chars?)
-- type ValueText = Text
-- 
-- -- | Charge Property
-- type ChargeProperty = Refined (Or (NegativeFromTo 15 0) (FromTo 0 15)) Int
-- 
-- -- | Radical of Property Block
-- data RadicalProperty = NoRadical
--                      | Singlet   -- (:)       Default
--                      | Doublet   -- (. or ^)
--                      | Triplet   -- (^^)
--   deriving(Show, Eq, Enum, Ord, Bounded)
-- 
-- -- | Encodes the isotope property
-- --   No value is interpreted as default which means natural abundance
-- data IsotopeProperty = DefaultIsotope
--                      | Isotope IsotopePropertyR
--   deriving(Show, Eq)
-- -- | Refined range for isotope values
-- type IsotopePropertyR = Refined (Or (NegativeFromTo 18 0) (FromTo 0 12)) Int
-- 
-- -- | RingBondCount encoding
-- data RingBondCountProperty = RBOff       -- Default
--                            | NoRingBonds
--                            | AsDrawnRB   -- (r*)
--                            | R2          -- (r2)
--                            | R3          -- (r3)
--                            | R4          -- (r4)
--   deriving(Show, Eq, Enum, Ord, Bounded)
-- 
-- -- | Substitution representation
-- data SubstitutionCountProperty = SUBOff        -- Default
--                           | NoSubstitution
--                           | AsDrawnS      -- (s*)
--                           | S1            -- (s1)
--                           | S2            -- (s2)
--                           | S3            -- (s3)
--                           | S4            -- (s4)
--                           | S5            -- (s5)
--                           | S6            -- (s6)
--  deriving(Show, Eq, Enum, Ord, Bounded)
-- 
-- -- | Unsaturation
-- data UnsaturationProperty = UNSOff | UNSOn
--   deriving(Show, Eq, Enum, Ord, Bounded)
-- 
-- -- | Counts for bbb and ccc which can be zero for atoms with
-- --   attachement point information
-- type LinkAtomReference = Refined (FromTo 0 999) Int
-- -- | Link atom count repetitions  vvv >= 2 for substituents
-- --   other than bbb and ccc
-- type LinkAtomRepetition = Refined (FromTo 2 999) Int
-- 
-- -- | Number of atom list entries on line (max. 16)
-- type AtomListEntries = Refined (FromTo 1 16) Int
-- 
-- -- | List encoding
-- data AtomListType = NotList | NormalList
--   deriving(Show, Eq, Enum, Ord, Bounded)
-- 
-- -- | Represents the atoms listed in the property line
-- data AtomSymbolList = AtomSymbolList AtomListType [MolAtomSymbol]
--   deriving(Show, Eq)
-- 
-- -- | Rgroup properties
-- --   An enumeration of the Rgroup property labels which are not handled
-- --   See: Page 50 | BIOVIA Databases 2020 - CT File Formats:
-- --
-- --   This data type is added to have a quick overview on what is not
-- --   not handled in the ctab property block in terms of Rgroup labels
-- data RgroupLabels = APO -- Attachement Point
--                   | AAL -- Atom Attachement Order
--                   | RGP -- Label Location
--                   | LOG -- Logic, Unsatisfied Sites, Range of Occurence
-- 
-- -- | Sgroup properties
-- --   An enumeration of the Sgroup property labels which are not handled
-- --   See: Page 50 | BIOVIA Databases 2020 - CT File Formats:
-- --
-- --   This data type is added to have a quick overview on what is not
-- --   not handled in the ctab property block in terms of Sgroup labels
-- data SgroupLabels = STY -- Type
--                   | SST -- Subtype
--                   | SLB -- Labels
--                   | SCN -- Connectivity
--                   | SDS -- Expansion
--                   | SAL -- Atom List
--                   | SBL -- Bond List

public export
data Property : Type where

--------------------------------------------------------------------------------
--          MolFile
--------------------------------------------------------------------------------

public export
record MolFile where
  constructor MkMolFile
  name    : StringN 80
  info    : StringN 80
  comment : StringN 80
  counts  : Counts
  atoms   : Vect (cast counts.atoms.value) Atom
  bonds   : Vect (cast counts.bonds.value) Bond
  props   : List Property


-- -- CTAB file types -------------------------------------------------------------
-- 
-- -- | Specifies reserved tags for CTAB file types
-- -- TODO: Unclear wheter list is exhaustive (most likely not)
-- data CTABFileTypes = RGfile  --  $MDL
--                    | SDfile  --  $$$$ (record separator)
--                    | RXNfile --  $RXN
--                    | RDfile  --  $RDFILE (header)
-- 
-- 
-- -- | Encoding for 2D or 3D representation
-- --   NOTE: If a non-zero Z coordinate is encountered,
-- --         then a 2D (Dim2) flag is ignored and the
-- --         molfile is treated as 3D instead
-- data Dimension = Dim2 | Dim3
--   deriving (Show, Eq, Ord, Enum, Bounded)
-- 
-- -- | Scaling factor short (SS)
-- type ScalingFactorShort = Refined (FromTo 0 99) Int
-- -- Refined types for time & Date representation
-- -- | Restriction to a two digit numbers representing years
-- type YearShort = Refined (FromTo 0 99) Int
-- -- | Months of a year
-- type Month = Refined (FromTo 1 12) Int
-- -- | Stretches to the maximal number of days in a month
-- --   Does not account for differences
-- type Day   = Refined (FromTo 1 31) Int
-- -- | Hour range
-- type Hour = Refined (FromTo 0 24) Int
-- -- | Minute Range
-- type Minute = Refined (FromTo 0 60) Int
-- 
-- -- | Representation of a date such as 20.10.2020
-- --   TODO: This type does not prevent invalid dates
-- --         such as 30.02.2020.
-- data UnfullyCheckedDate = UnfullyCheckedDate Day Month YearShort
--   deriving (Show, Eq)
-- 
-- -- | Type to represent time of a day
-- data Time = Time Hour Minute
--   deriving (Show, Eq)
-- 
