module Text.Molfile.Parser.Stack

import Data.Array.Mutable
import Data.SortedMap as SM

import Syntax.T1

import Text.ILex.Derive

import public Text.ILex
import public Text.Molfile.Types

%default total
%language ElabReflection

--------------------------------------------------------------------------------
-- Stack and State
--------------------------------------------------------------------------------

%runElab deriveParserState "CSz" "CST"
  [ "CErr", "H1", "H2", "H3", "Counts", "EndMol", "CDone" -- general states
  , "SData", "SDValue" -- SD Files

  -- V2000 States
  , "Coords2", "Sym2", "Chrg2", "Bnd2", "Prop2"

  -- V3000 States
  , "CountsV3", "ACount", "BCount", "CountEnd", "EmptyV3"
  , "Atom3", "Index3", "Coords3", "Sym3", "AAMap", "Prop3", "AtomEnd"
  , "BondBegin", "BondEnd", "Bnd3", "BndProp3"
  , "RestV3", "SGroup"
  ]

||| A molecular graph in the making.
public export
record MGraph (q : Type) where
  constructor MG
  atoms   : Nat
  atom    : Ref q (Fin $ S atoms)
  indices : Ref q (SortedMap Nat $ Fin (S atoms))
  bond    : Ref q (Maybe $ Edge (S atoms) MolBond)
  graph   : MArray q (S atoms) (Adj (S atoms) MolBond MolAtom)

export
mgraph : (atoms : Nat) -> F1 q (MGraph q)
mgraph atoms = T1.do
  atm <- ref1 FZ
  ixs <- ref1 SM.empty
  bnd <- ref1 Nothing
  g   <- marray1 (S atoms) (A (cast {from = Elem} C) empty)
  pure (MG atoms atm ixs bnd g)

public export
record CSTCK (q : Type) where
  constructor CK
  -- text position
  prev_      : Ref q ByteString
  cur_       : Ref q ByteString
  offset_    : Ref q Nat
  relpos_    : Ref q Integer
  len_       : Ref q Nat
  positions_ : Ref q (SnocList BytePos)

  -- headers
  h1,h2,h3   : Ref q MolLine

  -- graphs
  mgraph     : Ref q (MGraph q)
  stack_     : Ref q (SnocList Molfile)
  groups     : Ref q (SortedMap Nat String)
  count      : Ref q Nat
  isEmpty    : Ref q Bool

  -- sdata
  sdhead     : Ref q SDHeader
  sdvals     : Ref q (SnocList StructureData)

  -- utilities
  error_     : Ref q (Maybe $ BBErr MolErr)
  strings_   : Ref q (SnocList String)
  pos        : Ref q Nat

%runElab derive "CSTCK" [HasBBErr,HasBytes,HasStack,HasStringLits]

export
init : F1 q (CSTCK q)
init = T1.do
  pr <- ref1 empty
  fl <- ref1 empty
  ro <- ref1 Z
  rr <- ref1 0
  ll <- ref1 Z
  ps <- ref1 [<]
  h1  <- ref1 ""
  h2  <- ref1 ""
  h3  <- ref1 ""
  mg  <- mgraph 0
  gr  <- ref1 mg
  gs  <- ref1 [<]
  grp <- ref1 SM.empty
  cnt <- ref1 Z
  ie  <- ref1 False
  sdh <- ref1 ""
  sdd <- ref1 [<]
  err <- ref1 Nothing
  str <- ref1 [<]
  pos <- ref1 Z
  pure (CK pr fl ro rr ll ps h1 h2 h3 gr gs grp cnt ie sdh sdd err str pos)

export %inline
setPos : (sk : CSTCK q) => Nat -> F1' q
setPos n = write1 sk.pos n

export %inline
incPos : (sk : CSTCK q) => Nat -> F1 q Nat
incPos n = T1.do
  v <- read1 sk.pos
  writeAs sk.pos (v+n) v
