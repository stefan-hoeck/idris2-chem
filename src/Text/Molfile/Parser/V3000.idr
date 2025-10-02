module Text.Molfile.Parser.V3000

import Data.Finite
import Data.SortedMap
import Syntax.T1
import Text.Molfile.Parser.Stack
import Text.Molfile.Parser.Util

%default total

--------------------------------------------------------------------------------
-- Expressions
--------------------------------------------------------------------------------

||| the "M  V30" line prefix
public export
mv30 : RExp True
mv30 = "M  V30"

||| Recognizes a V3000 `BEGIN` statement
export
beginV3 : RExp True -> RExp True
beginV3 x = mv30 >> "BEGIN" >> spaces >> x >> dots >> newline

||| Recognizes a V3000 version line followed by
||| `"M  V30 BEGIN CTAB"` and
export
v3000 : RExp True
v3000 =
     star sdigit >> oneof ['V','v'] >> "3000" >> newline
  >> beginV3 "CTAB"
  >> mv30

||| Recognizes a V3000 `END` statement
export
endV3 : RExp True -> RExp True
endV3 x = mv30 >> "END" >> spaces >> x >> spaces >> newline

export
countsExpr : RExp True
countsExpr = mv30 >> "COUNTS" >> spaces

||| Recognizes some tokens, dropping any optional white space around them.
export
spaced : CST -> Steps q CSz CSTCK -> DFA q CSz CSTCK
spaced x ss = dfa $ conv' (plus ' ') x :: ss

export
bondExprV3 : RExp True
bondExprV3 = mv30 >> repeat 4 (spaces >> plus digit)

||| Expression for V3000 coordinates.
export
coordinatesV3 : RExp True
coordinatesV3 =
 let pre   := ('-' >> repeatRange 1 4 digit) <|> repeatRange 1 5 digit
     rem   := '.' >> repeatRange 1 4 digit
     coord := pre >> opt rem
  in coord >> plus ' ' >> coord >> plus ' ' >> coord


--------------------------------------------------------------------------------
-- State Transitions
--------------------------------------------------------------------------------

parameters {auto sk : CSTCK q}

  ||| Reads the number of atoms from the given byte string
  ||| and sets up a new (mutable) graph accodringly.
  export
  newV3 : ByteString -> F1 q CST
  newV3 bs =
    case cast {to = Nat} (decimal bs) of -- number of atoms
      0   => writeAs sk.isEmpty True EmptyV3
      S k => T1.do
        g <- mgraph k
        writeAs sk.mgraph g BCount

  ||| Writes the number of bonds to the corresponding field on the stack.
  export %inline
  bondsV3 : ByteString -> F1 q CST
  bondsV3 bs = writeAs sk.count (cast $ decimal bs) CountEnd

  ||| Reads the number of atoms from the given byte string
  ||| and sets up a new (mutable) graph accodringly.
  export
  indexV3 : ByteString -> F1 q CST
  indexV3 bs = T1.do
    let ix := cast {to = Nat} (decimal bs)
    g <- read1 sk.mgraph
    x <- read1 g.atom
    m <- read1 g.indices
    case SortedMap.lookup ix m of
      Nothing => writeAs g.indices (insert ix x m) Sym3
      Just _  => failHere {s = CSTCK} (Custom $ MNode ix) CErr

  atomV3 : F1 q CST
  atomV3 = T1.do
    mg <- read1 sk.mgraph
    x  <- read1 mg.atom
    let x2 := finToNat $ FS x
    case tryLT x2 of
      Just0 prf => writeAs mg.atom (natToFinLT x2) Atom3
      Nothing0  => pure AtomEnd

  massV3 : ByteString -> F1 q CST
  massV3 bs =
   let x := decimal $ drop 5 bs
    in case refineMassNr (cast x) of
      Nothing => failHere (Custom $ MMass x) CErr
      Just x  => modAtom {elem $= setMass x} >> pure Prop3

  export
  beginBondV3 : F1 q CST
  beginBondV3 = countdown sk.count BondBegin RestV3

  export
  checkBondV3 : F1 q CST
  checkBondV3 = T1.do
    mg     <- read1 sk.mgraph
    Just e <- read1 mg.bond | Nothing => pure BondEnd
    linsEdge mg.graph e
    countdown sk.count Bnd3 BondEnd

  ||| Converts a bytestring into a set of coordinates and
  ||| writes it to the current atom.
  export
  coordsV3 : ByteString -> F1 q CST
  coordsV3 bs =
   let (x,r) := break (SPACE ==) (trimLeft bs)
       (y,z) := break (SPACE ==) (trimLeft r)
    in modAtom {position := [coord x,coord y,coord z]} >> pure AAMap

  export
  bondV3 : ByteString -> F1 q CST
  bondV3 bs = T1.do
    [_,_,_,tp,a1,a2] <- pure (splitNonEmpty SPACE bs) | _ => checkBondV3
    mg               <- read1 sk.mgraph
    ixs              <- read1 mg.indices
    let Right x      := lkpNode ixs a1   | Left x => failErr x
        Right e      := lkpEdge ixs x a2 | Left x => failErr x
        Right o      := bondOrder tp     | Left x => failErr x
        lbl          := MkBond (x < e.node2) o NoBondStereo
    writeAs mg.bond (Just $ {label := lbl} e) BndProp3

chargeV3 : Charge -> Step1 q CSz CSTCK
chargeV3 c (_ # t) = let _ # t := modAtom {charge := c} t in Prop3 # t

radicalV3 : Radical -> Step1 q CSz CSTCK
radicalV3 c (_ # t) = let _ # t := modAtom {radical := c} t in Prop3 # t

||| Recognizes and drops a fixed number of V3000 lines, increasing
||| the line count accordingly and setting the column to `6`
||| (right after the `M  V30` prefix). Constant `mv30` must not be
||| part of the given regular expression.
export
mv30prefix : Nat -> RExp b -> CST -> (RExp True, Step q CSz CSTCK)
mv30prefix n x = linecol' n 6 (orT $ x >> mv30)

export
emptyEnd : List (RExp True, Step q CSz CSTCK)
emptyEnd =
 let pre := zeroes >> endV3 "CTAB" >> m_end
  in [newlines' 3 pre CDone, newlines' 3 (pre >> newline) EndMol]

||| Recognizers for additional atom properties.
|||
||| Most of these are currently not handled, and some
||| are not yet supported.
|||
||| TODO: At least handle (and possibly ignore) the following props:
|||       `Rgroups`, `ATTCHORD`, `CLASS`, `SEQID`, `SEQNAME`
export
prop3 : List (RExp True, Step q CSz CSTCK)
prop3 =
     vals (("CHG="++) . interpolate) chargeV3 values
  ++ vals (("RAD="++) . dispRadical) radicalV3 values
  ++ [ conv   ("MASS=" >> plus digit) massV3
     , cexpr' ("CFG=" >> oneof ['0','1','2','3']) Prop3
     , conv'  ("VAL=" >> opt '-' >> plus digit) Prop3
     , conv'  ("HCOUNT=" >> opt '-' >> plus digit) Prop3
     , cexpr' ("STBOX=" >> bindigit) Prop3
     , cexpr' ("INVERT=" >> oneof ['0','1','2']) Prop3
     , cexpr' ("EXACHG=" >> bindigit) Prop3
     , conv'  ("SUBST=" >> opt '-' >> plus digit) Prop3
     , cexpr' ("UNSAT=" >> bindigit) Prop3
     , conv'  ("RBCNT=" >> opt '-' >> plus digit) Prop3
     , conv'  ("ATTACHPT=" >> opt '-' >> plus digit) Prop3
     , mv30prefix 1 ('-' >> newline) Prop3
     , newline newline atomV3
     ]

export
bondProp3 : List (RExp True, Step q CSz CSTCK)
bondProp3 =
  [ mv30prefix 1 ('-' >> newline) BndProp3
  , newline newline checkBondV3
  ]

||| Recognizes (and currently discards) all remaining lines starting
||| with `M  V30` until `M  END` is encountered.
export
rest3 : List (RExp True, Step q CSz CSTCK)
rest3 =
  [ conv' m_end CDone
  , newline' (m_end >> newline) EndMol
  , newline' (mv30 >> dots >> newline) RestV3
  ]
