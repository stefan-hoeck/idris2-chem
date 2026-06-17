module Text.Molfile.Parser.V3000

import Data.Finite
import Data.SortedMap
import Syntax.T1
import Text.Molfile.Parser.KeyVal
import Text.Molfile.Parser.Stack
import Text.Molfile.Parser.Util
import Text.Molfile.Writer.Util
import Text.Molfile.Writer.V3000

%default total

--------------------------------------------------------------------------------
-- Expressions
--------------------------------------------------------------------------------

||| Recognizes a V3000 `BEGIN` statement
export
beginV3 : (s : String) -> (0 p : NonEmpty (unpack s)) => RExp True
beginV3 x =
  mv30 >> spaces >> like "BEGIN" >> spaces >> like x >> dots >> newline

||| Recognizes a V3000 version line followed by
||| `"M  V30 BEGIN CTAB"` and
export
v3000 : RExp True
v3000 = star sdigit >> like "V3000" >> newline >> beginV3 "CTAB"

||| Recognizes a V3000 `END` statement
export
endV3 : (s : String) -> (0 p : NonEmpty (unpack s)) => RExp True
endV3 x = mv30 >> spaces >> "END" >> spaces >> like x >> spaces >> newline

export
countsExpr : RExp True
countsExpr = mv30 >> like "COUNTS" >> spaces

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

supLines : RExp True
supLines = mv30 >> spaces >> decimal >> spaces >> like "SUP" >> keyValRest

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

  export
  sup : ByteString -> F1 q CST
  sup bs = case keyVals bs of
    Left x => getPosition >>= \p => failWith (fromPosition x p) CErr
    Right (I n::S _::I _::t) => case lookupVal "LABEL" t >>= toString of
      Just lbl => case lookupVal "ATOMS" t >>= toNats of
        Just as => T1.do
          mg <- read1 sk.mgraph
          addGroup (cast n) mg lbl as
        Nothing => failHere (Custom MAbbr) CErr
      Nothing => failHere (Custom MAbbr) CErr
    Right p => failHere (Custom MAbbr) CErr
    where
      addGroup : Nat -> MGraph q -> String -> List Nat -> F1 q CST
      addGroup v g l []        = pure SGroup
      addGroup v g l (x :: xs) = T1.do
       is <- read1 g.indices
       let Just n := lookup x is | _ => failHere {sk} (Custom $ MNode x) CErr
       lupdNode g.graph n {label := Just $ G v l}
       addGroup v g l xs

bondStereoV3 : BondStereo -> Step1 q CSz CSTCK
bondStereoV3 s _ t = let _ # t := modBond {stereo := s} t in BndProp3 # t

chargeV3 : Charge -> Step1 q CSz CSTCK
chargeV3 c _ t = let _ # t := modAtom {charge := c} t in Prop3 # t

radicalV3 : Radical -> Step1 q CSz CSTCK
radicalV3 c _ t = let _ # t := modAtom {radical := c} t in Prop3 # t

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
|||
||| TODO: CHG, RAD, and CFG (for bonds) should be case-insensitive
export
prop3 : List (RExp True, Step q CSz CSTCK)
prop3 =
     vals (("CHG="++) . interpolate) chargeV3 values
  ++ vals (("RAD="++) . dispRadical) radicalV3 values
  ++ [ conv   (like "MASS=" >> plus digit) massV3
     , cexpr' (like "CFG=" >> oneof ['0','1','2','3']) Prop3
     , conv'  (like "VAL=" >> integer) Prop3
     , conv'  (like "HCOUNT=" >> integer) Prop3
     , cexpr' (like "STBOX=" >> bindigit) Prop3
     , cexpr' (like "INVERT=" >> oneof ['0','1','2']) Prop3
     , cexpr' (like "EXACHG=" >> bindigit) Prop3
     , conv'  (like "SUBST=" >> integer) Prop3
     , cexpr' (like "UNSAT=" >> bindigit) Prop3
     , conv'  (like "RBCNT=" >> integer) Prop3
     , conv'  (like "ATTACHPT=" >> integer) Prop3
     , mv30prefix 1 ('-' >> newline) Prop3
     , newline newline atomV3
     ]

export
bondProp3 : List (RExp True, Step q CSz CSTCK)
bondProp3 =
     vals (("CFG="++) . dispStereoV3) bondStereoV3 values
  ++ [ cexpr' (like "TOPO=" >> oneof ['0','1','2']) BndProp3
     , conv'  (like "RXCTR=" >> integer) BndProp3
     , cexpr' (like "STBOX=" >> bindigit) BndProp3
     , mv30prefix 1 ('-' >> newline) BndProp3
     , newline newline checkBondV3
     ]

||| Recognizes (and currently discards) all remaining lines starting
||| with `M  V30` until `M  END` is encountered.
export
rest3 : List (RExp True, Step q CSz CSTCK)
rest3 =
  [ conv' m_end CDone
  , newline' (m_end >> newline) EndMol
  , newline' (beginV3 "Sgroup") SGroup
  , newline' (mv30 >> dots >> newline) RestV3
  ]

export
sgroup : List (RExp True, Step q CSz CSTCK)
sgroup =
  [ newline' (endV3 "Sgroup") RestV3
  , multiline supLines sup
  , newline' (mv30 >> dots >> newline) SGroup
  ]
