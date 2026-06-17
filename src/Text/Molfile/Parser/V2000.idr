module Text.Molfile.Parser.V2000

import Data.SortedMap
import Syntax.T1
import Text.Molfile.Parser.Stack
import Text.Molfile.Parser.Util

%default total

--------------------------------------------------------------------------------
-- Expressions
--------------------------------------------------------------------------------

||| V2000 Counts line
export
v2000 : RExp True
v2000 = repeat 34 sdigit >> oneof ['V','v'] >> "2000" >> newline

||| An arbitrary number of spaces and digits followed by a line break.
export
sdigits : Nat -> RExp True
sdigits n = orT $ atleast n sdigit >> newline

||| Expression recognizing the remainder of an `SMT` entry in
||| a v2000 properties block.
export
smtExpr : RExp True
smtExpr = repeat 3 sdigit >> ' ' >> star dot

||| Expression recognizing the remainder of an `SYT` entry in
||| a v2000 properties block.
export
styExpr : RExp True
styExpr = repeat 3 sdigit >> star (repeat 4 sdigit >> ' ' >> repeat 3 upper)

||| Expression for V2000 coordinates.
export
coordinatesV2 : RExp True
coordinatesV2 =
  repeat 3 $
        ("   " >> optmin >> digit          >> rem)
    <|> ("  "  >> optmin >> repeat 2 digit >> rem)
    <|> (" "   >> optmin >> repeat 3 digit >> rem)
    <|> (         optmin >> repeat 4 digit >> rem)

  where
    optmin, rem : RExp True
    optmin = ' ' <|> '-' <|> digit
    rem    = '.' >> repeat 4 digit

--------------------------------------------------------------------------------
-- State Transitions
--------------------------------------------------------------------------------

parameters {auto sk : CSTCK q}

  ||| Reads the number of atoms and bonds from a V2000 counts line,
  ||| and sets up a new (mutable) graph accodringly.
  export
  countsV2 : ByteString -> F1 q CST
  countsV2 bs =
    case nat (substring 0 3 bs) of -- number of atoms
      0   => writeAs sk.isEmpty True Prop2
      S k => T1.do
        g <- mgraph k
        write1 sk.count (nat $ substring 3 3 bs)
        writeAs sk.mgraph g Coords2

  ||| Converts a bytestring into a set of coordinates and
  ||| writes it to the current atom.
  export
  coordsV2 : ByteString -> F1 q CST
  coordsV2 bs =
   let x := substring 0  10 bs
       y := substring 10 10 bs
       z := substring 20 10 bs
    in modAtom {position := [coord x,coord y,coord z]} >> pure Sym2

  ||| Finalizes a V2000 atom, increasing the current node and
  ||| moving to the bond block if all atoms have been processed.
  export
  atomV2 : F1 q CST
  atomV2 = T1.do
    mg <- read1 sk.mgraph
    x  <- read1 mg.atom
    let x2 := finToNat $ FS x
    case tryLT x2 of
      Just0 prf => writeAs mg.atom (natToFinLT x2) Coords2
      Nothing0  => countdown sk.count Bnd2 Prop2

  ||| Sets an atom's charge and finalizes it via `atomV2`.
  export
  chargeV2 : F1 q CST
  chargeV2 =
    read blockcharge 3 >>= \case
      Left  x => failErr x
      Right c => modAtom {charge := c} >> atomV2

  ||| Parses a V2000 bond entry and adds an edge to the graph.
  export
  bond : F1 q CST
  bond = T1.do
    mg      <- read1 sk.mgraph
    Right x <- read node       3 | Left x => failErr x
    Right e <- read (uedge x)  3 | Left x => failErr x
    Right o <- read bondOrder  3 | Left x => failErr x
    Right s <- read bondStereo 3 | Left x => failErr x
    linsEdge mg.graph ({label := MkBond (x == e.node1) o s} e)
    countdown sk.count Bnd2 Prop2

--------------------------------------------------------------------------------
-- V2000 properties
--------------------------------------------------------------------------------

  -- repeats and effect the given number of times before returning
  -- the given result
  repeat : CST -> F1' q -> Nat -> F1 q CST
  repeat res f 0     = pure res
  repeat res f (S k) = T1.do
    f
    Nothing <- read1 sk.error_ | Just _ => pure CErr
    repeat res f k

  -- reads a three digit natural number and repeats the
  -- given effect the specified number of times
  nx : CST -> F1' q -> F1 q CST
  nx res f = read nat 3 >>= repeat res f

  -- processes a atom property in the V2000 properties block
  prop :
       (ByteString -> Either ErrPair a)
    -> (a -> MolAtom -> MolAtom)
    -> F1 q CST
  prop rd adj = read1 sk.mgraph >>= nx Prop2 . act
    where
      act : MGraph q -> F1' q
      act mg = T1.do
        Right x <- read node 4 | Left x => fail x
        Right v <- read rd 4   | Left x => fail x
        lupdNode mg.graph x (adj v)

  chg, iso, rad, sal, sty, smt : F1 q CST
  chg = prop charge $ \c => {charge := c}
  iso = prop massNr $ \m => {elem $= setMass m}
  rad = prop radical $ \r => {radical := r}

  sal = T1.do
    v <- read nat 4
    nx Prop2 $ T1.do
      mg      <- read1 sk.mgraph
      Right n <- read node 4 | Left x => fail x
      lupdNode mg.graph n {label := Just $ G v ""}

  sty = nx Prop2 $ T1.do
    n   <- read nat 4
    SUP <- read sgroupType 4 | _ => pure ()
    mod1 sk.groups (insert n "")

  smt = T1.do
    n <- read nat 5
    s <- remString
    mod1 sk.groups $ \m => case lookup n m of
      Just _  => insert n s m
      Nothing => m
    pure Prop2

export
line : Nat -> a -> (CSTCK q => F1 q CST) -> (a, Step q CSz CSTCK)
line n x f = (x, Run $ \(sk # t) => (write1 sk.pos n >> f <* incline 1) t)

export
prop2 : Steps q CSz CSTCK
prop2 =
  [ line 6 ("M  CHG" >> star ('-' <|> sdigit) >> newline) chg
  , line 6 ("M  ISO" >> star sdigit >> newline) iso
  , line 6 ("M  RAD" >> star sdigit >> newline) rad
  , line 6 ("M  SAL" >> star sdigit >> newline) sal
  , line 6 ("M  STY" >> styExpr >> newline) sty
  , line 6 ("M  SMT " >> smtExpr >> newline) smt
  , newline m_end (end >> pure CDone)
  , newline' (m_end >> newline) EndMol
  , newline' (oneof ['M','V','G','A'] >> "  " >> star dot >> newline) Prop2
  ]
