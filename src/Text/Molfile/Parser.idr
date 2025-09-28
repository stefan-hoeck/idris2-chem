module Text.Molfile.Parser

import Text.Molfile.Types
import Data.Array.Mutable
import Data.SortedMap as SM
import Data.Finite
import Syntax.T1
import Text.ILex
import Text.ILex.Derive

%default total
%language ElabReflection

--------------------------------------------------------------------------------
-- Values
--------------------------------------------------------------------------------

isos : List Isotope
isos = MkI H (Just 2) :: MkI H (Just 3) :: map (`MkI` Nothing) values

dispIso : Isotope -> String
dispIso (MkI H (Just 2)) = "D"
dispIso (MkI H (Just 3)) = "T"
dispIso (MkI e _)        = symbol e

--------------------------------------------------------------------------------
-- Expressions
--------------------------------------------------------------------------------

fill : Nat -> String -> List String
fill n s = go [<] (n `minus` length s) 0
  where
    go : SnocList String -> Nat -> Nat -> List String
    go ss 0     j = ss <>> [s ++ replicate j ' ']
    go ss (S k) j =
      go (ss:< (replicate (S k) ' ' ++ s ++ replicate j ' ')) k (S j)

newline : RExp True
newline = '\r' <|> '\n' <|> "\r\n"

sdigit : RExp True
sdigit = ' ' <|> digit

szeroes : RExp True
szeroes = star (' ' <|> '0') >> newline

smtExpr, styExpr : RExp True
smtExpr = repeat 3 sdigit >> ' ' >> star dot
styExpr = repeat 3 sdigit >> star (repeat 4 sdigit >> ' ' >> repeat 3 upper)

sdigits : Nat -> RExp True
sdigits n = orT $ atleast n sdigit >> newline

v2000, v3000, coordinate : RExp True
v2000 = repeat 34 sdigit >> oneof ['V','v'] >> "2000" >> newline
v3000 = star sdigit >> oneof ['V','v'] >> "3000" >> newline

coordinate =
      ("   " >> optmin >> digit          >> rem)
  <|> ("  "  >> optmin >> repeat 2 digit >> rem)
  <|> (" "   >> optmin >> repeat 3 digit >> rem)
  <|> (         optmin >> repeat 4 digit >> rem)

  where
    optmin, rem : RExp True
    optmin = ' ' <|> '-' <|> digit
    rem    = '.' >> repeat 4 digit

--------------------------------------------------------------------------------
-- Stack and State
--------------------------------------------------------------------------------

%runElab deriveParserState "CSz" "CST"
  [ "CErr", "H1", "H2", "H3", "Counts", "EndMol", "CDone" -- general states
  , "Coords2", "Sym2", "Chrg2", "Bnd2", "Prop2" -- V2000 states
  , "SData", "SDValue"
  ]

record MGraph (q : Type) where
  constructor MG
  atoms : Nat
  atom  : Ref q (Fin $ S atoms)
  graph : MArray q (S atoms) (Adj (S atoms) MolBond MolAtom)

mgraph : (atoms : Nat) -> F1 q (MGraph q)
mgraph atoms = T1.do
  atm <- ref1 FZ
  g   <- marray1 (S atoms) (A (cast {from = Elem} C) empty)
  pure (MG atoms atm g)

export
record CSTCK (q : Type) where
  constructor CK
  -- text position
  line_      : Ref q Nat
  col_       : Ref q Nat
  positions_ : Ref q (SnocList Position)

  -- headers
  h1,h2,h3   : Ref q MolLine

  -- graphs
  mgraph     : Ref q (MGraph q)
  stack_     : Ref q (SnocList Molfile)
  groups     : Ref q (SortedMap Nat String)

  -- atom
  coords     : Ref q Coordinates
  isotope    : Ref q Isotope
  charge     : Ref q Charge
  count      : Ref q Nat

  -- sdata
  sdhead     : Ref q SDHeader
  sdvals     : Ref q (SnocList StructureData)

  -- utilities
  error_     : Ref q (Maybe $ BoundedErr MolErr)
  bytes_     : Ref q ByteString
  strings_   : Ref q (SnocList String)
  pos        : Ref q Nat

%runElab derive "CSTCK" [HasPosition,HasError,HasBytes,HasStack,HasStringLits]

init : F1 q (CSTCK q)
init = T1.do
  l   <- ref1 Z
  c   <- ref1 Z
  ps  <- ref1 [<]
  h1  <- ref1 ""
  h2  <- ref1 ""
  h3  <- ref1 ""
  mg  <- mgraph 0
  gr  <- ref1 mg
  gs  <- ref1 [<]
  grp <- ref1 SM.empty
  cos <- ref1 [0,0,0]
  iso <- ref1 (MkI Elem.C Nothing)
  chg <- ref1 (the Charge 0)
  cnt <- ref1 Z
  sdh <- ref1 ""
  sdd <- ref1 [<]
  err <- ref1 Nothing
  bs  <- ref1 empty
  str <- ref1 [<]
  pos <- ref1 Z
  pure (CK l c ps h1 h2 h3 gr gs grp cos iso chg cnt sdh sdd err bs str pos)

--------------------------------------------------------------------------------
-- State Transitions
--------------------------------------------------------------------------------

%inline
line : Nat -> a -> (CSTCK q => F1 q CST) -> (a, Step q CSz CSTCK)
line n x f = (x, Rd $ \(sk # t) => (write1 sk.pos n >> f <* incline 1) t)

parameters {auto sk : CSTCK q}
  fail : ErrPair -> F1' q
  fail (BS l $ BV _ o2 _, x) = T1.do
    BS _ (BV _ o1 _) <- read1 (bytes sk)
    p                <- getPosition
    let ps := addCol (o2 `minus` o1) p
        pe := addCol l ps
    write1 sk.error_ (Just $ B (Custom x) $ BS ps pe)

  failErr : ErrPair -> F1 q CST
  failErr p = fail p >> pure CErr

  %inline
  inc : Nat -> F1 q Nat
  inc k = read1 sk.pos >>= \n => writeAs sk.pos (k+n) n

  %inline
  drop : Nat -> F1' q
  drop = ignore1 . inc

  remString : F1 q String
  remString = T1.do
    p  <- read1 sk.pos
    bs <- read1 sk.bytes_
    pure (toString $ trim $ drop p bs)

  %inline
  read : (ByteString -> a) -> (len : Nat) -> F1 q a
  read f len = T1.do
    bs <- read1 sk.bytes_
    p  <- inc len
    pure (f $ substring p len bs)


  end : F1 q CST
  end = T1.do
    h1   <- replace1 sk.h1 ""
    h2   <- replace1 sk.h2 ""
    h3   <- replace1 sk.h3 ""
    sds  <- getList sk.sdvals
    mg   <- read1 sk.mgraph
    grps <- replace1 sk.groups SM.empty
    lupdNodes mg.graph $ {label $= map (groupLbl grps)}
    g  <- Array.Core.unsafeFreeze mg.graph
    push1 sk.stack_ (MkMolfile h1 h2 h3 (G _ $ IG g) sds)
    pure H1

  %inline
  h1,h2,h3 : ByteString -> F1 q CST
  h1 bs = writeAs sk.h1 (cast bs) H2
  h2 bs = writeAs sk.h2 (cast bs) H3
  h3 bs = writeAs sk.h3 (cast bs) Counts

  checkBond : F1 q CST
  checkBond = T1.do
    S k <- read1 sk.count | 0 => pure Prop2
    writeAs sk.count k Bnd2

  atom : Charge -> F1 q CST
  atom cg = T1.do
    c  <- read1 sk.coords
    i  <- read1 sk.isotope
    mg <- read1 sk.mgraph
    x  <- read1 mg.atom
    set mg.graph x (A (MkAtom i cg c NoRadical () () () Nothing) empty)
    let x2 := finToNat $ FS x
    case tryLT x2 of
      Just0 prf => writeAs mg.atom (natToFinLT x2) Coords2
      Nothing0  => checkBond

  repeat : CST -> F1' q -> Nat -> F1 q CST
  repeat res f 0     = pure res
  repeat res f (S k) = T1.do
    f
    Nothing <- read1 sk.error_ | Just _ => pure CErr
    repeat res f k

  nx : CST -> F1' q -> F1 q CST
  nx res f = read nat 3 >>= repeat res f

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

  chrg, bond, chg, iso, rad, sal, sty, smt : F1 q CST
  chg = prop charge $ \c => {charge := c}
  iso = prop massNr $ \m => {elem $= setMass m}
  rad = prop radical $ \r => {radical := r}
  chrg = read blockcharge 3 >>= either failErr atom

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
    drop 6
    n <- read nat 3
    s <- remString
    mod1 sk.groups $ \m => case lookup n m of
      Just _  => insert n s m
      Nothing => m
    pure Prop2

  setBond : BondOrder -> F1 q CST
  setBond o = T1.do
    mg      <- read1 sk.mgraph
    Right x <- read node       3 | Left x => failErr x
    Right e <- read (uedge x)  3 | Left x => failErr x
    linsEdge mg.graph ({label := MkBond (x == e.node1) o NoBondStereo} e)
    checkBond

  bond = T1.do
    mg      <- read1 sk.mgraph
    Right x <- read node       3 | Left x => failErr x
    Right e <- read (uedge x)  3 | Left x => failErr x
    Right o <- read bondOrder  3 | Left x => failErr x
    Right s <- read bondStereo 3 | Left x => failErr x
    linsEdge mg.graph ({label := MkBond (x == e.node1) o s} e)
    checkBond

  counts, coords : ByteString -> F1 q CST
  coords x = writeAs sk.coords [coord 0 10 x,coord 10 10 x,coord 20 10 x] Sym2

  counts bs =
    case nat (substring 0 3 bs) of -- number of atoms
      0   => pure Prop2
      S k => T1.do
        g <- mgraph k
        write1 sk.count (nat $ substring 3 3 bs)
        writeAs sk.mgraph g Coords2

  sdheader : ByteString -> F1 q CST
  sdheader bs = writeAs sk.sdhead (readHeader bs) SDValue

  endSDValue : F1 q CST
  endSDValue = T1.do
    hd <- read1 sk.sdhead
    v  <- getStr
    push1 sk.sdvals (SD hd $ fromMaybe "" $ refineSDValue v)
    pure SData

--------------------------------------------------------------------------------
-- Parser
--------------------------------------------------------------------------------

prop2 : Steps q CSz CSTCK
prop2 =
  [ line 6 ("M  CHG" >> star ('-' <|> sdigit) >> newline) chg
  , line 6 ("M  ISO" >> star sdigit >> newline) iso
  , line 6 ("M  RAD" >> star sdigit >> newline) rad
  , line 6 ("M  SAL" >> star sdigit >> newline) sal
  , line 6 ("M  STY" >> styExpr >> newline) sty
  , line 6 ("M  SMT " >> smtExpr >> newline) smt
  , newline' ("M  END" >> star dot >> opt newline) EndMol
  ]

sdata : Steps q CSz CSTCK
sdata =
  [ newline ("$$$$" >> newline) end
  , cexpr  "$$$$" (ignore1 end >> pure CDone)
  , convline ( '>' >> star dot >> newline) sdheader
  ]

sdvalue : Steps q CSz CSTCK
sdvalue =
  [ newline (star ' ' >> newline) endSDValue
  , convline (star dot >> newline) (pushStr SDValue . toString . trimRight)
  ]

ctabTrans : Lex1 q CSz CSTCK
ctabTrans =
  lex1
    [ E H1       $ dfa [convline (star dot >> newline) h1]
    , E H2       $ dfa [convline (star dot >> newline) h2]
    , E H3       $ dfa [convline (star dot >> newline) h3]
    , E Counts   $ dfa [newline' v3000 CErr, convline v2000 counts]
    , E Coords2  $ dfa [conv (repeat 3 coordinate >> ' ') coords]
    , E Sym2     $ dfa $ writeValsN (fill 3 . dispIso) isotope Chrg2 isos
    , E Chrg2    $ dfa [newline szeroes (atom 0), line 2 (sdigits 5) chrg]
    , E Bnd2     $ dfa [line 0 (sdigits 6) bond]
    , E Prop2    $ dfa prop2
    , E EndMol   $ dfa sdata
    , E SData    $ dfa sdata
    , E SDValue  $ dfa sdvalue
    ]

ctabErr : Arr32 CSz (CSTCK q -> F1 q (BoundedErr MolErr))
ctabErr = arr32 CSz (unexpected []) []

ctabEOI : CST -> CSTCK q -> F1 q (Either (BoundedErr MolErr) (List Molfile))
ctabEOI st sk =
  case st == H1 || st == CDone of
    False => case st == EndMol of
      False => arrFail CSTCK ctabErr st sk
      True  => ignore1 end >> getList sk.stack_ >>= pure . Right
    True  => getList sk.stack_ >>= pure . Right

export
ctab : P1 q (BoundedErr MolErr) CSz CSTCK (List Molfile)
ctab = P H1 init ctabTrans snocChunk ctabErr ctabEOI

parameters {auto has : Has (ParseError MolErr) es}
  export
  readMolFrom : Origin -> String -> ChemRes es Molfile
  readMolFrom o s =
    case parseString ctab o s of
      Left x    => Left $ inject x
      Right []  => Right (MkMolfile "" "" "" (G 0 empty) [])
      Right [x] => Right x
      Right _   =>
        Left (inject $ toParseError o s (B (Custom MEntries) NoBounds))

  export %inline
  readMol : String -> ChemRes es Molfile
  readMol = readMolFrom Virtual

  export %inline
  readSDFFrom : Origin -> String -> ChemRes es (List Molfile)
  readSDFFrom o = mapFst inject . parseString ctab o

  export %inline
  readSDF : String -> ChemRes es (List Molfile)
  readSDF = readSDFFrom Virtual
