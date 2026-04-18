module Text.Smiles.Parser

import Chem
import Data.Finite
import Data.SnocVect
import Derive.Prelude
import Syntax.T1
import Text.ILex
import Text.ILex.Derive
import Text.Smiles.Types

%default total
%language ElabReflection

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

%inline
drop : List a -> List a
drop (_::t) = t
drop []     = []

%inline
doubleHead : List a -> List a
doubleHead l@(h::_) = h::l
doubleHead []       = []

public export
data SmilesErr : Type where
  RingBondMismatch   : SmilesErr
  UnclosedRing       : SmilesErr
  ManyEntries        : SmilesErr

export
Interpolation SmilesErr where
  interpolate RingBondMismatch = "Ring bonds do not match"
  interpolate UnclosedRing     = "Unclosed ring"
  interpolate ManyEntries      = "More than one molecule"

%runElab derive "SmilesErr" [Eq,Show]

public export
0 SmilesParseErr : Type
SmilesParseErr = ParseError SmilesErr

data DOB : Type where
  No  : DOB
  Dot : DOB
  Bnd : SmilesBond -> DOB

record RingInfo n where
  constructor R
  start : Fin n
  nr    : RingNr
  atom  : SmilesAtom
  bond  : Maybe SmilesBond
  pos   : Position

record AtomInfo n where
  constructor A
  node  : Fin n
  atom  : SmilesAtom

smilesBond : (xa,ya : Bool) -> SmilesBond
smilesBond True True = Arom
smilesBond _    _    = Sngl

ringBond : (b,c : Maybe SmilesBond) -> (x,y : SmilesAtom) -> Maybe SmilesBond
ringBond Nothing Nothing   x y = Just $ smilesBond (isArom x) (isArom y)
ringBond Nothing (Just x)  _ _ = Just x
ringBond (Just x) Nothing  _ _ = Just x
ringBond (Just x) (Just y) _ _ = if x == y then Just x else Nothing

lookupRing : RingNr -> List (RingInfo n) -> Maybe (RingInfo n)
lookupRing r []      = Nothing
lookupRing r (x::xs) = case compare r (nr x) of
  LT => Nothing
  EQ => Just x
  GT => lookupRing r xs

insert : RingInfo n -> List (RingInfo n) -> List (RingInfo n)
insert r []      = [r]
insert r (x::xs) = if r.nr < x.nr then r::x::xs else x::insert r xs

delete : RingNr -> List (RingInfo n) -> List (RingInfo n)
delete r []      = []
delete r (x::xs) = if r == x.nr then xs else x::delete r xs

ringBondMismatch : Ring -> Position -> BoundedErr SmilesErr
ringBondMismatch r p =
 let bs := BS p $ addCol (length "\{r}") p
  in B (Custom RingBondMismatch) bs

record ST where
  constructor S
  cnt   : Nat
  stck  : List (AtomInfo cnt)
  atoms : SnocVect cnt SmilesAtom
  bonds : List (Edge cnt SmilesBond)
  rings : List (RingInfo cnt)

empty : ST
empty = S 0 [] [<] [] []

toGraph : ST -> Either (BoundedErr SmilesErr) SmilesGraph
toGraph (S n _ a b [])                = Right $ G n (mkGraph (cast a) b)
toGraph (S _ _ _ _ (R _ r _ b p ::_)) =
 let bs := BS p $ addCol (length "\{R r b}") p
  in Left $ B (Custom UnclosedRing) bs

weakenST : List (AtomInfo n) -> List (AtomInfo $ S n)
weakenST x = believe_me x

weakenBS : List (Edge n e) -> List (Edge (S n) e)
weakenBS x = believe_me x

weakenRS : List (RingInfo n) -> List (RingInfo (S n))
weakenRS x = believe_me x

plainAtom : SmilesAtom -> ST -> ST
plainAtom a1 (S c (A n a::ss) sa bs rs) =
  let bs2 := edge n (smilesBond (isArom a) (isArom a1)) :: weakenBS bs
      st2 := A last a1 :: weakenST ss
   in S (S c) st2 (sa:<a1) bs2 (weakenRS rs)
plainAtom a1 st = st

atomWithBond : SmilesBond -> SmilesAtom -> ST -> ST
atomWithBond b a1 (S c (A n _::ss) sa bs rs) =
  let bs2 := edge n b :: weakenBS bs
      st2 := A last a1 :: weakenST ss
   in S (S c) st2 (sa:<a1) bs2 (weakenRS rs)
atomWithBond b a1 st = st

dottedAtom : SmilesAtom -> ST -> ST
dottedAtom a1 (S c st sa bs rs) =
  S (S c) (A last a1 :: weakenST st) (sa:<a1) (weakenBS bs) (weakenRS rs)

addRing : Position -> Ring -> ST -> Either (BoundedErr SmilesErr) ST
addRing p (R r mb1) st =
  case st.stck of
    A n1 a1::_ => case lookupRing r st.rings of
      Just (R n2 nr a2 mb2 p) => case ringBond mb1 mb2 a1 a2 of
        Just b  => case mkEdge n1 n2 b of
          Just e  => Right $ {bonds $= (e::), rings $= delete r} st
          Nothing => Right st -- impossible
        Nothing => Left (ringBondMismatch (R r mb1) p)
      Nothing => Right $ {rings $= insert (R n1 r a1 mb1 p)} st
    [] => Right st -- impossible

--------------------------------------------------------------------------------
--          Parser
--------------------------------------------------------------------------------

export
record SSTCK (q : Type) where
  constructor SS
  line_      : Ref q Nat
  col_       : Ref q Nat
  positions_ : Ref q (SnocList Position)
  st         : Ref q ST
  dob        : Ref q DOB
  bytes_     : Ref q ByteString
  mass       : Ref q (Maybe MassNr)
  elem       : Ref q AromElem
  chirality  : Ref q Chirality
  hcount     : Ref q HCount
  charge     : Ref q Charge
  error_     : Ref q (Maybe $ BoundedErr SmilesErr)
  stack_     : Ref q (SnocList SmilesGraph)

%runElab derive "SSTCK" [HasPosition, HasBytes, HasError, HasStack]

init : F1 q (SSTCK q)
init = T1.do
  l   <- ref1 Z
  c   <- ref1 Z
  p   <- ref1 [<]
  s   <- ref1 empty
  db  <- ref1 Dot
  b   <- ref1 ByteString.empty
  ms  <- ref1 Nothing
  el  <- ref1 (MkAE C False)
  cy  <- ref1 (the Chirality None)
  hc  <- ref1 (the HCount 0)
  ch  <- ref1 (the Charge 0)
  er  <- ref1 Nothing
  st  <- ref1 [<]
  pure (SS l c p s db b ms el cy hc ch er st)

%runElab deriveParserState "SSz" "SST"
  [ "Chain", "NewBranch", "SRing", "Closed", "Err", "Atom"
  , "BMass","BElem","BChiral","BHCount","BCharge","BEnd"
  ]

endGraph : SSTCK q -> F1 q (Maybe (BoundedErr SmilesErr))
endGraph sk = T1.do
  st    <- replace1 sk.st empty
  write1 sk.dob Dot
  let Right g := toGraph st | Left err => pure (Just err)
  [<] <- replace1 sk.positions_ [<]
    | _:<p => pure $ Just (B (Unclosed "(") (BS p (incCol p)))
  case g.order of
    0 => pure Nothing
    _ => push1 sk.stack_ g >> pure Nothing

onAtom : SmilesAtom -> Step1 q SSz SSTCK
onAtom a = \(sk # t) =>
 let s # t := read1 sk.st t
  in case read1 sk.dob t of
       No    # t => writeAs sk.st (plainAtom a s) SRing t
       Bnd b # t =>
        let _ # t := write1 sk.dob No t
         in writeAs sk.st (atomWithBond b a s) SRing t
       Dot # t  =>
        let _ # t := write1 sk.dob No t
         in writeAs sk.st (dottedAtom a s) SRing t

onRing : Ring -> Step1 q SSz SSTCK
onRing r = \(sk # t) =>
  let p # t := getPosition t
      s # t := read1 sk.st t
   in case addRing p r s of
        Right s2 => writeAs sk.st s2 SRing t
        Left  x  => failWith x Err t

bracket : (sk : SSTCK q) => F1 q SST
bracket t =
  let m  # t := replace1 sk.mass Nothing t
      e  # t := read1 sk.elem t
      cy # t := replace1 sk.chirality None t
      h  # t := replace1 sk.hcount 0 t
      ch # t := replace1 sk.charge 0 t
   in onAtom (bracket (aromIsotope m e) cy h ch) (sk # t)

mass : (RExp True, Step q SSz SSTCK)
mass = conv (plus digit) wrt
  where
    %inline wrt : (sk : SSTCK q) =>  ByteString ->F1 q SST
    wrt bs = writeAs sk.mass (refineMassNr $ cast $ decimal bs) BElem

elem : List (RExp True, Step q SSz SSTCK)
elem = writeVals interpolate elem BChiral values

chirality : List (RExp True, Step q SSz SSTCK)
chirality = writeVals interpolate chirality BHCount values

hc : List (RExp True, Step q SSz SSTCK)
hc = cexpr "H1" (wrt 1) :: vals encodeH (\v => \(sk # t) => wrt v t) values
  where
    wrt : HCount -> (sk : SSTCK q) => F1 q SST
    wrt c = writeAs sk.hcount c BCharge

chrg : List (RExp True, Step q SSz SSTCK)
chrg =
     cexpr "+1" (wrt 1)
  :: cexpr "-1" (wrt (-1))
  :: cexpr "++" (wrt 2)
  :: cexpr "--" (wrt (-2))
  :: vals encodeCharge (\v => \(sk # t) => wrt v t) values
  where
    wrt : Charge -> (sk : SSTCK q) => F1 q SST
    wrt c = writeAs sk.charge c BEnd

bend : List (RExp True, Step q SSz SSTCK)
bend = [cclose ']' bracket]

atom : List (RExp True, Step q SSz SSTCK)
atom = copen' '[' BMass :: vals encodeAtom onAtom subset

ring : List (RExp True, Step q SSz SSTCK)
ring = vals interpolate onRing values

bond : List (RExp True, Step q SSz SSTCK)
bond = cexpr '.' dot :: vals interpolate wrt values
  where
    %inline wrt   : SmilesBond -> Step1 q SSz SSTCK
    wrt b = \(sk # t) => writeAs sk.dob (Bnd b) Atom t

    dot : (k : SSTCK q) => F1 q SST
    dot = writeAs k.dob Dot Atom

openClose : List (RExp True, Step q SSz SSTCK)
openClose = [copen '(' opn, cclose ')' cls]
  where
    opn,cls : (k : SSTCK q) => F1 q SST
    opn = read1 k.st >>= \s => writeAs k.st ({stck $= doubleHead} s) NewBranch
    cls = read1 k.st >>= \s => writeAs k.st ({stck $= drop} s) Closed

space : List (RExp True, Step q SSz SSTCK)
space = [conv (plus $ oneof [' ', '\t']) (const end), newline nl end]
  where
    nl : RExp True
    nl = "\r\n" <|> '\n' <|> '\r'

    end : (sk : SSTCK q) => F1 q SST
    end = T1.do
      Nothing <- endGraph sk | Just x => failWith x Err
      pure Chain

smilesTrans : Lex1 q SSz SSTCK
smilesTrans =
  lex1
    [ E Chain     $ dfa (atom ++ space)
    , E Atom      $ dfa atom
    , E SRing     $ dfa (atom ++ ring ++ bond ++ openClose ++ space)
    , E NewBranch $ dfa (atom ++ bond)
    , E Closed    $ dfa (atom ++ bond ++ openClose ++ space)
    , E BMass     $ dfa (mass :: elem)
    , E BElem     $ dfa elem
    , E BChiral   $ dfa (chirality ++ hc ++ chrg ++ bend)
    , E BHCount   $ dfa (hc ++ chrg ++ bend)
    , E BCharge   $ dfa (chrg ++ bend)
    , E BEnd      $ dfa bend
    ]

smilesErr : Arr32 SSz (SSTCK q -> F1 q (BoundedErr SmilesErr))
smilesErr =
  arr32 SSz (unexpected [])
    [ E BMass   $ unclosedIfNLorEOI "[" []
    , E BElem   $ unclosedIfNLorEOI "[" []
    , E BChiral $ unclosedIfNLorEOI "[" []
    , E BHCount $ unclosedIfNLorEOI "[" []
    , E BEnd    $ unclosedIfNLorEOI "[" []
    ]

smilesEOI :
     SST
  -> SSTCK q
  -> F1 q (Either (BoundedErr SmilesErr) (List SmilesGraph))
smilesEOI st sk =
  case st == Chain || st == SRing || st == Closed of
    False => arrFail SSTCK smilesErr st sk
    True  => endGraph sk >>= \case
      Just x  => pure (Left x)
      Nothing => getList sk.stack_ >>= pure . Right

export
smiles : P1 q (BoundedErr SmilesErr) (List SmilesGraph)
smiles = P Chain init smilesTrans snocChunk smilesErr smilesEOI

||| Parses a list of smiles codes separated by whitespace
export %inline
parseSmiles : Origin -> String -> Either SmilesParseErr (List SmilesGraph)
parseSmiles = parseString smiles

test : String -> IO ()
test s =
  case parseSmiles Virtual s of
    Right x => for_ x $ \(G _ g) => putStrLn (pretty interpolate interpolate g)
    Left x  => putStrLn "\{x}"

export
readSmilesFrom :
     {auto has : Has SmilesParseErr es}
  -> Origin
  -> String
  -> ChemRes es SmilesGraph
readSmilesFrom o s =
  case parseSmiles o s of
    Left  x   => Left (inject x)
    Right []  => Right (G 0 empty)
    Right [g] => Right g
    Right _   =>
      Left (inject $ toParseError o s (B (Custom ManyEntries) NoBounds))

export %inline
readSmiles : Has SmilesParseErr es => String -> ChemRes es SmilesGraph
readSmiles = readSmilesFrom Virtual

||| This is a convenience alias `readSmiles`, which can be used
||| to quickly come up with fairly complex molecular graphs.
|||
||| All errors are converted to pretty printed error messages.
export %inline
readSmiles' : String -> Either String SmilesGraph
readSmiles' =
  mapFst (interpolate . project1) . readSmiles {es = [SmilesParseErr]}
