module Text.Smiles.Lexer

import Chem
import Derive.Prelude
import Text.Lex.Elem
import Text.Parse.Manual
import Text.Smiles.Types

%default total

%language ElabReflection

--------------------------------------------------------------------------------
--          Types
--------------------------------------------------------------------------------

public export
data SmilesErr : Type where
  ExpectedAtom       : SmilesErr
  ExpectedAtomOrRing : SmilesErr
  ExpectedAtomOrBond : SmilesErr
  EmptyParen         : SmilesErr
  UnexpectedRing     : SmilesErr
  RingBondMismatch   : SmilesErr
  UnclosedRing       : SmilesErr

export
Interpolation SmilesErr where
  interpolate ExpectedAtom = "Expected an atom"
  interpolate ExpectedAtomOrRing = "Expected an atom or ring bond"
  interpolate ExpectedAtomOrBond = "Expected an atom or a bond"
  interpolate EmptyParen = "Empty parens"
  interpolate UnexpectedRing = "Unexpected ring token"
  interpolate RingBondMismatch = "Ring bonds do not match"
  interpolate UnclosedRing = "Unclosed ring"

%runElab derive "SmilesErr" [Eq,Show]

public export
record Ring where
  constructor R
  ring   : RingNr
  bond   : Maybe SmilesBond

%runElab derive "Ring" [Show,Eq]

export
rnChars : RingNr -> Nat
rnChars rn = if rn < 10 then 1 else 3

export
ringChars : Ring -> Nat
ringChars (R rn mb) = rnChars rn + maybe 0 (const 1) mb

export
Interpolation Ring where
  interpolate (R r (Just b)) = "\{b}\{r}"
  interpolate (R r Nothing)  = "\{r}"

public export
data SmilesToken : Type where
  PO  : SmilesToken -- '('
  PC  : SmilesToken -- ')'
  Dot : SmilesToken
  TB  : SmilesBond -> SmilesToken
  TA  : SmilesAtom -> SnocList Ring -> SmilesToken

%runElab derive "SmilesToken" [Show,Eq]

export
Interpolation SmilesToken where
  interpolate PO        = "("
  interpolate PC        = ")"
  interpolate Dot       = "."
  interpolate (TB x)    = "\{x}"
  interpolate (TA x rs) = "\{x}\{fastConcat $ map interpolate (rs <>> [])}"

public export
0 LexErr : Type
LexErr = ParseError Void SmilesErr

public export
0 Err : Type
Err = ParseError SmilesToken SmilesErr

export
ringBounds : Nat -> RingNr -> Bounds
ringBounds k rn = BS (P 0 $ k `minus` rnChars rn) (P 0 k)

-- TODO: This is not perfect since there are different encodings
--       for the same bracket atom. A better option would perhaps
--       be to include the string length in the `Bracket` data
--       constructor.
export
bounds : SmilesToken -> Nat -> Bounds
bounds t k = BS (P 0 k) (P 0 $ k + length "\{t}")

%inline
subset : (e : Elem) -> {auto 0 _ : ValidSubset e False} -> SmilesToken
subset e = TA (SubsetAtom e False) [<]

%inline
subsetA : (e : Elem) -> {auto 0 _ : ValidSubset e True} -> SmilesToken
subsetA e = TA (SubsetAtom e True) [<]

--------------------------------------------------------------------------------
--          Atoms
--------------------------------------------------------------------------------

fromDigs : Cast Nat b => Nat -> (b -> Maybe a) -> AutoTok e a
fromDigs k f (x :: xs) =
  if isDigit x then fromDigs (k * 10 + digit x) f xs else case f (cast k) of
    Just v  => Succ v (x::xs)
    Nothing => unknownRange p (x::xs)
fromDigs k f [] = case f (cast k) of
  Just v  => Succ v []
  Nothing => unknownRange p []

maybeFromDigs : Cast Nat b => a -> (b -> Maybe a) -> AutoTok e a
maybeFromDigs v f (x::xs) =
  if isDigit x then fromDigs (digit x) f xs else Succ v (x::xs)
maybeFromDigs v f [] = Succ v []

strictFromDigs : Cast Nat b => (b -> Maybe a) -> AutoTok e a
strictFromDigs f (x::xs) =
  if isDigit x then fromDigs (digit x) f xs else failDigit Dec p
strictFromDigs f [] = eoiAt p

atom : SmilesAtom -> AutoTok e SmilesAtom
atom a (']' :: xs) = Succ a xs
atom _ (x :: xs)   = single (Expected $ Left "]") p
atom _ []          = eoiAt p

charge : AromIsotope -> Chirality -> HCount -> AutoTok e SmilesAtom
charge ai c h ('+' :: t) = case t of
  '+'::t  => atom (bracket ai c h 2) t
  t       => case maybeFromDigs 1 refineCharge t of
    Succ ch ys => atom (bracket ai c h ch) ys
    Fail x y z => Fail x y z
charge ai c h ('-' :: t) = case t of
  '-'::t  => atom (bracket ai c h (-2)) t
  t       => case maybeFromDigs (-1) (refineCharge . negate) t of
    Succ ch ys => atom (bracket ai c h ch) ys
    Fail x y z => Fail x y z
charge ai c h t = atom (bracket ai c h 0) t

hcount : AromIsotope -> Chirality -> AutoTok e SmilesAtom
hcount ai c ('H' :: xs) = case maybeFromDigs 1 refineHCount xs of
  Succ h ys => charge ai c h ys
  Fail x y z => Fail x y z
hcount ai c xs = charge ai c 0 xs

chiral : AromIsotope -> AutoTok e SmilesAtom
chiral ai ('@' :: xs) = case xs of
  '@'          ::t => hcount ai CW t
  'T'::'H'::'1'::t => hcount ai TH1 t
  'T'::'H'::'2'::t => hcount ai TH2 t
  'A'::'L'::'1'::t => hcount ai AL1 t
  'A'::'L'::'2'::t => hcount ai AL2 t
  'S'::'P'::'1'::t => hcount ai SP1 t
  'S'::'P'::'2'::t => hcount ai SP2 t
  'S'::'P'::'3'::t => hcount ai SP3 t
  'T'::'B'::     t => case strictFromDigs refineTBIx t of
    Succ x ys  => hcount ai (TB x) ys
    Fail x y z => Fail x y z
  'O'::'H'::     t => case strictFromDigs refineOHIx t of
    Succ x ys  => hcount ai (OH x) ys
    Fail x y z => Fail x y z
  t                => hcount ai CCW t
chiral ai xs = hcount ai None xs

anyElem : Maybe MassNr -> AutoTok e SmilesAtom
anyElem mn ('c'     ::t) = chiral (MkAI C  mn True) t
anyElem mn ('b'     ::t) = chiral (MkAI B  mn True) t
anyElem mn ('n'     ::t) = chiral (MkAI N  mn True) t
anyElem mn ('o'     ::t) = chiral (MkAI O  mn True) t
anyElem mn ('p'     ::t) = chiral (MkAI P  mn True) t
anyElem mn ('s'::'e'::t) = chiral (MkAI Se mn True) t
anyElem mn ('s'     ::t) = chiral (MkAI S  mn True) t
anyElem mn ('a'::'s'::t) = chiral (MkAI As mn True) t
anyElem mn xs = case autoTok {orig} lexElement xs of
  Succ e ys                => chiral (MkAI e mn False) ys
  Fail start errEnd reason => Fail start errEnd reason

export
bracket : AutoTok e SmilesAtom
bracket xs = case maybeFromDigs Nothing (map Just . refineMassNr) xs of
  Succ mn ys => anyElem mn ys
  Fail x y z => Fail x y z

--------------------------------------------------------------------------------
--          Tokenizer
--------------------------------------------------------------------------------

unknownChars : List Char -> (start : Nat) -> Bounded (ParseError e t)
unknownChars cs s =
  B (Unknown . Left $ pack cs) $ BS (P 0 s) (P 0 $ s + length cs)

unexpectedRing : (end : Nat) -> RingNr -> Bounded LexErr
unexpectedRing s rn = B (Custom UnexpectedRing) $ ringBounds s rn

rng :
     SnocList (SmilesToken,Nat)
  -> (column     : Nat)
  -> (ringNr     : RingNr)
  -> (cs : List Char)
  -> (0 acc : SuffixAcc cs)
  -> Either (Bounded LexErr) (List (SmilesToken,Nat))

tok :
     SnocList (SmilesToken,Nat)
  -> (column : Nat)
  -> (cs : List Char)
  -> (0 acc : SuffixAcc cs)
  -> Either (Bounded LexErr) (List (SmilesToken,Nat))
tok st c ('C'::'l'::t) (SA r) = tok (st :< (subset Cl,c)) (c+2) t r
tok st c ('C'     ::t) (SA r) = tok (st :< (subset C,c))  (c+1) t r
tok st c ('c'     ::t) (SA r) = tok (st :< (subsetA C,c)) (c+1) t r
tok st c ('N'     ::t) (SA r) = tok (st :< (subset N,c))  (c+1) t r
tok st c ('n'     ::t) (SA r) = tok (st :< (subsetA N,c)) (c+1) t r
tok st c ('O'     ::t) (SA r) = tok (st :< (subset O,c))  (c+1) t r
tok st c ('o'     ::t) (SA r) = tok (st :< (subsetA O,c)) (c+1) t r
tok st c ('F'     ::t) (SA r) = tok (st :< (subset F,c))  (c+1) t r
tok st c ('S'     ::t) (SA r) = tok (st :< (subset S,c))  (c+1) t r
tok st c ('s'     ::t) (SA r) = tok (st :< (subsetA S,c)) (c+1) t r
tok st c ('P'     ::t) (SA r) = tok (st :< (subset P,c))  (c+1) t r
tok st c ('p'     ::t) (SA r) = tok (st :< (subsetA P,c)) (c+1) t r
tok st c ('I'     ::t) (SA r) = tok (st :< (subset I,c))  (c+1) t r
tok st c ('B'::'r'::t) (SA r) = tok (st :< (subset Br,c)) (c+2) t r
tok st c ('B'     ::t) (SA r) = tok (st :< (subset B,c))  (c+1) t r
tok st c ('b'     ::t) (SA r) = tok (st :< (subsetA B,c)) (c+1) t r
tok st c ('['     ::t) (SA r) = case bracket {orig = '[' :: t} t of
  Succ a ys @{p}  => tok (st :< (TA a [<], c)) (c + toNat p) ys r
  Fail s _ @{q} r =>
    let c1 := c + toNat s
        c2 := c1 + toNat q
     in Left (B r $ BS (P 0 c1) (P 0 c2))
tok st c ('('     ::t) (SA r) = tok (st :< (PO,c)) (c+1) t r
tok st c (')'     ::t) (SA r) = tok (st :< (PC,c)) (c+1) t r
tok st c ('='     ::t) (SA r) = tok (st :< (TB Dbl,c)) (c+1) t r
tok st c ('#'     ::t) (SA r) = tok (st :< (TB Trpl,c)) (c+1) t r
tok st c ('$'     ::t) (SA r) = tok (st :< (TB Quad,c)) (c+1) t r
tok st c ('-'     ::t) (SA r) = tok (st :< (TB Sngl,c)) (c+1) t r
tok st c (':'     ::t) (SA r) = tok (st :< (TB Arom,c)) (c+1) t r
tok st c ('.'     ::t) (SA r) = tok (st :< (Dot,c)) (c+1) t r
tok st c ('/'     ::t) (SA r) = tok (st :< (TB FW,c)) (c+1) t r
tok st c ('\\'    ::t) (SA r) = tok (st :< (TB BW,c)) (c+1) t r
tok st c ('0'     ::t) (SA r) = rng st (c+1) 0 t r
tok st c ('1'     ::t) (SA r) = rng st (c+1) 1 t r
tok st c ('2'     ::t) (SA r) = rng st (c+1) 2 t r
tok st c ('3'     ::t) (SA r) = rng st (c+1) 3 t r
tok st c ('4'     ::t) (SA r) = rng st (c+1) 4 t r
tok st c ('5'     ::t) (SA r) = rng st (c+1) 5 t r
tok st c ('6'     ::t) (SA r) = rng st (c+1) 6 t r
tok st c ('7'     ::t) (SA r) = rng st (c+1) 7 t r
tok st c ('8'     ::t) (SA r) = rng st (c+1) 8 t r
tok st c ('9'     ::t) (SA r) = rng st (c+1) 9 t r
tok st c ('%'::x::y::t) (SA r) =
  if isDigit x && isDigit y then
    case refineRingNr (cast $ digit x * 10 + digit y) of
      Just rn => rng st (c+3) rn t r
      Nothing => Left $ unknownChars ['%',x,y] c
  else Left $ unknownChars ['%',x] c
tok st c (x       ::t) (SA r) = Left $ unknownChars [x] c
tok st c []               _   = Right (st <>> [])

rng (st :< (TA a rs,x)) c rn cs acc =
  tok (st :< (TA a (rs :< R rn Nothing),x)) c cs acc
rng (st :< (TA a rs,x):< (TB b, y)) c rn cs acc =
  tok (st :< (TA a (rs :< R rn (Just b)),x)) c cs acc
rng st c rn cs acc = Left (unexpectedRing c rn)

export
lexSmiles : String -> Either (Bounded LexErr) (List (SmilesToken,Nat))
lexSmiles s = tok [<] 0 (unpack s) suffixAcc
