module Text.Smiles.Lexer

import Chem
import Derive.Prelude
import Text.Lex.Element
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
  bond   : Maybe Bond

%runElab derive "Ring" [Show,Eq]

public export
rnChars : RingNr -> Nat
rnChars rn = if rn < 10 then 1 else 3

public export
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
  TB  : Bond -> SmilesToken
  TA  : Atom -> List Ring -> SmilesToken

%runElab derive "SmilesToken" [Show,Eq]

export
Interpolation SmilesToken where
  interpolate PO        = "("
  interpolate PC        = ")"
  interpolate Dot       = "."
  interpolate (TB x)    = "\{x}"
  interpolate (TA x rs) = "\{x}\{fastConcat $ map interpolate rs}"

public export
0 LexErr : Type
LexErr = ParseError Void SmilesErr

public export
0 Err : Type
Err = ParseError SmilesToken SmilesErr

public export
ringBounds : Nat -> RingNr -> Bounds
ringBounds k rn = BS (P 0 $ k `minus` rnChars rn) (P 0 k)

-- TODO: This is not perfect since there are different encodings
--       for the same bracket atom. A better option would perhaps
--       be to include the string length in the `Bracket` data
--       constructor.
public export
bounds : SmilesToken -> Nat -> Bounds
bounds t k = BS (P 0 k) (P 0 $ k + length "\{t}")

%inline
subset : (e : Elem) -> {auto 0 _ : ValidSubset e False} -> SmilesToken
subset e = TA (SubsetAtom e False) []

%inline
subsetA : (e : Elem) -> {auto 0 _ : ValidSubset e True} -> SmilesToken
subsetA e = TA (SubsetAtom e True) []

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

public export
atom : Atom -> AutoTok e Atom
atom a (']' :: xs) = Succ a xs
atom _ (x :: xs)   = single (Expected $ Left "]") p
atom _ []          = eoiAt p

public export
charge : Maybe MassNr -> ValidElem -> Chirality -> HCount -> AutoTok e Atom
charge mn e c h ('+' :: t) = case t of
  '+'::t  => atom (bracket mn e c h 2) t
  t       => case maybeFromDigs 1 refineCharge t of
    Succ ch ys => atom (bracket mn e c h ch) ys
    Fail x y z => Fail x y z
charge mn e c h ('-' :: t) = case t of
  '-'::t  => atom (bracket mn e c h (-2)) t
  t       => case maybeFromDigs (-1) (refineCharge . negate) t of
    Succ ch ys => atom (bracket mn e c h ch) ys
    Fail x y z => Fail x y z
charge mn e c h t = atom (bracket mn e c h 0) t

public export
hcount : Maybe MassNr -> ValidElem -> Chirality -> AutoTok e Atom
hcount mn e c ('H' :: xs) = case maybeFromDigs 1 refineHCount xs of
  Succ h ys => charge mn e c h ys
  Fail x y z => Fail x y z
hcount mn e c xs = charge mn e c 0 xs

public export
chiral : Maybe MassNr -> ValidElem -> AutoTok e Atom
chiral mn e ('@' :: xs) = case xs of
  '@'          ::t => hcount mn e CW t
  'T'::'H'::'1'::t => hcount mn e TH1 t
  'T'::'H'::'2'::t => hcount mn e TH2 t
  'A'::'L'::'1'::t => hcount mn e AL1 t
  'A'::'L'::'2'::t => hcount mn e AL2 t
  'S'::'P'::'1'::t => hcount mn e SP1 t
  'S'::'P'::'2'::t => hcount mn e SP2 t
  'S'::'P'::'3'::t => hcount mn e SP3 t
  'T'::'B'::     t => case strictFromDigs refineTBIx t of
    Succ x ys  => hcount mn e (TB x) ys
    Fail x y z => Fail x y z
  'O'::'H'::     t => case strictFromDigs refineOHIx t of
    Succ x ys  => hcount mn e (OH x) ys
    Fail x y z => Fail x y z
  t                => hcount mn e CCW t
chiral mn e xs = hcount mn e None xs

public export
anyElem : Maybe MassNr -> AutoTok e Atom
anyElem mn ('c'     ::t) = chiral mn (VE C True) t
anyElem mn ('b'     ::t) = chiral mn (VE B True) t
anyElem mn ('n'     ::t) = chiral mn (VE N True) t
anyElem mn ('o'     ::t) = chiral mn (VE O True) t
anyElem mn ('p'     ::t) = chiral mn (VE P True) t
anyElem mn ('s'::'e'::t) = chiral mn (VE Se True) t
anyElem mn ('s'     ::t) = chiral mn (VE S True) t
anyElem mn ('a'::'s'::t) = chiral mn (VE As True) t
anyElem mn xs = case autoTok {orig} lexElement xs of
  Succ e ys                => chiral mn (VE e False) ys
  Fail start errEnd reason => Fail start errEnd reason

public export
bracket : AutoTok e Atom
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

public export
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
  Succ a ys @{p}  => tok (st :< (TA a [], c)) (c + toNat p) ys r
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
  tok (st :< (TA a (R rn Nothing :: rs),x)) c cs acc
rng (st :< (TA a rs,x):< (TB b, y)) c rn cs acc =
  tok (st :< (TA a (R rn (Just b) :: rs),x)) c cs acc
rng st c rn cs acc = Left (unexpectedRing c rn)

public export
lexSmiles : String -> Either (Bounded LexErr) (List (SmilesToken,Nat))
lexSmiles s = tok [<] 0 (unpack s) suffixAcc
