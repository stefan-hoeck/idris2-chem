module Text.Smiles.Lexer

import Chem.Element
import Chem.Types
import Data.Refined
import Derive.Prelude
import Text.Bounds
import Text.Lex.Manual
import Text.Lex.Element
import Text.Smiles.Types

%default total

%language ElabReflection

public export
data SmilesToken : Type where
  PO    : SmilesToken -- '('
  PC    : SmilesToken -- ')'
  UB    : SmilesToken -- '/'
  DB    : SmilesToken -- '\'
  Dot   : SmilesToken
  TBond : Bond -> SmilesToken
  TRing : RingNr -> SmilesToken
  TAtom : Atom -> SmilesToken

%runElab derive "SmilesToken" [Show,Eq]

export
Interpolation SmilesToken where
  interpolate PO  = "("
  interpolate PC  = ")"
  interpolate UB  = "/"
  interpolate DB  = "\\"
  interpolate Dot = "."
  interpolate (TBond x) = "\{x}"
  interpolate (TRing x) = "\{x}"
  interpolate (TAtom x) = "\{x}"

%inline
subset : (e : Elem) -> {auto 0 _ : ValidSubset e False} -> SmilesToken
subset e = TAtom $ SubsetAtom e False

%inline
subsetA : (e : Elem) -> {auto 0 _ : ValidSubset e True} -> SmilesToken
subsetA e = TAtom $ SubsetAtom e True

--------------------------------------------------------------------------------
--          Atoms
--------------------------------------------------------------------------------

fromDigs : Cast Nat b => Nat -> (b -> Maybe a) -> AutoTok Char a
fromDigs k f (x :: xs) =
  if isDigit x then fromDigs (k * 10 + digit x) f xs else case f (cast k) of
    Just v  => Succ v (x::xs)
    Nothing => unknownRange p (x::xs)
fromDigs k f [] = case f (cast k) of
  Just v  => Succ v []
  Nothing => unknownRange p []

maybeFromDigs : Cast Nat b => a -> (b -> Maybe a) -> AutoTok Char a
maybeFromDigs v f (x::xs) =
  if isDigit x then fromDigs (digit x) f xs else Succ v (x::xs)
maybeFromDigs v f [] = Succ v []

strictFromDigs : Cast Nat b => (b -> Maybe a) -> AutoTok Char a
strictFromDigs f (x::xs) =
  if isDigit x then fromDigs (digit x) f xs else unknownRange p xs
strictFromDigs f [] = failEOI p

public export
atom : Atom -> AutoTok Char Atom
atom a (']' :: xs) = Succ a xs
atom _ (x :: xs)   = unknownRange p xs
atom _ []          = failEOI p

public export
charge : Maybe MassNr -> ValidElem -> Chirality -> HCount -> AutoTok Char Atom
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
hcount : Maybe MassNr -> ValidElem -> Chirality -> AutoTok Char Atom
hcount mn e c ('H' :: xs) = case maybeFromDigs 1 refineHCount xs of
  Succ h ys => charge mn e c h ys
  Fail x y z => Fail x y z
hcount mn e c xs = charge mn e c 0 xs

public export
chiral : Maybe MassNr -> ValidElem -> AutoTok Char Atom
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
anyElem : Maybe MassNr -> AutoTok Char Atom
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
bracket : AutoTok Char Atom
bracket xs = case maybeFromDigs Nothing (map Just . refineMassNr) xs of
  Succ mn ys => anyElem mn ys
  Fail x y z => Fail x y z

--------------------------------------------------------------------------------
--          Tokenizer
--------------------------------------------------------------------------------

public export
tok :
     SnocList (SmilesToken,Nat)
  -> (line,column : Nat)
  -> (cs : List Char)
  -> (0 acc : SuffixAcc cs)
  -> Either (Bounded StopReason) (List (SmilesToken,Nat))
tok st l c ('C'::'l'::t) (SA r) = tok (st :< (subset Cl,c)) l (c+2) t r
tok st l c ('C'     ::t) (SA r) = tok (st :< (subset C,c))  l (c+1) t r
tok st l c ('c'     ::t) (SA r) = tok (st :< (subsetA C,c)) l (c+1) t r
tok st l c ('N'     ::t) (SA r) = tok (st :< (subset N,c))  l (c+1) t r
tok st l c ('n'     ::t) (SA r) = tok (st :< (subsetA N,c)) l (c+1) t r
tok st l c ('O'     ::t) (SA r) = tok (st :< (subset O,c))  l (c+1) t r
tok st l c ('o'     ::t) (SA r) = tok (st :< (subsetA O,c)) l (c+1) t r
tok st l c ('F'     ::t) (SA r) = tok (st :< (subset F,c))  l (c+1) t r
tok st l c ('S'     ::t) (SA r) = tok (st :< (subset S,c))  l (c+1) t r
tok st l c ('s'     ::t) (SA r) = tok (st :< (subsetA S,c)) l (c+1) t r
tok st l c ('P'     ::t) (SA r) = tok (st :< (subset P,c))  l (c+1) t r
tok st l c ('p'     ::t) (SA r) = tok (st :< (subsetA P,c)) l (c+1) t r
tok st l c ('I'     ::t) (SA r) = tok (st :< (subset I,c))  l (c+1) t r
tok st l c ('B'::'r'::t) (SA r) = tok (st :< (subset Br,c)) l (c+2) t r
tok st l c ('B'     ::t) (SA r) = tok (st :< (subset B,c))  l (c+1) t r
tok st l c ('b'     ::t) (SA r) = tok (st :< (subsetA B,c)) l (c+1) t r
tok st l c ('['     ::t) (SA r) = case bracket {orig = '[' :: t} t of
  Succ a ys @{p}  => tok (st :< (TAtom a, c)) l (c + toNat p + 1) ys r
  Fail s _ @{e} r => Left (B r $ BS (P l $ toNat s) (P l $ toNat e))
tok st l c ('('     ::t) (SA r) = tok (st :< (PO,c)) l (c+1) t r
tok st l c (')'     ::t) (SA r) = tok (st :< (PC,c)) l (c+1) t r
tok st l c ('='     ::t) (SA r) = tok (st :< (TBond Dbl,c)) l (c+1) t r
tok st l c ('#'     ::t) (SA r) = tok (st :< (TBond Trpl,c)) l (c+1) t r
tok st l c ('$'     ::t) (SA r) = tok (st :< (TBond Quad,c)) l (c+1) t r
tok st l c ('-'     ::t) (SA r) = tok (st :< (TBond Sngl,c)) l (c+1) t r
tok st l c (':'     ::t) (SA r) = tok (st :< (TBond Arom,c)) l (c+1) t r
tok st l c ('.'     ::t) (SA r) = tok (st :< (Dot,c)) l (c+1) t r
tok st l c ('/'     ::t) (SA r) = tok (st :< (UB,c)) l (c+1) t r
tok st l c ('\\'    ::t) (SA r) = tok (st :< (DB,c)) l (c+1) t r
tok st l c ('0'     ::t) (SA r) = tok (st :< (TRing 0,c)) l (c+1) t r
tok st l c ('1'     ::t) (SA r) = tok (st :< (TRing 1,c)) l (c+1) t r
tok st l c ('2'     ::t) (SA r) = tok (st :< (TRing 2,c)) l (c+1) t r
tok st l c ('3'     ::t) (SA r) = tok (st :< (TRing 3,c)) l (c+1) t r
tok st l c ('4'     ::t) (SA r) = tok (st :< (TRing 4,c)) l (c+1) t r
tok st l c ('5'     ::t) (SA r) = tok (st :< (TRing 5,c)) l (c+1) t r
tok st l c ('6'     ::t) (SA r) = tok (st :< (TRing 6,c)) l (c+1) t r
tok st l c ('7'     ::t) (SA r) = tok (st :< (TRing 7,c)) l (c+1) t r
tok st l c ('8'     ::t) (SA r) = tok (st :< (TRing 8,c)) l (c+1) t r
tok st l c ('9'     ::t) (SA r) = tok (st :< (TRing 9,c)) l (c+1) t r
tok st l c ('%'::x::y::t) (SA r) =
  if isDigit x && isDigit y then
    case refineRingNr (cast $ digit x * 10 + digit y) of
      Just rn => tok (st :< (TRing rn, c)) l (c+3) t r
      Nothing => Left (B UnknownToken $ BS (P l c) (P l $ c + 3))
  else Left (B UnknownToken $ BS (P l c) (P l $ c + 3))
tok st l c (x       ::t) (SA r) = Left (B UnknownToken $ oneChar (P l c))
tok st l c []               _   = Right (st <>> [])

public export
lexSmiles :
     (line : Nat)
  -> String
  -> Either (Bounded StopReason) (List (SmilesToken,Nat))
lexSmiles l s = tok [<] l 0 (unpack s) suffixAcc
