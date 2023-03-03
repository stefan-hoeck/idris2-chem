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
charge mn (VE e a) c h ('+' :: t) = case t of
  '+'::t  => atom (Bracket mn e a c h 2) t
  t       => case maybeFromDigs 1 refineCharge t of
    Succ ch ys => atom (Bracket mn e a c h ch) ys
    Fail x y z => Fail x y z
charge mn (VE e a) c h ('-' :: t) = case t of
  '-'::t  => atom (Bracket mn e a c h (-2)) t
  t       => case maybeFromDigs (-1) (refineCharge . negate) t of
    Succ ch ys => atom (Bracket mn e a c h ch) ys
    Fail x y z => Fail x y z
charge mn (VE e a) c h t = case maybeFromDigs 0 refineCharge t of
    Succ ch ys => atom (Bracket mn e a c h ch) ys
    Fail x y z => Fail x y z

public export
hcount : Maybe MassNr -> ValidElem -> Chirality -> AutoTok Char Atom
hcount mn e c ('H' :: xs) = case maybeFromDigs 0 refineHCount xs of
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

-- public export
-- tok :
--      SnocList (Bounded SmilesToken)
--   -> Position
--   -> (cs : List Char)
--   -> (0 acc : SuffixAcc cs)
--   -> Either StopReason (List (Bounded SmilesToken))
-- tok st p ('C'::'l'::t) (SA r) = tok (TAtom $ SubsetAtom Cl False) t
-- tok st p ('B'::'r'::t) (SA r) = tok (TAtom $ SubsetAtom Br False) t
-- tok st p ('C'     ::t) (SA r) = tok (TAtom $ SubsetAtom C False) t
-- tok st p ('c'     ::t) (SA r) = tok (TAtom $ SubsetAtom C True) t
-- tok st p ('N'     ::t) (SA r) = tok (TAtom $ SubsetAtom N False) t
-- tok st p ('n'     ::t) (SA r) = tok (TAtom $ SubsetAtom N True) t
-- tok st p ('O'     ::t) (SA r) = tok (TAtom $ SubsetAtom O False) t
-- tok st p ('o'     ::t) (SA r) = tok (TAtom $ SubsetAtom O True) t
-- tok st p ('F'     ::t) (SA r) = tok (TAtom $ SubsetAtom F False) t
-- tok st p ('S'     ::t) (SA r) = tok (TAtom $ SubsetAtom S False) t
-- tok st p ('s'     ::t) (SA r) = tok (TAtom $ SubsetAtom S True) t
-- tok st p ('P'     ::t) (SA r) = tok (TAtom $ SubsetAtom P False) t
-- tok st p ('p'     ::t) (SA r) = tok (TAtom $ SubsetAtom P True) t
-- tok st p ('I'     ::t) (SA r) = tok (TAtom $ SubsetAtom I False) t
-- tok st p ('B'     ::t) (SA r) = tok (TAtom $ SubsetAtom B False) t
-- tok st p ('b'     ::t) (SA r) = tok (TAtom $ SubsetAtom B True) t
-- tok st p ('['     ::t) (SA r) = TAtom <$> bracket t
-- tok st p ('('     ::t) (SA r) = Succ PO t
-- tok st p (')'     ::t) (SA r) = Succ PC t
-- tok st p ('='     ::t) (SA r) = Succ (TBond $ Dbl) t
-- tok st p ('#'     ::t) (SA r) = Succ (TBond $ Trpl) t
-- tok st p ('$'     ::t) (SA r) = Succ (TBond $ Quad) t
-- tok st p ('-'     ::t) (SA r) = Succ (TBond $ Sngl) t
-- tok st p (':'     ::t) (SA r) = Succ (TBond $ Arom) t
-- tok st p ('.'     ::t) (SA r) = Succ Dot t
-- tok st p ('/'     ::t) (SA r) = Succ UB t
-- tok st p ('\\'    ::t) (SA r) = Succ DB t
-- tok st p ('0'     ::t) (SA r) = Succ (TRing 0) t
-- tok st p ('1'     ::t) (SA r) = Succ (TRing 1) t
-- tok st p ('2'     ::t) (SA r) = Succ (TRing 2) t
-- tok st p ('3'     ::t) (SA r) = Succ (TRing 3) t
-- tok st p ('4'     ::t) (SA r) = Succ (TRing 4) t
-- tok st p ('5'     ::t) (SA r) = Succ (TRing 5) t
-- tok st p ('6'     ::t) (SA r) = Succ (TRing 6) t
-- tok st p ('7'     ::t) (SA r) = Succ (TRing 7) t
-- tok st p ('8'     ::t) (SA r) = Succ (TRing 8) t
-- tok st p ('9'     ::t) (SA r) = Succ (TRing 9) t
-- tok st p ('%'     ::t) (SA r) = TRing <$> strictFromDigs refineRingNr t
-- tok st p (x       ::t) (SA r) = ?unknownCase
-- tok st p []                   = Succ (st <>> [])
