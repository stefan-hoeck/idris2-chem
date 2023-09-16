module Text.Smiles.Parser

import Chem
import Data.List.Quantifiers.Extra
import Derive.Prelude
import Text.Parse.Manual
import Text.Smiles.Lexer
import Text.Smiles.Types

%default total
%language ElabReflection

--------------------------------------------------------------------------------
--          Types
--------------------------------------------------------------------------------

public export
record SmilesParseErr where
  constructor SPE
  smiles  : String
  context : FileContext
  error   : Err

export
fromBounded : String -> Origin -> Bounded Err -> SmilesParseErr
fromBounded s o (B v bs) = SPE s (FC o bs) v

%runElab derive "SmilesParseErr" [Eq,Show]

export
Interpolation SmilesParseErr where
  interpolate (SPE s c e) = printParseError s c e

record RingInfo (k : Nat) where
  constructor R
  orig   : Fin k
  atom   : SmilesAtom
  bond   : Maybe SmilesBond
  column : Nat

record AtomInfo (k : Nat) where
  constructor A
  orig   : Fin k
  atom   : SmilesAtom
  column : Nat

0 Atoms : Nat -> Type
Atoms k = Vect k SmilesAtom

0 Rings : Nat -> Type
Rings k = List (RingNr, RingInfo k)

0 Bonds : Nat -> Type
Bonds k = List (Edge k SmilesBond)

0 Stack : Nat -> Type
Stack = List . AtomInfo

lookupRing : RingNr -> Rings k -> Maybe (RingInfo k)
lookupRing r []        = Nothing
lookupRing r (x :: xs) = case compare r (fst x) of
  LT => Nothing
  EQ => Just (snd x)
  GT => lookupRing r xs

insert : RingNr -> RingInfo k -> Rings k -> Rings k
insert r i []        = [(r,i)]
insert r i (x :: xs) = case compare r (fst x) of
  LT => (r,i) :: x :: xs
  _  => x :: insert r i xs

delete : RingNr -> Rings k -> Rings k
delete r []        = []
delete r (x :: xs) = case compare r (fst x) of
  LT => x :: delete r xs
  EQ => xs
  GT => x :: delete r xs

--------------------------------------------------------------------------------
--          Weakenings
--------------------------------------------------------------------------------

-- All weakening functions should be optimized away by the
-- Idris compiler. It is paramount to test this by parsing a
-- huge SMILES string, to make sure the SMILES parser runs in
-- linear time.

wring : RingInfo k -> RingInfo (S k)
wring (R o a b c) = R (weaken o) a b c

watom : AtomInfo k -> AtomInfo (S k)
watom (A o a b) = A (weaken o) a b

wrings : Rings k -> Rings (S k)
wrings []     = []
wrings ((n,h)::t) = (n, wring h) :: wrings t

wbonds : Bonds k -> Bonds (S k)
wbonds []         = []
wbonds (h::t) = weakenEdge h :: wbonds t

wstack : Stack k -> Stack (S k)
wstack []     = []
wstack (h::t) = watom h :: wstack t

--------------------------------------------------------------------------------
--          Parser
--------------------------------------------------------------------------------

addBond : {k : _} -> Fin k -> SmilesBond -> Bonds (S k) -> Bonds (S k)
addBond n1 b es = edge n1 b :: es

waddBond : {k : _} -> Fin k -> SmilesBond -> Bonds k -> Bonds (S k)
waddBond n1 b es = addBond n1 b (wbonds es)

bond : SmilesAtom -> SmilesAtom -> SmilesBond
bond x y = if isArom x && isArom y then Arom else Sngl

ringBond : (b,c : Maybe SmilesBond) -> (x,y : SmilesAtom) -> Maybe SmilesBond
ringBond Nothing Nothing   x y = Just $ bond x y
ringBond Nothing (Just x)  _ _ = Just x
ringBond (Just x) Nothing  _ _ = Just x
ringBond (Just x) (Just y) _ _ = if x == y then Just x else Nothing

bondError : (column : Nat) -> RingNr -> Either (Bounded Err) a
bondError c rn = custom (ringBounds c rn) RingBondMismatch

rings :
     {k : _}
  -> (column : Nat)
  -> SmilesAtom
  -> SnocList Ring
  -> Stack k
  -> Rings k
  -> Rings (S k)
  -> Atoms k
  -> Bonds (S k)
  -> (ts   : List (SmilesToken,Nat))
  -> Either (Bounded Err) SmilesMol

finalize :
     {k : _}
  -> Stack k
  -> Rings k
  -> Atoms k
  -> Bonds k
  -> Either (Bounded Err) SmilesMol
finalize (A _ _ c :: xs) _       _  _  = unclosed (oneChar (P 0 c)) PO
finalize [] ((r,R _ _ _ c) :: _) _  _  = custom (ringBounds c r) UnclosedRing
finalize [] []                   as bs = Right $ G k (mkGraphRev as bs)

-- We just got a fresh atom. Now come the optional ring bonds and branches.
-- branched_atom ::= atom ringbond* branch*
chain :
     {k    : Nat}
  -> (orig : Fin k)         -- the node we bind to
  -> (a    : SmilesAtom)    -- the atom we bind to
  -> (s    : Stack k)       -- stack of open branches
  -> (r    : Rings k)       -- list of opened ring bonds
  -> (as   : Atoms k)       -- accumulated atoms
  -> (bs   : Bonds k)       -- accumulated bonds
  -> (ts   : List (SmilesToken,Nat))
  -> Either (Bounded Err) SmilesMol
chain o a s r as bs [] = finalize s r as bs
chain o a s r as bs ((x,c)::xs) = case x of
  TA a2 rs => rings c a2 rs s r (wrings r) as (waddBond o (bond a a2) bs) xs

  PC => case s of
    A o2 a2 _ :: t => chain o2 a2 t r as bs xs
    []             => unexpected (B PC $ bounds PC c)

  PO => case xs of
    (TB b, _) :: (TA a2 rs,d) :: t =>
      rings d a2 rs (A o a c :: s) r (wrings r) as (waddBond o b bs) t
    (TA a2 rs,d) :: t =>
      rings d a2 rs (A o a c :: s) r (wrings r) as (waddBond o (bond a a2) bs) t
    _ => custom (bounds x c) ExpectedAtomOrBond

  TB b  => case xs of
    (TA a2 rs,d) :: t => rings d a2 rs s r (wrings r) as (waddBond o b bs) t
    _ => custom (bounds x c) ExpectedAtomOrRing

  Dot => case xs of
    (TA a2 rs,d) :: t => rings d a2 rs s r (wrings r) as (wbonds bs) t
    ((t,c)::_)     => custom (bounds t c) ExpectedAtom
    []             => eoi

rings c a [<]             s wr r as bs ts = chain last a (wstack s) r (a::as) bs ts
rings c a (xs :< R rn mb) s wr r as bs ts =
  let c1 := c + ringChars (R rn mb)
   in case lookupRing rn wr of
        Nothing => rings c1 a xs s wr (insert rn (R last a mb c1) r) as bs ts
        Just (R n a2 mb2 c2) =>
          let Just b := ringBond mb mb2 a a2 | Nothing => bondError c1 rn
              r2     := delete rn r
           in rings c1 a xs s wr r2 as (addBond n b bs) ts

start : List (SmilesToken,Nat) -> Either (Bounded Err) SmilesMol
start ((TA a rs,c) :: xs) = rings c a rs [] [] [] [] [] xs
start []                  = Right (G 0 empty)
start ((t,c) :: _)        = custom (bounds t c) ExpectedAtom

export
readSmilesFrom : Has SmilesParseErr es => Origin -> String -> ChemRes es SmilesMol
readSmilesFrom o s =
  let Right ts := lexSmiles s
        | Left e => Left $ inject (fromBounded s o (voidLeft <$> e))
      Right m  := start ts
        | Left e => Left $ inject (fromBounded s o e)
   in Right m

export %inline
readSmiles : Has SmilesParseErr es => String -> ChemRes es SmilesMol
readSmiles = readSmilesFrom Virtual
