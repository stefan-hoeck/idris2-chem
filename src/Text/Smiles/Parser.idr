module Text.Smiles.Parser

import Chem
import Data.SortedMap
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
data SmilesErr : Type where
  ExpectedAtom       : SmilesErr
  ExpectedAtomOrRing : SmilesErr
  ExpectedAtomOrBond : SmilesErr
  EmptyParen         : SmilesErr
  RingBondMismatch   : SmilesErr
  UnclosedRing       : SmilesErr

export
Interpolation SmilesErr where
  interpolate ExpectedAtom = "Expected an atom"
  interpolate ExpectedAtomOrRing = "Expected an atom or ring bond"
  interpolate ExpectedAtomOrBond = "Expected an atom or a bond"
  interpolate EmptyParen = "Empty parens"
  interpolate RingBondMismatch = "Ring bonds do not match"
  interpolate UnclosedRing = "Unclosed ring"

public export
0 Err : Type
Err = ParseError SmilesToken SmilesErr

%runElab derive "SmilesErr" [Eq,Show]

record RingInfo where
  constructor R
  orig   : Node
  atom   : Atom
  bond   : Maybe Bond
  column : Nat

record AtomInfo where
  constructor A
  orig   : Node
  atom   : Atom
  column : Nat

0 Rings : Type
Rings = SortedMap RingNr RingInfo

public export
0 Mol : Type
Mol = Graph Bond Atom

-- hopefully, we know what we are doing...
%inline
unsafeEdge : Node -> Node -> Edge
unsafeEdge x y = MkEdge x y (mkLT $ believe_me (Builtin.Refl {x = True}))

%inline
addBond : Node -> Node -> Bond -> Mol -> Mol
addBond n1 n2 b = insEdge $ MkLEdge (unsafeEdge n1 n2) b

%inline
addAtom : Node -> Atom -> Mol -> Mol
addAtom = insNode

--------------------------------------------------------------------------------
--          Parser
--------------------------------------------------------------------------------

bond : Atom -> Atom -> Bond
bond x y = if isArom x && isArom y then Arom else Sngl

ringBond : Maybe Bond -> Maybe Bond -> Atom -> Atom -> Maybe Bond
ringBond Nothing Nothing   x y = Just $ bond x y
ringBond Nothing (Just x)  _ _ = Just x
ringBond (Just x) Nothing  _ _ = Just x
ringBond (Just x) (Just y) _ _ = if x == y then Just x else Nothing

bondError : (column : Nat) -> RingNr -> Either (Bounded Err) a
bondError c x = custom (bounds (TR x) c) RingBondMismatch

ring :
     (col : Nat)
  -> RingNr
  -> Maybe Bond
  -> Node
  -> Atom
  -> Rings
  -> Mol
  -> Either (Bounded Err) (Rings,Mol)
ring col2 r mb2 n2 a2 rs m = case lookup r rs of
  Nothing => Right (insert r (R n2 a2 mb2 col2) rs, m)
  Just (R n a mb c) =>
    let Just b := ringBond mb mb2 a a2 | Nothing => bondError col2 r
        rs2    := delete r rs
        edge   := MkLEdge (unsafeEdge n n2) b
     in Right (rs2, addBond n n2 b m)

-- TODO: We should validate if atoms are aromatic in case of
--       an aromatic bond. But perhaps it is better to do that
--       in the main parser?
%inline
bondTo : Bond -> Node -> Node -> Atom -> Mol -> Mol
bondTo b n1 n2 a2 = addBond n1 n2 b . addAtom n2 a2

finalize : List AtomInfo -> Rings -> Mol -> Either (Bounded Err) Mol
finalize (A _ _ c :: xs) _ _ = unclosed (oneChar (P 0 c)) PO
finalize [] rs m = case SortedMap.toList rs of
  []                 => Right m
  (r,R _ _ _ c) :: _ => custom (bounds (TR r) c) UnclosedRing

-- We just got a fresh atom. Now come the optional ring bonds and branches.
-- branched_atom ::= atom ringbond* branch*
chain :
     (orig : Node)          -- the node we bind to
  -> (a    : Atom)          -- the atom we bind to
  -> (s    : List AtomInfo) -- stack of open branches
  -> (r    : Rings)         -- list of opened ring bonds
  -> (m    : Mol)           -- accumulated molecule
  -> (n    : Node)          -- current node
  -> (ts   : List (SmilesToken,Nat))
  -> Either (Bounded Err) Mol
chain o a s r m n [] = finalize s r m
chain o a s r m n ((x,c)::xs) = case x of
  TA a2 => chain n a2 s r (bondTo (bond a a2) o n a2 m) (n+1) xs
  TB b  => case xs of
    (TA a2,_) :: t => chain n a2 s r (bondTo b o n a2 m) (n+1) t
    (TR ri,c) :: t => case ring c ri (Just b) o a r m of
      Right (r2,m2) => chain o a s r2 m2 n t
      Left err      => Left err
    _ => custom (bounds x c) ExpectedAtomOrRing

  PO => case xs of
    (TB b, _) :: (TA a2,_) :: t =>
      chain n a2 (A o a c :: s) r (bondTo b o n a2 m) (n+1) t
    (TA a2,_) :: t =>
      chain n a2 (A o a c :: s) r (bondTo (bond a a2) o n a2 m) (n+1) t
    _ => custom (bounds x c) ExpectedAtomOrBond

  PC => case s of
    A o2 a2 _ :: t => chain o2 a2 t r m n xs
    []             => unexpected (B PC $ bounds PC c)

  TR ri => case ring c ri Nothing o a r m of
      Right (r2,m2) => chain o a s r2 m2 n xs
      Left err      => Left err

  Dot => case xs of
    (TA a2,_) :: t => chain n a2 s r (addAtom n a2 m) (n+1) t
    ((t,c)::_)     => custom (bounds t c) ExpectedAtom
    []             => eoi

start : List (SmilesToken,Nat) -> Either (Bounded Err) Mol
start ((TA a,_) :: xs) = chain 0 a [] empty (addAtom 0 a empty) 1 xs
start []               = Right empty
start ((t,c) :: _)     = custom (bounds t c) ExpectedAtom

export
parseFrom : Origin -> String -> Either (FileContext,Err) Mol
parseFrom o s =
  let Right ts := lexSmiles s | Left e => Left $ fromBounded o (Reason <$> e)
      Right m  := start ts    | Left e => Left $ fromBounded o e
   in Right m

export %inline
parse : String -> Either (FileContext,Err) Mol
parse = parseFrom Virtual
