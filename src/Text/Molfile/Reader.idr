module Text.Molfile.Reader

import Data.List.Quantifiers.Extra
import Data.Nat
import Data.String
import Data.Vect
import Text.Lex.Manual.Syntax
import public Text.Molfile.Reader.Types

%default total

--------------------------------------------------------------------------------
--          Properties
--------------------------------------------------------------------------------

0 Prop : Nat -> Type
Prop k = (Fin k, MolAtom -> MolAtom)

-- applyProps : Props k -> Fin k -> MolAtom -> MolAtom
-- applyProps []            _ a = a
-- applyProps ((x,f) :: ps) y a =
--   let a' := if x == y then f a else a
--    in applyProps ps y a'
--
-- modGraph : {k : _} -> Props k -> IGraph k b MolAtom -> IGraph k b MolAtom
-- modGraph [] x      = x
-- modGraph ps (IG x) = IG $ mapWithIndex (map . applyProps ps) x
--
-- repeat : Nat -> Tok b MolFileError a -> List a -> Tok False MolFileError (List a)
-- repeat 0     f xs cs = Succ xs cs
-- repeat (S k) f xs cs = case f cs of
--   Succ x2 cs2 @{p} => weaken $ trans (repeat k f (x2 :: xs) cs2) p
--   Fail x y z       => Fail x y z
--
-- charge : {k : _} -> Tok False MolFileError (Prop k)
-- charge = Tok.do
--   n <- node {k} 4
--   c <- int 4 (refineCharge . cast)
--   pure $ (n, {charge := c})
--
-- %inline
-- setMass : MassNr -> Isotope -> Isotope
-- setMass v = {mass := Just v}

-- iso : {k : _} -> Tok False MolFileError (Prop k)
-- iso = Tok.do
--   n <- node {k} 4
--   v <- nat 4 (refineMassNr . cast)
--   pure $ (n, {elem $= setMass v})

-- n8 : List a -> Tok False MolFileError a -> Tok False MolFileError (List a)
-- n8 xs f = Tok.do
--   n  <- nat 3 (\n => if 1 <= n && n <= 8 then Just n else Nothing)
--   g2 <- repeat n f xs
--   pure g2

property : {k : _} -> Tok False MolFileError (Prop k)
-- property ps ('M'::' '::' '::'C'::'H'::'G'::t) = succF $ n8 ps charge t
-- property ps ('M'::' '::' '::'I'::'S'::'O'::t) = succF $ n8 ps iso t
-- property ps cs = fail Same

--------------------------------------------------------------------------------
--          Reading
--------------------------------------------------------------------------------

||| General format:
|||   aaabbblllfffcccsssxxxrrrpppiiimmmvvvvvv
|||     3  3  3  3  3  3  3  3  3  3  3     6
|||     3  3     6
|||
|||   aaa    : number of atoms
|||   bbb    : number of bonds
|||   ccc    : chiral flag
|||   vvvvvv : version
|||
||| The other fields are obsolete or no longer supported
||| and are being ignored by the parser.
export
counts : Tok False MolFileError Counts
counts = Tok.do
  ac <- count
  bc <- count
  drop 3
  cf <- trim 3 chiralFlag
  drop 21
  v  <- trim 6 version
  pure $ MkCounts ac bc cf v

||| General format:
|||   xxxxx.xxxxyyyyy.yyyyzzzzz.zzzz aaaddcccssshhhbbbvvvHHHrrriiimmmnnneee
|||
|||   x,y,z : coordinates
|||   aaa   : atom symbol
|||   dd    : mass difference (superseded by M ISO line)
|||   ccc   : charge (superseded by M RAD and M CHG lines)
|||   sss   : atom stereo parity
|||   hhh   : hydrogen count + 1
|||   bbb   : stereo care box
|||   vvv   : valence
|||   HHH   : H0 designator
|||
|||   r and i are not used and ignored
export
atom : Tok False MolFileError MolAtom
atom = Tok.do
  pos   <- coords
  i     <- (trim 4 isotope)
  drop 2
  c     <- nat 3 $ refineCharge . cast
  drop 30
  pure $ MkAtom i c pos NoRadical () () () ()

||| General format:
|||   111222tttsssxxxrrrccc
|||
|||   111 and 222 : atom references
|||   ttt         : bond type
|||   sss         : bond stereo
|||   rrr         : bond topology
|||   ccc         : reacting center status
|||
|||   xxx is not used and ignored
export
bond : {k : _} -> Tok False MolFileError (Edge k MolBond)
bond = Tok.do
  x  <- node {k} 3
  y  <- node {k} 3
  t  <- trim 3 bondType
  s  <- trim 3 bondStereo
  drop 9
  edge x y $ MkBond (x < y) t s

export
lineTok :
     (line : Nat)
  -> Tok b MolFileError a
  -> String
  -> Either (Bounded Error) a
lineTok l f s = case f (unpack s) of
  Succ val []           => Right val
  Succ val (x::xs) @{p} =>
    Left $ oneChar (Unexpected $ Left $ show x) (P l $ toNat p)
  Fail x y z  => Left $ boundedErr (P l 0) x y z

%inline
right : Ur (IArray k (Adj k x y)) -@ Ur (Either e (IGraph k x y))
right (MkBang u) = MkBang (Right $ IG u)

properties :
     {k : _}
  -> (line  : Nat)
  -> (lines : List String)
  -> MArray k (Adj k MolBond MolAtom)
  -@ Ur (Either (Bounded Error) (IGraph k MolBond MolAtom))
properties l []               m = right (freeze m)
properties l ("M  END" :: ss) m = right (freeze m)
properties l (s        :: ss) m =
  case lineTok l property s of
    Right ps2 => ?rightCase
    Left err  => discarding m $ MkBang $ Left err

bonds :
     {k : _}
  -> (n, line : Nat)
  -> (lines   : List String)
  -> MArray k (Adj k MolBond MolAtom)
  -@ Ur (Either (Bounded Error) (IGraph k MolBond MolAtom))
bonds 0     l ss      m = properties l ss m
bonds (S k) l (s::ss) m =
  case lineTok l bond s of
    Right (E x y b) =>
      let m2 := modify x {neighbours $= insert y b} m
          m3 := modify y {neighbours $= insert x b} m2
       in bonds k (S k) ss m3
    Left err        => discarding m $ MkBang $ Left err
bonds (S k) l []      m = discarding m $ MkBang $ Left (oneChar EOI $ P l 0)

atoms :
     {k : _}
  -> (n, line, nbonds : Nat)
  -> {auto ix : Ix n k}
  -> (lines        : List String)
  -> MArray k (Adj k MolBond MolAtom)
  -@ Ur (Either (Bounded Error) (IGraph k MolBond MolAtom))
atoms 0     l bs ss      m  = bonds bs l ss m
atoms (S v) l bs (s::ss) m =
  case lineTok l atom s of
    Right a  =>
      let m2 := modifyIx v {label := a} m
       in atoms v (S l) bs ss m2
    Left err => discarding m $ MkBang $ Left err
atoms (S v) l bs [] m = discarding m $ MkBang $ Left (oneChar EOI $ P l 0)

adjIni : Adj k MolBond MolAtom
adjIni = A (cast Elem.C) empty

readMol' : (ls : List String) -> Either (Bounded Error) Molfile
readMol' (h1::h2::h3::cs::t) = do
  name    <- lineTok 0 molLine h1
  info    <- lineTok 1 molLine h2
  comment <- lineTok 2 molLine h3
  counts  <- lineTok 3 counts cs
  g       <- unrestricted $ alloc counts.atoms adjIni (atoms counts.atoms 4 counts.bonds t)
  pure $ MkMolfile name info comment (G counts.atoms g)
readMol' ls = Left (B (Custom EHeader) $ BS begin (P (length ls) 0))

export %inline
readMol : Has MolParseErr es => Origin -> String -> ChemRes es Molfile
readMol o s = mapFst (inject . fromBounded s o) . readMol' $ lines s
