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
Prop k = (Fin k, Atom -> Atom)

0 Props : Nat -> Type
Props = List . Prop

applyProps : Props k -> Fin k -> Atom -> Atom
applyProps []            _ a = a
applyProps ((x,f) :: ps) y a =
  let a' := if x == y then f a else a
   in applyProps ps y a'

modGraph : {k : _} -> Props k -> IGraph k b Atom -> IGraph k b Atom
modGraph [] x      = x
modGraph ps (IG x) = IG $ mapWithIndex (map . applyProps ps) x

repeat : Nat -> Tok b MolFileError a -> List a -> Tok False MolFileError (List a)
repeat 0     f xs cs = Succ xs cs
repeat (S k) f xs cs = case f cs of
  Succ x2 cs2 @{p} => weaken $ trans (repeat k f (x2 :: xs) cs2) p
  Fail x y z       => Fail x y z

charge : {k : _} -> Tok False MolFileError (Prop k)
charge = Tok.do
  n <- node {k} 4
  c <- int 4 (refineCharge . cast)
  pure $ (n, {charge := c})

iso : {k : _} -> Tok False MolFileError (Prop k)
iso = Tok.do
  n <- node {k} 4
  v <- nat 4 (refineMassNr . cast)
  pure $ (n, {massNr := Just v})

n8 : List a -> Tok False MolFileError a -> Tok False MolFileError (List a)
n8 xs f = Tok.do
  n  <- nat 3 (\n => if 1 <= n && n <= 8 then Just n else Nothing)
  g2 <- repeat n f xs
  pure g2

property : {k : _} -> Props k -> Tok False MolFileError (Props k)
property ps ('M'::' '::' '::'C'::'H'::'G'::t) = succF $ n8 ps charge t
property ps ('M'::' '::' '::'I'::'S'::'O'::t) = succF $ n8 ps iso t
property ps cs = fail Same

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
atom : Tok False MolFileError Atom
atom = Tok.do
  cs <- coords
  a  <- (trim 4 atomSymbol)
  drop 2
  c  <- nat 3 $ refineCharge . cast
  s  <- trim 3 stereoParity
  h  <- nat 3 $ refineHydrogenCount . cast
  b  <- trim 3 stereoCareBox
  v  <- nat 3 $ refineValence. cast
  h0 <- trim 3 h0designator
  drop 15
  pure $ MkAtom cs a Nothing c s h b v h0

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
bond : {k : _} -> Tok False MolFileError (Edge k Bond)
bond = Tok.do
  x  <- node {k} 3
  y  <- node {k} 3
  t  <- trim 3 bondType
  s  <- trim 3 bondStereo
  drop 3
  r  <- trim 3 bondTopo
  drop 3
  edge x y $ MkBond (x < y) t s r

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

properties :
     {k : _}
  -> IGraph k b Atom
  -> Props k
  -> (line  : Nat)
  -> (lines : List String)
  -> Either (Bounded Error) (IGraph k b Atom)
properties g ps l []               = Right (modGraph ps g)
properties g ps l ("M  END" :: ss) = Right (modGraph ps g)
properties g ps l (s        :: ss) = case lineTok l (property ps) s of
  Right ps2 => properties g ps2 (S l) ss
  Left err  => properties g ps (S l) ss

bonds :
     {k : _}
  -> Vect k Atom
  -> List (Edge k Bond)
  -> (nbonds, line : Nat)
  -> (lines        : List String)
  -> Either (Bounded Error) (IGraph k Bond Atom)
bonds as bs 0     l ss      = properties (mkGraphRev as bs) [] l ss
bonds as bs (S k) l (s::ss) = case lineTok l bond s of
  Right e  => bonds as (e :: bs) k (S l) ss
  Left err => Left err
bonds _ _ (S k) l [] = Left (oneChar EOI $ P l 0)

atoms :
     {k : _}
  -> Vect k Atom
  -> (natoms, nbonds, line : Nat)
  -> (lines        : List String)
  -> Either (Bounded Error) (IGraph (k + natoms) Bond Atom)
atoms as 0     bs l ss      =
  rewrite plusZeroRightNeutral k in bonds as [] bs l ss
atoms as (S v) bs l (s::ss) = case lineTok l atom s of
  Right a  =>
    rewrite sym (plusSuccRightSucc k v) in atoms (a :: as) v bs (S l) ss
  Left err => Left err
atoms as (S k) bs l [] = Left (oneChar EOI $ P l 0)

readMol' : (ls : List String) -> Either (Bounded Error) MolFile
readMol' (h1::h2::h3::cs::t) = do
  name    <- lineTok 0 molLine h1
  info    <- lineTok 1 molLine h2
  comment <- lineTok 2 molLine h3
  counts  <- lineTok 3 counts cs
  g       <- atoms [] counts.atoms counts.bonds 4 t
  pure $ MkMolFile name info comment (G counts.atoms g)
readMol' ls = Left (B (Custom EHeader) $ BS begin (P (length ls) 0))

export %inline
readMol : Has MolParseErr es => Origin -> String -> ChemRes es MolFile
readMol o s = mapFst (inject . fromBounded s o) . readMol' $ lines s
