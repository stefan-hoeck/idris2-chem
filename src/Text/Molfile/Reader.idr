module Text.Molfile.Reader

import Data.Nat
import Data.String
import Data.Vect
import Text.Lex.Manual.Syntax
import public Text.Molfile.Reader.Types

%default total

--------------------------------------------------------------------------------
--          Properties
--------------------------------------------------------------------------------


repeat : Nat -> (a -> Tok b MolFileError a) -> a -> Tok False MolFileError a
repeat 0     f x cs = Succ x cs
repeat (S k) f x cs = case f x cs of
  Succ x2 cs2 @{p} => weaken $ trans (repeat k f x2 cs2) p
  Fail x y z       => Fail x y z

charge : Graph Bond Atom -> Tok False MolFileError (Graph Bond Atom)
charge (MkGraph g) = Tok.do
  n <- node 4
  c <- nat 4 (refineCharge . cast)
  pure $ MkGraph $ update n (map {charge := c}) g

iso : Graph Bond Atom -> Tok False MolFileError (Graph Bond Atom)
iso (MkGraph g) = Tok.do
  n <- node 4
  v <- nat 4 (refineMassNr . cast)
  pure $ MkGraph $ update n (map {massNr := Just v}) g

n8 :
     Graph Bond Atom
  -> (Graph Bond Atom -> Tok False MolFileError (Graph Bond Atom))
  -> Tok False MolFileError (Graph Bond Atom)
n8 g f = Tok.do
  n  <- nat 3 (\n => if 1 <= n && n <= 8 then Just n else Nothing)
  g2 <- repeat n f g
  pure g2

property : Graph Bond Atom -> Tok False MolFileError (Graph Bond Atom)
property g ('M'::' '::' '::'C'::'H'::'G'::t) = succF $ n8 g charge t
property g ('M'::' '::' '::'I'::'S'::'O'::t) = succF $ n8 g iso t
property g cs = fail Same

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
bond : Tok False MolFileError (LEdge Bond)
bond = Tok.do
  ed <- edge
  t  <- trim 3 bondType
  s  <- trim 3 bondStereo
  drop 3
  r  <- trim 3 bondTopo
  drop 3
  pure $ MkLEdge ed $ MkBond t s r

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
     Graph Bond Atom
  -> (line  : Nat)
  -> (lines : List String)
  -> Either (Bounded Error) (Graph Bond Atom)
properties g l []               = Right g
properties g l ("M  END" :: ss) = Right g
properties g l (s        :: ss) = case lineTok l (property g) s of
  Right g2 => properties g2 (S l) ss
  Left err => Left err

bonds :
     Graph Bond Atom
  -> (nbonds, line : Nat)
  -> (lines        : List String)
  -> Either (Bounded Error) (Graph Bond Atom)
bonds g 0     l ss      = properties g l ss
bonds g (S k) l (s::ss) = case lineTok l bond s of
  Right e  => bonds (insEdge e g) k (S l) ss
  Left err => Left err
bonds g (S k) l [] = Left (oneChar EOI $ P l 0)

atoms :
     Graph Bond Atom
  -> (natoms, nbonds, line : Nat)
  -> (node         : Node)
  -> (lines        : List String)
  -> Either (Bounded Error) (Graph Bond Atom)
atoms g 0     bs l n ss      = bonds g bs l ss
atoms g (S k) bs l n (s::ss) = case lineTok l atom s of
  Right a  => atoms (insNode n a g) k bs (S l) (n+1) ss
  Left err => Left err
atoms g (S k) bs l n [] = Left (oneChar EOI $ P l 0)

readMol' : (ls : List String) -> Either (Bounded Error) MolFile
readMol' (h1::h2::h3::cs::t) = do
  name    <- lineTok 0 molLine h1
  info    <- lineTok 1 molLine h2
  comment <- lineTok 2 molLine h3
  counts  <- lineTok 3 counts cs
  g       <- atoms empty counts.atoms counts.bonds 4 0 t
  pure $ MkMolFile name info comment g
readMol' ls = Left (B (Custom EHeader) $ BS begin (P (length ls) 0))

export %inline
readMol : Origin -> String -> Either (FileContext,Error) MolFile
readMol o = mapFst (fromBounded o) . readMol' . lines
