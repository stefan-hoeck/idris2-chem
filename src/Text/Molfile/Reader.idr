module Text.Molfile.Reader

import Chem
import Data.List.Quantifiers
import Data.Nat
import Data.Vect
import Decidable.HDec.Integer
import Derive.Prelude
import Text.Lex.Element
import Text.Lex.Manual.Syntax
import Text.Parse.Manual
import public Text.Molfile.Float
import public Text.Molfile.Types

%default total
%language ElabReflection

public export
data MolFileError : Type where
  InvalidEdge   : MolFileError
  InvalidHeader : MolFileError

%runElab derive "MolFileError" [Show,Eq]

export
Interpolation MolFileError where
  interpolate InvalidEdge   = "Invalid bond"
  interpolate InvalidHeader = "Invalid mol-File header"


public export
0 Err : Type
Err = ParseError Void MolFileError

--------------------------------------------------------------------------------
--          Reading
--------------------------------------------------------------------------------

molLine' : SnocList Char -> AutoTok MolFileError MolLine
molLine' sc (x :: xs) = case isControl x of
  False => molLine' (sc :< x) xs
  True  => case refineMolLine (pack $ sc <>> []) of
    Just ml => Succ ml (x::xs)
    Nothing => range (Custom InvalidHeader) p (x::xs)
molLine' sc []        = case refineMolLine (pack $ sc <>> []) of
  Just ml => Succ ml []
  Nothing => range (Custom InvalidHeader) p []

molLine : Tok False MolFileError MolLine
molLine [] = Succ "" []
molLine (x :: xs) = case isControl x of
  True  => Succ "" (x::xs)
  False => weaken $ molLine' [<x] xs

dropSpaces : a -> Nat -> AutoTok e a
dropSpaces v 0     xs        = Succ v xs
dropSpaces v (S k) (' '::xs) = dropSpaces v k xs
dropSpaces v (S k) (x::xs)   = unknown p
dropSpaces v (S k) []        = eoiAt p

eat :
     SnocList Char
  -> Nat
  -> (SnocList Char -> Maybe a)
  -> AutoTok e a
eat sc 0 f cs = case f sc of
  Just v => Succ v cs
  Nothing => unknownRange p cs
eat sc (S k) f (' '::cs) = case f sc of
  Just v  => dropSpaces v k cs
  Nothing => unknownRange p cs
eat sc (S k) f (c::cs) = eat (sc :< c) k f cs
eat sc (S k) f []      = eoiAt p

trimmed' : (n : Nat) -> (SnocList Char -> Maybe a) -> AutoTok e a
trimmed' (S k) f (' '::xs) = trimmed' k f xs
trimmed' n     f xs        = eat [<] n f xs

trimmed :
     (n : Nat)
  -> {auto 0 p : IsSucc n}
  -> (SnocList Char -> Maybe a)
  -> Tok True e a
trimmed (S k) f (' '::cs) = trimmed' k f cs
trimmed (S k) f (c::cs)   = eat [<c] k f cs
trimmed (S k) f []        = eoiAt Same


toNat : Nat -> (Nat -> Maybe a) -> List Char -> Maybe a
toNat k f []        = f k
toNat k f (x :: xs) = if isDigit x then toNat (k*10 + digit x) f xs else Nothing

toInt : (Integer -> Maybe a) -> List Char -> Maybe a
toInt f ('-' :: xs) = toNat 0 (f . negate . cast) xs
toInt f xs          = toNat 0 (f . cast) xs

%inline
nat : (n : Nat) -> {auto 0 p : IsSucc n} -> (Nat -> Maybe a) -> Tok True e a
nat n f = trimmed n (toNat 0 f . (<>> []))

%inline
int : (n : Nat) -> {auto 0 p : IsSucc n} -> (Integer -> Maybe a) -> Tok True e a
int n f = trimmed n (toInt f . (<>> []))

drop' : (n : Nat) -> AutoTok e ()
drop' (S k) (x :: xs) = drop' k xs
drop' 0     xs        = Succ () xs
drop' _     []        = eoiAt p

drop : (n : Nat) -> {auto 0 p : IsSucc n} -> Tok True e ()
drop (S k) (x :: xs) = drop' k xs
drop _     []        = eoiAt Same

chiral : Tok True e ChiralFlag
chiral = trimmed 3 $ \case
  [<]    => Just NonChiral
  [<'0'] => Just NonChiral
  [<'1'] => Just Chiral
  _      => Nothing

version : Tok True e MolVersion
version = trimmed 6 $ \case
  [<'v','2','0','0','0'] => Just V2000
  [<'V','2','0','0','0'] => Just V2000
  [<'v','3','0','0','0'] => Just V3000
  [<'V','3','0','0','0'] => Just V3000
  _                      => Nothing

dot : Tok True e ()
dot ('.'::xs) = Succ () xs
dot (x::xs)   = single (Expected $ Left ".") Same
dot []        = eoiAt Same

coord : Tok True e Coordinate
coord cs = case Tok.[| coord (int 5 Just) dot (nat 4 Just) |] cs of
  Succ (Just v) xs      => Succ v xs
  Succ Nothing  xs @{p} => unknownRange p xs
  Fail x y z            => Fail x y z
  where
    coord : Integer -> () -> Nat -> Maybe Coordinate
    coord i _ k = refineFloat (cast i) (cast k)

coords : Tok True e (Vect 3 Coordinate)
coords = Tok.[| (\x,y,z => [x,y,z]) coord coord coord |]

-- Atom references go from 1 to 999, which means the corresponding
-- nodes go from 0 to 998.
toAtomRef : Nat -> Maybe Node
toAtomRef (S k) = if k < 999 then Just $ cast k else Nothing
toAtomRef 0     = Nothing

%inline
node : (n : Nat) -> { auto 0 p : IsSucc n} -> Tok True e Node
node n = nat n toAtomRef

%inline
count : Tok True e Nat
count = nat 3 Just

symbol : Tok True e AtomSymbol
symbol = trimmed 4 $ \sc => case readElement (pack $ sc <>> []) of
  Just el => Just $ El el
  Nothing => case sc of
    [<'L']     => Just L
    [<'A']     => Just A
    [<'Q']     => Just Q
    [<'*']     => Just Ast
    [<'L','P'] => Just LP
    [<'R','#'] => Just RSharp
    _          => Nothing

stereoParity     : Tok True e StereoParity
stereoParity = trimmed 3 $ \case
  [<'0'] => Just NoStereo
  [<'1'] => Just OddStereo
  [<'2'] => Just EvenStereo
  [<'3'] => Just AnyStereo
  [<]    => Just NoStereo
  _      => Nothing

stereoCareBox    : Tok True e StereoCareBox
stereoCareBox = trimmed 3 $ \case
  [<]    => Just IgnoreStereo
  [<'0'] => Just IgnoreStereo
  [<'1'] => Just MatchStereo
  _      => Nothing

h0designator    : Tok True e H0Designator
h0designator = trimmed 3 $ \case
  [<]    => Just H0NotSpecified
  [<'0'] => Just H0NotSpecified
  [<'1'] => Just NoHAllowed
  _      => Nothing

invRetentionFlag : Tok True e InvRetentionFlag
invRetentionFlag = trimmed 3 $ \case
  [<]    => Just InvNotApplied
  [<'0'] => Just InvNotApplied
  [<'1'] => Just ConfigInverted
  [<'2'] => Just ConfigRetained
  _      => Nothing

exactChangeFlag  : Tok True e ExactChangeFlag
exactChangeFlag = trimmed 3 $ \case
  [<]    => Just ChangeNotApplied
  [<'0'] => Just ChangeNotApplied
  [<'1'] => Just ExactChange
  _      => Nothing

bondType : Tok True e BondType
bondType = trimmed 3 $ \case
  [<'1']     => Just Single
  [<'2']     => Just Dbl
  [<'3']     => Just Triple
  [<'4']     => Just Aromatic
  [<'5']     => Just SngOrDbl
  [<'6']     => Just SngOrAromatic
  [<'7']     => Just DblOrAromatic
  [<'8']     => Just AnyBond
  _          => Nothing

bondStereo : Tok True e BondStereo
bondStereo = trimmed 3 $ \case
  [<]        => Just NoBondStereo
  [<'0']     => Just NoBondStereo
  [<'1']     => Just Up
  [<'3']     => Just CisOrTrans
  [<'4']     => Just UpOrDown
  [<'6']     => Just Down
  _          => Nothing

bondTopo : Tok True e BondTopo
bondTopo = trimmed 3 $ \case
  [<]        => Just AnyTopology
  [<'0']     => Just AnyTopology
  [<'1']     => Just Ring
  [<'2']     => Just Chain
  _          => Nothing

reactingCenterStatus : Tok True e ReactingCenterStatus
reactingCenterStatus = trimmed 3 $ \case
  [<]        => Just Unmarked
  [<'0']     => Just Unmarked
  [<'-','1'] => Just NotACenter
  [<'1']     => Just Center
  [<'2']     => Just NoChange
  [<'4']     => Just BondMadeBroken
  [<'8']     => Just BondOrderChange
  [<'1','2'] => Just BondMBAndOC
  [<'5']     => Just CenterBMB
  [<'9']     => Just CenterBOC
  [<'1','3'] => Just CenterBMBAndOC
  _          => Nothing

edge : Tok True MolFileError Edge
edge cs = case Tok.[| mkEdge (node 3) (node 3) |] cs of
  Succ (Just v) cs2             => Succ v cs2
  Succ Nothing  cs2 @{Uncons _} => Fail Same cs2 (Custom InvalidEdge)
  Fail x y z                    => Fail x y z

rpairs : {n : _} -> Tok b e a -> Tok False e (Vect n (Node,a))
rpairs {n = 0}   f cs = Succ [] cs
rpairs {n = S k} f cs =
  weaken $ Tok.[| (\x,y,z => (x,y)::z) (node 4) f (rpairs f) |] cs

repeat : Nat -> (a -> Tok b e a) -> a -> Tok False e a
repeat 0     f x cs = Succ x cs
repeat (S k) f x cs = case f x cs of
  Succ x2 cs2 @{p} => weaken $ trans (repeat k f x2 cs2) p
  Fail x y z       => Fail x y z

charge : Graph Bond Atom -> Tok True MolFileError (Graph Bond Atom)
charge (MkGraph g) = Tok.do
  n <- node 4
  c <- nat 4 (refineCharge . cast)
  pure $ MkGraph $ update n (map {charge := c}) g

iso : Graph Bond Atom -> Tok True MolFileError (Graph Bond Atom)
iso (MkGraph g) = Tok.do
  n <- node 4
  v <- nat 4 (refineMassNr . cast)
  pure $ MkGraph $ update n (map {massNr := Just v}) g

n8 :
     Graph Bond Atom
  -> (Graph Bond Atom -> Tok True MolFileError (Graph Bond Atom))
  -> Tok True MolFileError (Graph Bond Atom)
n8 g f = Tok.do
  n  <- nat 3 (\n => if 1 <= n && n <= 8 then Just n else Nothing)
  g2 <- repeat n f g
  pure g2

property : Graph Bond Atom -> Tok True MolFileError (Graph Bond Atom)
property g ('M'::' '::' '::'C'::'H'::'G'::t) = succT $ n8 g charge t
property g ('M'::' '::' '::'I'::'S'::'O'::t) = succT $ n8 g iso t
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
counts : Tok True e Counts
counts = Tok.[| mkCounts count count (drop 3) chiral (drop 21) version |]
  where
    mkCounts : Nat -> Nat -> () -> ChiralFlag -> () -> MolVersion -> Counts
    mkCounts ac bc _ cf _ v = MkCounts ac bc cf v

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
atom : Tok True e Atom
atom = Tok.do
  cs <- coords
  a  <- symbol
  drop 2
  c  <- nat 3 $ refineCharge . cast
  s  <- stereoParity
  h  <- nat 3 $ refineHydrogenCount . cast
  b  <- stereoCareBox
  v  <- nat 3 $ refineValence. cast
  h0 <- h0designator
  drop 6
  m  <- node 3
  n  <- invRetentionFlag
  e  <- exactChangeFlag
  pure $ MkAtom cs a Nothing c s h b v h0 m n e

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
bond : Tok True MolFileError (LEdge Bond)
bond = Tok.do
  ed <- edge
  t  <- bondType
  s  <- bondStereo
  drop 3
  r  <- bondTopo
  c  <- reactingCenterStatus
  pure $ MkLEdge ed $ MkBond t s r c

export
lineTok :
     (line : Nat)
  -> Tok b MolFileError a
  -> String
  -> Either (Bounded Err) a
lineTok l f s = case f (unpack s) of
  Succ val []          => Right val
  Succ val ['\n']      => Right val
  Succ val ['\r','\n'] => Right val
  Succ val (x::xs) @{p} =>
    Left $ oneChar (Unexpected $ Left $ show x) (P l $ toNat p)
  Fail x y z  => Left $ boundedErr (P l 0) x y z

properties :
     Graph Bond Atom
  -> (line  : Nat)
  -> (lines : List String)
  -> Either (Bounded Err) (Graph Bond Atom)
properties g l []        = Right g
properties g l (s :: ss) =
  if isPrefixOf "M  END" s then Right g
  else case lineTok l (property g) s of
         Right g2 => properties g2 (S l) ss
         Left err => Left err

bonds :
     Graph Bond Atom
  -> (nbonds, line : Nat)
  -> (lines        : List String)
  -> Either (Bounded Err) (Graph Bond Atom)
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
  -> Either (Bounded Err) (Graph Bond Atom)
atoms g 0     bs l n ss      = bonds g bs l ss
atoms g (S k) bs l n (s::ss) = case lineTok l atom s of
  Right a  => atoms (insNode n a g) k bs (S l) (n+1) ss
  Left err => Left err
atoms g (S k) bs l n [] = Left (oneChar EOI $ P l 0)

readMol : (ls : List String) -> Either (Bounded Err) MolFile
readMol (h1::h2::h3::cs::t) = do
  name    <- lineTok 0 molLine h1
  info    <- lineTok 1 molLine h2
  comment <- lineTok 2 molLine h3
  counts  <- lineTok 3 counts cs
  g       <- atoms empty counts.atoms counts.bonds 4 0 t
  pure $ MkMolFile name info comment g
readMol ls = Left (B (Custom InvalidHeader) $ BS begin (P (length ls) 0))
