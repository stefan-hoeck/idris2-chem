module Text.Molfile.Reader

import Chem
import Data.List.Quantifiers
import Data.Nat
import Data.Vect
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

%runElab derive "MolFileError" [Show,Eq]


public export
0 Err : Type
Err = ParseError Void MolFileError

--------------------------------------------------------------------------------
--          Reading
--------------------------------------------------------------------------------

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

%inline
atomRef : Tok True e AtomRef
atomRef = nat 3 (refineAtomRef . cast)

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
atom =
  Tok.[|
    (\cs,a,d,c,s,h,b,v,h0,_,m,n,e => MkAtom cs a d c s h b v h0 m n e)
    coords
    symbol
    (int 2 $ refineMassDiff . cast)
    (nat 3 $ refineAtomCharge . cast)
    stereoParity
    (nat 3 $ refineHydrogenCount . cast)
    stereoCareBox
    (nat 3 $ refineValence. cast)
    h0designator
    (drop 6)
    atomRef
    invRetentionFlag
    exactChangeFlag
  |]

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
bond : Tok True e Bond
bond =
  Tok.[|
    (\r1,r2,t,s,_,r,c => MkBond r1 r2 t s r c)
    atomRef
    atomRef
    bondType
    bondStereo
    (drop 3)
    bondTopo
    reactingCenterStatus
  |]
--
-- readN :  {n : _}
--       -> (String -> Either String a)
--       -> List String
--       -> Either String (Vect n a, List String)
-- readN read = go n
--   where go : (k : Nat) -> List String -> Either String (Vect k a, List String)
--         go Z ss           = Right ([], ss)
--         go (S k) []       = Left "Unexpected end of input"
--         go (S k) (h :: t) = do
--           va        <- read h
--           (vt,rest) <- go k t
--           pure (va :: vt, rest)
--
-- readProps : List String -> Either String (List Property)
-- readProps []         = Left "Unexpected end of mol file"
-- readProps ["M  END"] = Right []
-- readProps (x :: xs)  = do
--   p1 <- readMsg x
--   t  <- readProps xs
--   pure $ p1 :: t
--
--
-- molLines : List String -> Either String MolFile
-- molLines (n :: i :: c :: cnt :: t) = do
--   name    <- readMsg n
--   info    <- readMsg i
--   comm    <- readMsg c
--   cnts    <- counts cnt
--   (as,t1) <- readN atom t
--   (bs,t2) <- readN bond t1
--   ps      <- readProps t2
--   pure (MkMolFile name info comm cnts as bs ps)
-- molLines _ = Left "Unexpected end of input"
--
-- export
-- mol : String -> Either String MolFile
-- mol = molLines . lines

export
runTok : Tok b MolFileError a -> String -> Either (Bounded Err) a
runTok f s = case f (unpack s) of
  Succ val []           => Right val
  Succ val (x::xs) @{p} =>
    Left $ boundedErr begin (weaken p) xs (Unexpected $ Left $ show x)
  Fail x y z  => Left $ boundedErr begin x y z
