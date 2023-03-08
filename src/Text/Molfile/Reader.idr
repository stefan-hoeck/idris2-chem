module Text.Molfile.Reader

import Data.List.Quantifiers
import Data.Nat
import Data.Vect
import Text.Parse.Manual
import public Text.Molfile.Float
import public Text.Molfile.Types

%default total

public export
data MolFileError : Type where


public export
0 Err : Type
Err = ParseError Char MolFileError

--------------------------------------------------------------------------------
--          Reading
--------------------------------------------------------------------------------

-- TODO: Part of this stuff should to to the parser lib

||| Result of running a (strict) tokenizer.
public export
0 WeakTok : (a : Type) -> Type
WeakTok a =
     {cs : List Char}
  -> (ts : List Char)
  -> {auto p : Suffix False ts cs}
  -> WeakRes Char cs a

dropSpaces : a -> Nat -> WeakTok a
dropSpaces v 0 xs = Succ v xs
dropSpaces v (S k) (' '::xs) = dropSpaces v k xs
dropSpaces v (S k) (x::xs)   = unknown xs
dropSpaces v (S k) []        = failEOI p

trimmed : (Nat -> WeakTok a) -> Nat -> WeakTok a
trimmed f (S k) (' '::xs) = trimmed f k xs
trimmed f n     xs        = case f n xs @{Same} of
  Succ va ys @{q} =>
    let n' := n `minus` toNat q
     in dropSpaces va n' ys @{trans q p}
  Fail x y z      => Fail (trans x p) y z

nat : (acc : Nat) -> (rem : Nat) -> (Nat -> Maybe a) -> WeakTok a
nat acc (S k) f (x :: xs) =
  if isDigit x then nat (digit x + acc * 10) k f xs else case f acc of
    Just v  => Succ v xs
    Nothing => unknownRange p xs
nat acc 0 f xs = case f acc of
  Just v  => Succ v xs
  Nothing => unknownRange p xs
nat acc (S k) f [] = failEOI p

int : (rem : Nat) -> (Integer -> Maybe a) -> WeakTok a
int (S $ S k) f ('-' :: x::xs) =
  if isDigit x then nat (digit x) k (f . negate . cast) xs
  else unknownRange p xs
int (S k) f (x::xs) =
  if isDigit x then nat (digit x) k (f . cast) xs
  else unknownRange p xs
int (S k) f [] = failEOI p
int 0 f xs     = nat 0 0 (f . cast) xs

drop : (n : Nat) -> WeakTok ()
drop (S k) (x :: xs) = drop k xs
drop 0     xs        = Succ () xs
drop _     []        = failEOI p

-- -- TODO: This should go to the parser library.
-- toks :
--      All (Tok Char) ts
--   -> (cs : List Char)
--   -> Result (not (null ts)) Char cs StopReason (All (Prelude.id) ts)
-- toks [] cs = Succ [] cs
-- toks (tk :: tks) cs =
--   let Succ v  cs2 @{p1} := tk cs | Fail x y z => Fail x y z
--       Succ vs cs3 @{p2} := toks tks cs2
--         | Fail x y z => Fail (weaken $ trans x p1) y z
--    in Succ (v::vs) cs3 @{orTrue $ trans p2 p1}
--
-- chiral : Tok Char ChiralFlag
-- chiral = nat 3 $ \case
--   0 => Just NonChiral
--   1 => Just Chiral
--   _ => Nothing
--
-- version : Tok Char MolVersion
-- version (' '::'v'::'2'::'0'::'0'::'0'::t) = Succ V2000 t
-- version (' '::'V'::'2'::'0'::'0'::'0'::t) = Succ V2000 t
-- version (' '::'v'::'3'::'0'::'0'::'0'::t) = Succ V3000 t
-- version (' '::'V'::'3'::'0'::'0'::'0'::t) = Succ V3000 t
-- version (x::xs)                           = unknown xs
-- version []                                = failEmpty
--
-- dot : Tok Char ()
-- dot ('.'::xs) = Succ () xs
-- dot (x::xs)   = unknown xs
-- dot []        = failEmpty
--
-- coord : Tok Char Coordinate
-- coord cs = case toks [int 5 Just, dot, nat 4 Just] cs of
--   Succ [x,_,y] r @{p} => case refineFloat (cast x) (cast y) of
--     Just f  => Succ f r
--     Nothing => unknown r @{weaken p}
--   Fail x y z => Fail x y z
--
-- coords : Tok Char (Vect 3 Coordinate)
-- coords cs = (\[x,y,z] => [x,y,z]) <$> toks [coord,coord,coord] cs
--
-- --------------------------------------------------------------------------------
-- --          Reading
-- --------------------------------------------------------------------------------
--
-- ||| General format:
-- |||   aaabbblllfffcccsssxxxrrrpppiiimmmvvvvvv
-- |||     3  3  3  3  3  3  3  3  3  3  3     6
-- |||
-- |||   aaa    : number of atoms
-- |||   bbb    : number of bonds
-- |||   ccc    : chiral flag
-- |||   vvvvvv : version
-- |||
-- ||| The other fields are obsolete or no longer supported
-- ||| and are being ignored by the parser.
-- export
-- counts : Tok Char Counts
-- counts cs =
--   (\[ac,bc,_,chi,_,v] => MkCounts ac bc chi v) <$>
--   toks [nat 3 Just, nat 3 Just, drop 6, chiral, drop 18, version] cs
--
-- ||| Chunks of an atom line. See `atom` for a description
-- ||| of the format and types of chunks.
-- public export
-- atomChunks : Vect 16 Int
-- atomChunks = [10,10,10,4,2,3,3,3,3,3,3,3,3,3,3,3]
--
-- ||| General format:
-- |||   xxxxx.xxxxyyyyy.yyyyzzzzz.zzzz aaaddcccssshhhbbbvvvHHHrrriiimmmnnneee
-- |||
-- |||   x,y,z : coordinates
-- |||   aaa   : atom symbol
-- |||   dd    : mass difference (superseded by M ISO line)
-- |||   ccc   : charge (superseded by M RAD and M CHG lines)
-- |||   sss   : atom stereo parity
-- |||   hhh   : hydrogen count + 1
-- |||   bbb   : stereo care box
-- |||   vvv   : valence
-- |||   HHH   : H0 designator
-- |||
-- |||   r and i are not used and ignored
-- export
-- atom : String -> Either String Atom
-- atom s = do
--   [x,y,z,a,d,c,s,h,b,v,h0,_,_,m,n,e] <- trimmedChunks atomChunks s
--   [| MkAtom (readMsg x) (readMsg y) (readMsg z) (readMsg a) (readMsg d) (readMsg c)
--             (readMsg s) (readMsg h) (readMsg b) (readMsg v) (readMsg h0)
--             (readMsg m) (readMsg n) (readMsg e) |]
--
-- ||| Chunks of a bond line. See `bond` for a description
-- ||| of the format and types of chunks.
-- export
-- bondChunks : Vect 7 Int
-- bondChunks = [3,3,3,3,3,3,3]
--
-- ||| General format:
-- |||   111222tttsssxxxrrrccc
-- |||
-- |||   111 and 222 : atom references
-- |||   ttt         : bond type
-- |||   sss         : bond stereo
-- |||   rrr         : bond topology
-- |||   ccc         : reacting center status
-- |||
-- |||   xxx is not used and ignored
-- export
-- bond : String -> Either String Bond
-- bond s = do
--   [r1,r2,t,ss,r,_,c] <- trimmedChunks bondChunks s
--   [| MkBond (readMsg r1) (readMsg r2) (readMsg t) (readMsg ss) (readMsg r) (readMsg c) |]
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
--
-- --------------------------------------------------------------------------------
-- --          Writing
-- --------------------------------------------------------------------------------
--
-- export
-- writeChunks : Vect n Int -> Vect n String -> String
-- writeChunks = go ""
--   where go : String -> Vect k Int -> Vect k String -> String
--         go res [] []               = res
--         go res (x :: xs) (y :: ys) =
--           go (res ++ padLeft (cast x) ' ' y) xs ys
--
-- export
-- writeCounts : Counts -> String
-- writeCounts (MkCounts a b c v) =
--   writeChunks countChunks
--     [write a,write b,"0","0",write c,"0","0","0","0","0","0", write v]
--
-- export
-- writeAtom : Atom -> String
-- writeAtom (MkAtom x y z a d c s h b v h0 m n e) =
--   writeChunks atomChunks
--     [ write x, write y, write z, write a, write d, write c
--     , write s, write h, write b, write v, write h0, "0", "0", write m, write n
--     , write e]
--
-- export
-- writeBond : Bond -> String
-- writeBond (MkBond r1 r2 t ss r c) =
--   writeChunks bondChunks
--     [write r1, write r2, write t, write ss, write r, "0", write c]
--
-- export
-- writeMol : MolFile -> String
-- writeMol (MkMolFile n i c cnts as bs ps) =
--   fastUnlines $  [value n, value i, value c, writeCounts cnts]
--               ++ toList (map writeAtom as)
--               ++ toList (map writeBond bs)
--               ++ map write ps
--               ++ ["M  END"]
