module Text.Molfile.Reader.Util

import Data.Either
import public Text.Molfile.Reader.Error
import public Text.Molfile.Types
import Text.Lex.Manual

%default total

public export
0 Parser : Type -> Type
Parser a = List Char -> Either MolErr (List Char, a) 

export %inline
(>>=) : Parser a -> (a -> Parser b) -> Parser b
(>>=) f g cs =
  case f cs of
    Right (cs2,va) => g va cs2
    Left err       => Left err

export %inline
(>>) : Parser () -> Parser a -> Parser a
(>>) f g = f >>= const g

export %inline
pure : a -> Parser a
pure v cs = Right (cs,v)

export
(<*>) : Parser (a -> b) -> Parser a -> Parser b
(<*>) f g cs =
  case f cs of
    Right (cs2,h) => map h <$> g cs2
    Left err      => Left err

export %inline
packChars : Parser String
packChars cs = Right ([], pack cs)

export
repeat : (n : Nat) -> Parser a -> SnocList a -> Parser (List a)
repeat 0     f sv cs = Right (cs,sv <>> [])
repeat (S k) f sv cs =
  case f cs of
    Right (cs2,v) => repeat k f (sv :< v) cs2
    Left err      => Left err

toML : List Char -> SnocList Char -> Either MolErr (List Char, MolLine)
toML cs = map (cs,) . maybeToEither EHeader . refineMolLine . pack . (<>> [])

export
molLine : Parser MolLine
molLine = go [<]
  where
    go : SnocList Char -> Parser MolLine
    go sc [] = toML [] sc
    go sc l@(x::xs) = if isControl x then toML l sc else go (sc:<x) xs

eat : SnocList Char -> Nat -> (SnocList Char -> Either MolErr a) -> Parser a
eat sc 0 f cs = map (cs,) (f sc)
eat sc (S k) f (' '::cs) = (drop k cs, ) <$> f sc
eat sc (S k) f (c::cs)   = eat (sc :< c) k f cs
eat sc (S k) f []        = map ([],) (f sc)

export
trim : Nat -> (SnocList Char -> Either MolErr a) -> Parser a
trim (S k) f (' '::xs) = trim k f xs
trim n     f xs        = eat [<] n f xs

toNat : List Char -> Nat -> (Nat -> Maybe a) -> List Char -> Either MolErr a
toNat orig k f [] = case f k of
  Just v  => Right v
  Nothing => Left (EOutOfBounds k)
toNat orig k f (x :: xs) =
  if isDigit x then toNat orig (k*10 + digit x) f xs
  else Left (EInvalid $ pack orig)

toInt : (Integer -> Maybe a) -> List Char -> Either MolErr a
toInt f ('-' :: xs) = toNat ('-'::xs) 0 (f . negate . cast) xs
toInt f xs          = toNat xs 0 (f . cast) xs

toSigned : List Char -> Either MolErr (Bool,Nat)
toSigned ('-' :: xs) = toNat ('-'::xs) 0 (Just . (True,)) xs
toSigned xs          = toNat xs 0 (Just . (False,)) xs

export %inline
nat : Nat -> (Nat -> Maybe a) -> Parser a
nat n f = trim n (\sc => let cs := sc <>> [] in toNat cs 0 f cs)

export %inline
int : Nat -> (Integer -> Maybe a) -> Parser a
int n f = trim n (toInt f . (<>> []))

export
signed : Nat -> Parser (Bool,Nat)
signed n = trim n (toSigned . (<>> []))

export %inline
dropN : (n : Nat) -> Parser ()
dropN n cs = Right (drop n cs, ())

export
radical : Parser Radical
radical =
  trim 4 $ \case
    [<'1'] => Right Singlet
    [<'2'] => Right Doublet
    [<'3'] => Right Triplet
    [<'0'] => Right NoRadical
    sc     => packError sc ERadical
