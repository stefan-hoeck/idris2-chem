module Text.Molfile.Reader.Util

import public Text.Molfile.Reader.Error
import public Text.Molfile.Types
import public Text.Parse.Manual
import Text.Lex.Manual.Syntax

%default total

public export
0 WeakTok : Type -> Type
WeakTok a =
     {orig   : List Char}
  -> (cs     : List Char)
  -> {auto p : Suffix False cs orig}
  -> Result False Char orig Error a

err :
     {orig   : List Char}
  -> (cs     : List Char)
  -> {auto p : Suffix False cs orig}
  -> Either Error a
  -> Result False Char orig Error a
err cs (Left x)  = Fail Same cs x
err cs (Right x) = Succ x cs

-- todo: Simplify
molLine' : SnocList Char -> WeakTok MolLine
molLine' sc (x :: xs) = case isControl x of
  False => molLine' (sc :< x) xs
  True  => case refineMolLine (pack $ sc <>> []) of
    Just ml => Succ ml (x::xs)
    Nothing => range (Custom EHeader) p (x::xs)
molLine' sc []        = case refineMolLine (pack $ sc <>> []) of
  Just ml => Succ ml []
  Nothing => range (Custom EHeader) p []

export
molLine : Tok False MolFileError MolLine
molLine [] = Succ "" []
molLine (x :: xs) = case isControl x of
  True  => Succ "" (x::xs)
  False => molLine' [<x] xs

dropSpaces : a -> Nat -> WeakTok a
dropSpaces v 0     xs        = Succ v xs
dropSpaces v (S k) (' '::xs) = dropSpaces v k xs
dropSpaces v (S k) (x::xs)   = unknown p
dropSpaces v (S k) []        = Succ v []

eat : SnocList Char -> Nat -> (SnocList Char -> Either Error a) -> WeakTok a
eat sc 0 f cs = err cs (f sc)
eat sc (S k) f (' '::cs) = case f sc of
  Right v => dropSpaces v k cs
  Left  e => range e p cs
eat sc (S k) f (c::cs) = eat (sc :< c) k f cs
eat sc (S k) f []      = err [] (f sc)

trim' : Nat -> (SnocList Char -> Either Error a) -> WeakTok a
trim' (S k) f (' '::xs) = trim' k f xs
trim' n     f xs        = eat [<] n f xs

export %inline
trim : Nat -> (SnocList Char -> Either Error a) -> Tok False MolFileError a
trim n f cs = trim' n f cs

toNat : List Char -> Nat -> (Nat -> Maybe a) -> List Char -> Either Error a
toNat orig k f []        = case f k of
  Just v  => Right v
  Nothing => Left (OutOfBounds $ Left $ show k)
toNat orig k f (x :: xs) =
  if isDigit x then toNat orig (k*10 + digit x) f xs
  else Left (Unknown $ Left $ pack orig)

toInt : (Integer -> Maybe a) -> List Char -> Either Error a
toInt f ('-' :: xs) = toNat ('-'::xs) 0 (f . negate . cast) xs
toInt f xs          = toNat xs 0 (f . cast) xs

export %inline
nat : Nat -> (Nat -> Maybe a) -> Tok False MolFileError a
nat n f = trim n (\sc => let cs := sc <>> [] in toNat cs 0 f cs)

export %inline
int : Nat -> (Integer -> Maybe a) -> Tok False MolFileError a
int n f = trim n (toInt f . (<>> []))

drop' : (n : Nat) -> WeakTok ()
drop' 0     cs        = Succ () cs
drop' (S k) (x :: xs) = drop' k xs
drop' _     []        = Succ () []

export %inline
drop : (n : Nat) -> Tok False MolFileError ()
drop n cs = drop' n cs
