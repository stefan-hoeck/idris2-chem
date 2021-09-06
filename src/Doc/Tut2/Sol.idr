module Doc.Tut2.Sol

import Doc.Tut1

%default total

--------------------------------------------------------------------------------
--          Exercise 1
--------------------------------------------------------------------------------

data Expr : (t : Type) -> Type where
  NatLit : (value : Nat)       -> Expr Nat
  StrLit : (value : String)    -> Expr String
  Len    : (val : Expr String) -> Expr Nat
  Add    : (lh : Expr Nat)     -> (rh : Expr Nat) -> Expr Nat
  Mult   : (lh : Expr Nat)     -> (rh : Expr Nat) -> Expr Nat
  IsZero : (val : Expr Nat)    -> Expr Bool
  And    : (lh : Expr Bool)    -> (rh : Expr Bool) -> Expr Bool
  Or     : (lh : Expr Bool)    -> (rh : Expr Bool) -> Expr Bool

eval : Expr t -> t
eval (NatLit v)   = v
eval (StrLit v)   = v
eval (Len val)    = length $ eval val
eval (Add lh rh)  = eval lh + eval rh
eval (Mult lh rh) = eval lh * eval rh
eval (IsZero val) = eval val == 0
eval (And lh rh)  = eval lh && eval rh
eval (Or lh rh)   = eval lh || eval rh

Num (Expr Nat) where
  fromInteger = NatLit . fromInteger
  (+) = Add
  (*) = Mult

FromString (Expr String) where
  fromString = StrLit

--------------------------------------------------------------------------------
--          Exercise 2
--------------------------------------------------------------------------------

data Vect : (n : Nat) -> (a : Type) -> Type where
  Nil  : Vect 0 a
  (::) : (h : a) -> (t : Vect n a) -> Vect (S n) a

drop2 : Vect (S $ S n) a -> Vect n a
drop2 (_ :: _ :: t) = t

drop : (n : Nat) -> Vect (n + m) a -> Vect m a
drop 0     x        = x
drop (S k) (h :: t) = drop k t

take : (n : Nat) -> Vect (n + m) a -> Vect n a
take 0     _        = []
take (S k) (h :: t) = h :: take k t

replicate : (n : Nat) -> (v : a) -> Vect n a
replicate 0     _ = []
replicate (S k) v = v :: replicate k v

iterate : (n : Nat) -> (f : a -> a) -> (ini : a) -> Vect n a
iterate 0     _ _   = []
iterate (S k) f ini = ini :: iterate k f (f ini)

--------------------------------------------------------------------------------
--          Exercise 3
--------------------------------------------------------------------------------

data BaseType = RNA | DNA

data Nucleobase : (t : BaseType) -> Type where
  A : Nucleobase t
  C : Nucleobase t
  G : Nucleobase t
  T : Nucleobase DNA
  U : Nucleobase RNA

DNABase : Type
DNABase = Nucleobase DNA

RNABase : Type
RNABase = Nucleobase RNA

DNASeq : Type
DNASeq = List DNABase

RNASeq : Type
RNASeq = List RNABase

translateBase : DNABase -> RNABase
translateBase A = A
translateBase C = C
translateBase G = G
translateBase T = U
translateBase U impossible

translate : DNASeq -> RNASeq
translate = map translateBase

complementBase : DNABase -> DNABase
complementBase A = T
complementBase C = G
complementBase G = C
complementBase T = A
complementBase U impossible

complement : DNASeq -> DNASeq
complement = map complementBase

readDNABase : Char -> Maybe DNABase
readDNABase 'A' = Just A
readDNABase 'C' = Just C
readDNABase 'G' = Just G
readDNABase 'T' = Just T
readDNABase _   = Nothing

readDNA : String -> Maybe DNASeq
readDNA = traverse readDNABase . unpack
