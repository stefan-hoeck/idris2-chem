module Doc.Tut3.Sol

import Data.Maybe
import Data.Vect
import Doc.Tut2.Sol

%default total

--------------------------------------------------------------------------------
--          Exercise 1
--------------------------------------------------------------------------------

public export
readRNABase : Char -> Maybe RNABase
readRNABase 'A' = Just A
readRNABase 'C' = Just C
readRNABase 'G' = Just G
readRNABase 'U' = Just U
readRNABase _   = Nothing

public export
readRNA : String -> Maybe RNASeq
readRNA = traverse readRNABase . unpack

public export
fromString : (s : String) -> {auto 0 prf : IsJust (readRNA s)} -> RNASeq
fromString s = fromJust $ readRNA s

public export
anRNASeq : RNASeq
anRNASeq = "CAGGUUUCCGACC"

--------------------------------------------------------------------------------
--          Exercise 2
--------------------------------------------------------------------------------

||| We use a trick here, which allows us to handle this with only a single
||| data constructor: By adding the lengths to the list of indexes,
||| we can declare in the data constructor, that the lengths must actually
||| be identical.
data SameLengthV : (m,n : Nat) -> (as : Vect m a) -> (bs : Vect n b) -> Type where
  OfSameLength : SameLengthV n n as bs

||| This is probably not so easy to get right, so make sure
||| to make use of holes to let the typechecker help you.
||| First and foremost, `SameLengthV` is actually a proof that `m = n`.
||| We make use of this in the pattern matches on `m` and `n`:
||| both are unwrapped to an `S k`, and Idris is able to figure out
||| that the two `k`s are actually identical.
|||
||| Does this mean, that we can do without the vector indices in `SameLengthV`?
||| Yes! See below.
zipWithSLV :  (f : a -> b -> c)
           -> (as : Vect m a)
           -> (bs : Vect n b)
           -> {auto 0 prf : SameLengthV m n as bs}
           -> Vect n c
zipWithSLV _ Nil Nil = Nil
zipWithSLV f (ha :: ta) (hb :: tb) {m = S k} {n = S k} =
  f ha hb :: zipWithSLV f ta tb
zipWithSLV _ Nil (_ :: _) impossible
zipWithSLV _ (_ :: _) Nil impossible

||| Proof that two natural numbers of unknown source are actually equal.
data SameNat : (m,n : Nat) -> Type where
  IsSameNat : SameNat n n

||| The concept of two values being identical is so common
||| that there is a builtin type called `Equal` for this, which
||| comes with an associated infix operator: `=`.
||| We make use of this in `zipWithSLV3`.
zipWithSLV2 :  (f : a -> b -> c)
            -> Vect m a
            -> Vect n b
            -> {auto 0 prf : SameNat m n}
            -> Vect n c
zipWithSLV2 _ Nil Nil = Nil
zipWithSLV2 f (ha :: ta) (hb :: tb) {m = S k} {n = S k} =
  f ha hb :: zipWithSLV2 f ta tb

zipWithSLV3 :  (f : a -> b -> c)
            -> Vect m a
            -> Vect n b
            -> {auto 0 prf : m = n}
            -> Vect n c
zipWithSLV3 _ Nil Nil = Nil
zipWithSLV3 f (ha :: ta) (hb :: tb) {m = S k} {n = S k} =
  f ha hb :: zipWithSLV3 f ta tb

--------------------------------------------------------------------------------
--          Exercise 3
--------------------------------------------------------------------------------

data At : (n : Nat) -> (as : List a) -> Type where
  AtZ : At Z (h :: t)
  AtS : At n t -> At (S n) (h :: t)

at : (n : Nat) -> (as : List a) -> {auto 0 prf : At n as} -> a
at 0     (h :: _)               = h
at (S k) (_ :: t) {prf = AtS x} = at k t
at _     [] impossible

--------------------------------------------------------------------------------
--          Exercise 4
--------------------------------------------------------------------------------

data IsSucc : (n : Nat) -> Type where
  IsIsSucc : IsSucc (S n)

safePred : (n : Nat) -> {auto 0 prf : IsSucc n} -> Nat
safePred (S k) = k
safePred 0 impossible

--------------------------------------------------------------------------------
--          Exercise 5
--------------------------------------------------------------------------------

data IsEven : (n : Nat) -> Type where
  EZ  : IsEven 0
  ESS : IsEven n -> IsEven (S $ S n)

div2 : (n : Nat) -> {auto 0 prf : IsEven n} -> Nat
div2 0                        = 0
div2 (S $ S k) {prf = ESS ie} = 1 + div2 k

sumOfEven : (m,n : Nat) -> IsEven m -> IsEven n -> IsEven (m + n)
sumOfEven 0         _ _        prfN = prfN
sumOfEven (S $ S k) n (ESS ie) prfN = ESS $ sumOfEven k n ie prfN

--------------------------------------------------------------------------------
--          Exercise 6
--------------------------------------------------------------------------------

data IsOdd : (n : Nat) -> Type where
  O1  : IsOdd 1
  OSS : IsOdd n -> IsOdd (S $ S n)

||| From what we saw above, it is clear that we could also
||| use `n = 1` instead of this. I'll show that as an alternative
||| below.
data Is1 : (n : Nat) -> Type where
  ItIs1 : Is1 1

rem2 : Nat -> Nat
rem2 0         = 0
rem2 (S 0)     = 1
rem2 (S $ S k) = rem2 k

rem2OddEq1 : (n : Nat) -> {0 prf : IsOdd n} -> Is1 (rem2 n)
rem2OddEq1 (S 0)                    = ItIs1
rem2OddEq1 (S $ S k) {prf = OSS io} = rem2OddEq1 k {prf = io}
rem2OddEq1 0 impossible

||| `x = y` has only one data constructor called `Refl`.
rem2OddEq1' : (n : Nat) -> {0 prf : IsOdd n} -> rem2 n = 1
rem2OddEq1' (S 0)                    = Refl
rem2OddEq1' (S $ S k) {prf = OSS io} = rem2OddEq1' k {prf = io}
rem2OddEq1' 0 impossible

--------------------------------------------------------------------------------
--          Exercise 7
--------------------------------------------------------------------------------

AssocList : (k : Type) -> (v : Type) -> Type
AssocList k v = List (k,v)

data IsKey : (key : k) -> (pairs : AssocList k v) -> Type where
  Here  : IsKey key $ (key,val) :: ps
  There : IsKey key ps -> IsKey key (p :: ps)

||| Note, that we actually don't do anything with the key here.
||| It is therefore safe to erase it.
lookup : (0 key : k) -> (ps : AssocList k v) -> {auto prf : IsKey key ps} -> v
lookup key ((key,val) :: _)  {prf = Here}     = val
lookup key (_         :: ps) {prf = There ik} = lookup key ps

--------------------------------------------------------------------------------
--          Exercise 8
--------------------------------------------------------------------------------

AssocVect : (n : Nat) -> (k : Type) -> (v : Type) -> Type
AssocVect n k v = Vect n (k,v)

data IsKeyV : (key : k) -> (pairs : AssocVect n k v) -> Type where
  HereV  : IsKeyV key $ (key,val) :: ps
  ThereV : IsKeyV key ps -> IsKeyV key (p :: ps)

||| This might have been hard to implement.
||| In the recursive case, we need to convince Idris,
||| that the tail of our vector can't be empty, as this
||| is a prerequisite in the type of delete.
||| We do this by pattern matching on the tail, allowing
||| Idris to verify that the combination of `ThereV` and an
||| empty tail is impossible.
delete :  (0 key : k)
       -> (ps : AssocVect (S n) k v)
       -> {auto prf : IsKeyV key ps}
       -> AssocVect n k v
delete key (_ :: t)          {prf = HereV}     = t
delete key (p :: t@(_ :: _)) {prf = ThereV ik} = p :: delete key t
delete key (p :: [])         {prf = ThereV ik} impossible

--------------------------------------------------------------------------------
--          Exercise 9
--------------------------------------------------------------------------------

data NonEmpty : (values : List a) -> Type where
  ItIsNonEmpty : NonEmpty (h :: t)

head : (xs : List a) -> {auto 0 prf : NonEmpty xs} -> a
head (h :: _) = h
head Nil impossible

data OneNonEmpty : (vss : List (List a)) -> Type where
  HereNE  : OneNonEmpty ((v :: vs) :: vss)
  ThereNE : OneNonEmpty vss -> OneNonEmpty (vs :: vss)

conc : List (List a) -> List a
conc []        = []
conc (x :: xs) = x ++ conc xs

concNonEmpty :  (vss : List (List a))
             -> (prf : OneNonEmpty vss)
             -> NonEmpty (conc vss)
concNonEmpty ([] :: t)       (ThereNE prf2) = concNonEmpty t prf2
concNonEmpty ((h :: _) :: _) _              = ItIsNonEmpty
concNonEmpty []   _           impossible
concNonEmpty [[]] HereNE      impossible
concNonEmpty [[]] (ThereNE _) impossible

headOfMany : (vss : List (List a)) -> {auto 0 prf : OneNonEmpty vss} -> a
headOfMany vss = head (conc vss) {prf = concNonEmpty vss prf}
