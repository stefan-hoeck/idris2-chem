module Chem.Formula

import Chem.Elem
import Data.Maybe.Upper
import Data.Nat
import Data.Prim.String
import Derive.Prelude

%default total

||| Utility for ordering elements according to Hill notation.
public export %inline
hill : Elem -> String
hill C = ""
hill H = " "
hill e = symbol e

||| Alias for `Upper (<)`: Used as a proof that the first
||| string comes before the second or that the second
||| value equals `Nothing`.
public export
0 (<): Maybe String -> Maybe String -> Type
(<) = Upper (<)

||| A proof that the first string is less than or equal
||| to the second string. A `Nothing` is treated as being
||| greater than all `Just`s.
public export
0 (<=): Maybe String -> Maybe String -> Type
m1 <= m2 = Either (m1 < m2) (m1 === m2)

||| A provably sorted, normalized representation
||| of molecular formulae as a list of element-count
||| pairs.
|||
||| This is indexed by the Hill-string of the head element
||| (if any) to help with the proof of the list being properly
||| sorted.
public export
data Repr : (ix : Maybe String) -> Type where
  Nil : Repr Nothing
  (::) :  {0 ix : _}
       -> (p     : (Elem,Nat))
       -> (ps    : Repr ix)
       -> {auto 0 prf : Just (hill $ fst p) < ix}
       -> {auto 0 nz  : IsSucc (snd p)}
       -> Repr (Just $ hill $ fst p)

--------------------------------------------------------------------------------
--          Merging Formulae
--------------------------------------------------------------------------------

||| Result of computing the union of two molecular formulae with
||| elem indices `e1` and `e2`. The result's elem index is equal to either
||| `e1` or `e2`
public export
record MergeRes (h1,h2 : Maybe String) where
  constructor MR
  {0 hx  : Maybe String}
  repr   : Repr hx
  0 prf  : Either (h1 === hx) (h2 === hx)

0 trans_LT_EQ : {0 lt : _} -> Transitive a lt => lt x y -> y === z -> lt x z
trans_LT_EQ w Refl = w

%inline
prepLT : (p : (Elem,Nat))
       -> MergeRes h1 (Just k2)
       -> (0 prf1 : Just (hill $ fst p) < h1)
       => (0 prf2 : Just (hill $ fst p) < Just k2)
       => (0 nz   : IsSucc (snd p))
       => MergeRes (Just $ hill $ fst p) (Just k2)
prepLT p (MR ps prf) =
  let 0 lt = either (trans_LT_EQ prf1) (trans_LT_EQ prf2) prf
   in MR (p :: ps) (Left Refl)

%inline
prepGT : (p : (Elem,Nat))
       -> MergeRes (Just k1) e2
       -> (0 prf1 : Just (hill $ fst p) < e2)
       => (0 prf2 : Just (hill $ fst p) < Just k1)
       => (0 nz   : IsSucc (snd p))
       => MergeRes (Just k1) (Just $ hill $ fst p)
prepGT p (MR ps prf) =
  let 0 lt = either (trans_LT_EQ prf2) (trans_LT_EQ prf1) prf
   in MR (p :: ps) (Right Refl)

%inline
prepEQ :  {0 x : Maybe String}
       -> (p : (Elem,Nat))
       -> (0 eq  : hill (fst p) === k)
       -> MergeRes h1 h2
       -> (0 prf1 : Just (hill $ fst p) < h1)
       => (0 prf2 : Just k < h2)
       => (0 nz   : IsSucc (snd p))
       => MergeRes (Just $ hill $ fst p) x
prepEQ p eq (MR ps prf) =
  let 0 fstp_lt_m2 = rewrite eq in prf2
      0 lt = either (trans_LT_EQ prf1) (trans_LT_EQ fstp_lt_m2) prf
   in MR (p :: ps) (Left Refl)

0 plusSucc : (m,n : Nat) -> (0 prf : IsSucc m) => IsSucc (m + n)
plusSucc (S k) n = ItIsSucc
plusSucc 0 n impossible

||| Merges to molecular formulae making sure by design that the
||| result ist still normalized, that is, entries are ordered
||| according to Hill notation, and all counts are positive.
export
merge : Repr h1 -> Repr h2 -> MergeRes h1 h2
merge (p :: ps) (q :: qs) = case comp (hill $ fst p) (hill $ fst q) of
  LT prf _   _   => prepLT p $ merge ps (q :: qs)
  EQ _   prf _   =>
    let 0 nz := plusSucc (snd p) (snd q)
     in prepEQ (fst p, snd p + snd q) prf $ merge ps qs
  GT _   _   prf => prepGT q $ merge (p :: ps) qs
merge y [] = MR y (Left Refl)
merge [] y = MR y (Right Refl)

||| Extract the key-value pairs from a molecular formula.
export
pairs : Repr h1 -> List (Elem,Nat)
pairs (h :: t) = h :: pairs t
pairs []       = []

--------------------------------------------------------------------------------
--          Comparisons
--------------------------------------------------------------------------------

||| Heterogeneous comparison of molecular formulae
public export
hcomp : Repr h1 -> Repr h2 -> Ordering
hcomp (p :: ps) (q :: qs) = case compare (hill $ fst p) (hill $ fst q) of
  EQ => case compare (snd p) (snd q) of
    EQ => hcomp ps qs
    o  => o
  o => o
hcomp []        []        = EQ
hcomp []        _         = LT
hcomp _         []        = GT

||| Heterogeneous equality between molecular formulae
public export
heq : Repr h1 -> Repr h2 -> Bool
heq x y = hcomp x y == EQ

||| True if the first formula has at least as many atoms of each element
||| as the second formula.
public export
contains_ : Repr h1 -> Repr h2 -> Bool
contains_ (p :: ps) (q :: qs) = case compare (hill $ fst p) (hill $ fst q) of
  LT => contains_ ps (q :: qs)
  EQ => snd p >= snd q && contains_ ps qs
  GT => False
contains_ _  [] = True
contains_ [] _  = False

--------------------------------------------------------------------------------
--          Formula
--------------------------------------------------------------------------------

||| A provably normalized molecular formula.
|||
||| This is just a wrapper around `Repr mx`, the representation of a
||| molecular formula as a provably sorted list of pairs.
public export
record Formula where
  constructor F
  {0 mx : Maybe String}
  pairs : Repr mx

public export %inline
Eq Formula where
  F x == F y = heq x y

public export %inline
Ord Formula where
  compare (F x) (F y) = hcomp x y

showPair : (Elem,Nat) -> String
showPair (e, 1) = symbol e
showPair (e, n) = symbol e ++ show n

export
Show Formula where
  show (F ps) = fastConcat $ map showPair (pairs ps)

export %inline
Interpolation Formula where
  interpolate = show

export %inline
Semigroup Formula where
  F x <+> F y = F (repr $ merge x y)

export %inline
Monoid Formula where
  neutral = F []

||| Creates a molecular formula with the given element and count.
export %inline
singleton : Elem -> (n : Nat) -> Formula
singleton e 0     = F []
singleton e (S n) = F [(e,S n)]

||| True, if the first `Formula` contains at least the atoms listed
||| in the second formula, that is, all elements in the second formula
||| apear at the same or a higher count in the first.
export %inline
contains : Formula -> Formula -> Bool
contains (F x) (F y) = contains_ x y

--------------------------------------------------------------------------------
--          Tests
--------------------------------------------------------------------------------

0 containsTest1 : contains (F [(C,2),(H,6), (O,1)]) (F [(H,2),(O,1)]) === True
containsTest1 = Refl

0 containsTest2 : contains (F [(H,1),(F,1)]) (F [(H,2),(O,1)]) === False
containsTest2 = Refl

0 containsTest3 : contains (F []) (F [(H,2)]) === False
containsTest3 = Refl

0 containsTest4 : contains (F []) (F []) === True
containsTest4 = Refl
