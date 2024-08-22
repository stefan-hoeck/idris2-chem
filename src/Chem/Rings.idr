module Chem.Rings

import Data.Array
import Data.Array.Indexed
import Data.Array.Mutable
import Data.AssocList.Indexed
import Data.Bits
import Data.Graph.Indexed.Types
import Data.Graph.Indexed.Util
import Data.Linear.Ref1
import Data.List

import Syntax.T1

%default total

public export
record Ring k where
  constructor R
  value : Integer

export
popCountInteger : Integer -> Nat
popCountInteger = go 0
  where
    go : Nat -> Integer -> Nat
    go n x =
      case x <= 0 of
        True  => n
        False =>
          let n2 := n + cast (popCount {a = Bits32} (cast x))
           in go n2 (assert_smaller x (shiftR x 32))

export %inline
ringSize : Ring k -> Nat
ringSize = popCountInteger . value

export
inRing : Fin k -> Ring k -> Bool
inRing v ring = testBit ring.value $ finToNat v

export
members : {k : _} -> Ring k -> List (Fin k)
members r = filter (`inRing` r) (allFinsFast k)

export
{k : _} -> Show (Ring k) where
  show = show . members

export
{k : _} -> Eq (Ring k) where
  r1 == r2 = (value r1) == (value r2)

export
Semigroup (Ring k) where
  (<+>) r1 r2 = R (xor r1.value r2.value)

export
Monoid (Ring k) where
  neutral = R 0

record PreRing (k : Nat) where
  constructor PR
  value : Integer

add : Fin k -> PreRing k -> PreRing k
add v prering = PR . setBit prering.value $ finToNat v

inPreRing : Fin k -> PreRing k -> Bool
inPreRing v prering = testBit prering.value $ finToNat v

merge : PreRing k -> PreRing k -> Ring k
merge pr1 pr2 = R (xor pr1.value pr2.value)

addFused : Bool -> Ring k -> List (Bool, Ring k) -> List (Bool, Ring k)
addFused f y []     = [(f, y)]
addFused f y (x :: xs) =
  if popCountInteger (value y .&. value (snd x)) > 1
    then addFused True (R $ value y .|. (value (snd x))) xs
    else x :: addFused False y xs

parameters (ps : MArray k (Maybe $ PreRing k))
           (rs : Ref1 (List (Bool, Ring k)))
           (g  : IGraph k e n)

  addRing : Ring k -> F1' [ps,rs]
  addRing x = mod1 rs (addFused False x)

  findRings : (v : Fin k) -> (curr, prev : PreRing k) -> F1' [ps,rs]
  
  findRings' : List (Fin k) -> (v : Fin k) -> (next, curr, prev : PreRing k) -> F1' [ps,rs]

  findRings v curr prev t =
    let _ # t := set ps v (Just curr) t
        next  := add v curr
     in findRings' (neighbours g v) v (assert_smaller curr next) curr prev t

  findRings' []        v next curr prev t = () # t
  findRings' (x :: xs) v next curr prev t =
    case get ps x t of
      Nothing # t =>
        let _ # t := findRings x next curr t
         in findRings' xs v next curr prev t
      Just pr # t =>
        if inPreRing x prev
          then 
            let _ # t := addRing (merge next pr) t
             in findRings' xs v next curr prev t
          else findRings' xs v next curr prev t

  findAll : List (Fin k) -> (1 t : T1 [ps,rs]) -> R1 [] (List (Bool, Ring k))
  findAll []        = T1.do release ps; readAndRelease rs
  findAll (x :: xs) = T1.do
    Nothing <- get ps x | Just _ => findAll xs
    findRings x (PR 0) (PR 0)
    findAll xs

export
rings : {k : _} -> (g : IGraph k e n) -> List (Bool, Ring k)
rings g =
  run1 $ \t =>
    let A rs t := ref1 (the (List (Bool, Ring k)) []) t
        A ps t := newMArray k (the (Maybe $ PreRing k) Nothing) t
     in findAll ps rs g (allFinsFast k) t
