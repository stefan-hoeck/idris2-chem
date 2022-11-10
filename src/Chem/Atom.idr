module Chem.Atom

import Chem
import Text.Smiles
import Chem.Formula
import Chem.Element
import Data.Maybe.NothingMax
import Data.Prim.String
import Data.Nat

%default total

public export
record Atom a where
  constructor MkAtom
  elem     : Elem
  arom     : Bool
  massNr   : Maybe MassNr
  charge   : Charge
  label    : a
  hydrogen : HCount
  {auto 0 prf    : ValidAromatic elem arom}

public export
Functor Atom where
  map f (MkAtom e ar ma ch l hy) = MkAtom e ar ma ch (f l) hy

public export
Foldable Atom where
  foldr f acc at  = f at.label acc
  foldl f acc at = f acc at.label
  null at         = False
  foldlM f acc at = f acc at.label
  toList at       = [at.label]
  foldMap f at    = f at.label

public export
Traversable Atom where
  traverse f (MkAtom e a ma ch l h) = (\v => MkAtom e a ma ch v h) <$> f l

export
Show a => Show (Atom a) where
  showPrec p (MkAtom e a ma ch l hy) =
    showCon p "MkAtom" $ showArg e ++ showArg a ++ showArg ma ++ showArg ch ++ 
      showArg l ++ showArg hy ++ "prf"

public export
Eq a => Eq (Atom a) where
  (MkAtom e1 a1 ma1 ch1 l1 hy1) == (MkAtom e2 a2 ma2 ch2 l2 hy2) =
    e1 == e2 && a1 == a2 && ma1 == ma2 && ch1 == ch2 && l1 == l2 && hy1 == hy2


public export
toFormula : Atom a -> Formula
toFormula (MkAtom e _ _ _ _ h) = case cast {to = Nat} (h.value) of
    0     => singleton e 1
    (S v) => singleton e 1 <+> singleton H (S v)
