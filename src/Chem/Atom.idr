module Chem.Atom

import Chem.Formula
import Chem.Element
import Chem.Types
import Data.Maybe.NothingMax
import Data.Nat
import Derive.Prelude

%language ElabReflection
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

%runElab derive "Atom" [Show,Eq]

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

public export
toFormula : Atom a -> Formula
toFormula (MkAtom e _ _ _ _ h) = case cast {to = Nat} (h.value) of
    0     => singleton e 1
    (S v) => singleton e 1 <+> singleton H (S v)
