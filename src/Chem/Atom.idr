module Chem.Atom

import Chem.Element
import Data.Maybe.Upper
import Data.Nat
import Derive.Prelude

%language ElabReflection
%default total

||| Generic atom type
|||
||| Depending on an atom's origin and use case, different
||| fields hold values of different types.
|||
||| @el  : Element label. This can be `Elem`, `AromElem` or
|||        a more general type that can be used for queries
|||        for instance
||| @pos : Coordinates, representing the position of an atom
||| @rad : Type holding information about the atom being
|||        a radical or not
||| @hyd : Implicit hydrogen count
||| @tpe : Atom type. This is used to describe not only
|||        the chemical element but also the atom's connectivity
|||        and, possibly, hybridisation
||| @chr : Chirality information
||| @lbl : Generic label holding additional information. This is
|||        placed last, so that an atom becomes a `Traversable`
|||        w.r.t. the label
public export
record Atom (el,pos,rad,hyd,tpe,chr,lbl : Type) where
  constructor MkAtom
  elem      : el
  charge    : Charge
  position  : pos
  radical   : rad
  hydrogen  : hyd
  type      : tpe
  chirality : chr
  label     : lbl

%runElab derive "Atom" [Show,Eq]

export %inline
Functor (Atom e p r h t c) where
  map f = {label $= f}

export %inline
Foldable (Atom e p r h t c) where
  foldr f acc at  = f at.label acc
  foldl f acc at  = f acc at.label
  null at         = False
  foldlM f acc at = f acc at.label
  toList at       = [at.label]
  foldMap f at    = f at.label

public export
Traversable (Atom e p r h t c) where
  traverse f (MkAtom e c p r h t ch l) = MkAtom e c p r h t ch <$> f l
