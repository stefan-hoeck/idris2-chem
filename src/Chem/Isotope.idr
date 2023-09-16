module Chem.Isotope

import Chem.Elem
import Chem.Types
import Derive.Prelude

%default total
%language ElabReflection

||| An element paired with an optional mass number.
|||
||| If the mass number is `Nothing`, a value of this type represents
||| a natural mixture of isotopes.
public export
record Isotope where
  constructor MkI
  elem : Elem
  mass : Maybe MassNr

%runElab derive "Isotope" [Show,Eq]

export %inline
Cast Isotope Elem where cast = elem

export %inline
Cast Elem Isotope where cast e = MkI e Nothing

||| An element paired with an optional mass number plus a
||| boolean flag representing aromaticity.
|||
||| If the mass number is `Nothing`, a value of this type represents
||| a natural mixture of isotopes.
public export
record AromIsotope where
  constructor MkAI
  elem : Elem
  mass : Maybe MassNr
  arom : Bool
  {auto 0 prf : ValidAromatic elem arom}

%runElab derive "AromIsotope" [Show,Eq]

export %inline
Cast AromIsotope Elem where cast = elem

export %inline
Cast Elem AromIsotope where cast e = MkAI e Nothing False

export %inline
Cast AromIsotope AromElem where cast (MkAI e m a) = MkAE e a

export %inline
Cast AromElem AromIsotope where cast (MkAE e a) = MkAI e Nothing a
