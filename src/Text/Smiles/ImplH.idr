module Text.Smiles.ImplH

import Chem
import Data.Maybe
import Data.List
import Derive.Prelude
import Text.Smiles.Types
import Data.List.Quantifiers.Extra

%language ElabReflection
%default total

---------------------------------------------------------------------
-- Error type
---------------------------------------------------------------------

public export
data HErr : Type where
  HE : Node -> Elem -> (bonds : Nat) -> HErr

%runElab derive "HErr" [Eq,Show]

export
Interpolation HErr where
  interpolate (HE n el bs) =
    "Valence exceeded for \{el}: \{show bs} bond equivalents found at node \{show n}"

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

-- calculates the total bond order
bondTotal : List Bond -> Nat
bondTotal = foldl (\n,b => n + ord b) 0
  where
    ord : Bond -> Nat
    ord Sngl = 1
    ord Arom = 2
    ord Dbl  = 2
    ord Trpl = 3
    ord Quad = 4
    ord FW   = 2
    ord BW   = 2

-- generates a pair with a list of non aromatic bonds and a
-- aromatic bond counter
aromBonds : List Bond -> (List Bond, Nat)
aromBonds = foldl fun ([],0)
  where fun : (List Bond, Nat) -> Bond -> (List Bond, Nat)
        fun (x, z) Arom = (x, S z)
        fun (x, z) FW = (Dbl :: x, z)
        fun (x, z) BW = (Dbl :: x, z)
        fun (x, z) b  = (b :: x, z)

-- creates an atom from a non-aromatic subset element
org : Elem -> HCount -> Atom Chirality
org e h = MkAtom e False Nothing 0 None h

-- creates an atom from an aromatic subset element
orgArom : (e : Elem) -> (0 _ : ValidAromatic e True) => HCount -> Atom Chirality
orgArom e h = MkAtom e True Nothing 0 None h

toImplH : (val : Nat) -> (bonds : Nat) -> Maybe HCount
toImplH val bonds = refineHCount (cast val - cast bonds)

subset : (e : Elem) -> {auto 0 _ : ValidSubset e False} -> Nat -> Maybe HCount
subset C n  = toImplH 4 n
subset O n  = toImplH 2 n
subset N n  = toImplH 3 n <|> toImplH 5 n
subset B n  = toImplH 3 n
subset F n  = toImplH 1 n
subset P n  = toImplH 3 n <|> toImplH 5 n
subset S n  = toImplH 2 n <|> toImplH 4 n <|> toImplH 6 n
subset Cl n = toImplH 1 n
subset Br n = toImplH 1 n
subset I n  = toImplH 1 n

arom : (e : Elem) -> (0 _ : ValidSubset e True) => List Bond -> Nat -> Maybe HCount
arom C [] 2      = Just 1
arom C [] 3      = Just 0
arom C [Sngl] 2  = Just 0
arom C [Dbl] 2   = Just 0
arom C l n       = Nothing
arom N [] 3      = Just 0
arom N [] 2      = Just 0
arom N [Sngl] 2  = Just 0
arom N l n       = Nothing
arom O [] 2      = Just 0
arom O l n       = Nothing
arom B [] 3      = Just 0
arom B [] 2      = Just 0
arom B [Sngl] 2  = Just 0
arom B l n       = Nothing
arom S [] 2      = Just 0
arom S l n       = Nothing
arom P [] 3      = Just 0
arom P [] 2      = Just 0
arom P l n       = Nothing

parameters {auto has : Has HErr es}

  adjToAtom : Node -> Adj Bond Atom -> ChemRes es (Adj Bond (Atom Chirality))
  adjToAtom n (MkAdj se ns) = case se of
    SubsetAtom e False =>
      let bnds := bondTotal $ values ns
       in case subset e bnds of
            Just h  => Right (MkAdj (org e h) ns)
            Nothing => Left $ inject (HE n e bnds)
    SubsetAtom e True  =>
      let (ys,bnds) := aromBonds $ values ns
       in case arom e ys bnds of
            Just h  => Right (MkAdj (orgArom e h) ns)
            Nothing => Left $ inject (HE n e bnds)
    Bracket _ e a _ h c => Right $ MkAdj (MkAtom e a Nothing c None h) ns


---------------------------------------------------------------------
-- Main function
---------------------------------------------------------------------

  export
  graphWithH : Graph Bond Atom -> ChemRes es (Graph Bond (Atom Chirality))
  graphWithH (MkGraph g) = map MkGraph (traverseWithKey adjToAtom g)
