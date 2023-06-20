module Text.Smiles.ImplH

import Chem
import Data.Maybe
import Data.List
import Text.Smiles.Types
import Data.List.Quantifiers.Extra

%default total

---------------------------------------------------------------------
-- Error type
---------------------------------------------------------------------

public export
data HErr : Type where
  ImplHErr :
       Elem
    -> (valence : Nat)
    -> (arom : Bool)
    -> (bonds : Nat)
    -> HErr

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
orgArom :
     (e : Elem)
  -> {auto 0 prf : ValidAromatic e True}
  -> HCount
  -> Atom Chirality
orgArom e h = MkAtom e True Nothing 0 None h

toImplH :
     (val : Nat)
  -> (bonds : Nat)
  -> (elem : Elem)
  -> ChemRes [HErr] HCount
toImplH val bonds e = case refineHCount (cast val - cast bonds) of
  Nothing => Left $ inject $ ImplHErr e val False bonds
  Just x  => Right x

-- maybe create implement an interface for 'Alternative Either'
subset :
     (e : Elem)
  -> {auto 0 prf : ValidSubset e False}
  -> Nat
  -> ChemRes [HErr] HCount
subset C n  = toImplH 4 n C
subset O n  = toImplH 2 n O
subset N n  = case toImplH 3 n N of --<|> toImplH 5 n
  Left x => toImplH 5 n N
  x      => x
subset B n  = toImplH 3 n B
subset F n  = toImplH 1 n F
subset P n  = case toImplH 3 n P of --<|> toImplH 5 n
  Left x => toImplH 5 n P
  x      => x
subset S n  = case toImplH 2 n S of --<|> toImplH 4 n <|> toImplH 6 n
  Left x => case toImplH 4 n S of
    Left y => toImplH 6 n S
    y      => y
  x      => x
subset Cl n = toImplH 1 n Cl
subset Br n = toImplH 1 n Br
subset I n  = toImplH 1 n I

subsetArom :
     (e : Elem)
  -> {auto 0 prf : ValidSubset e True}
  -> (List Bond, Nat)
  -> ChemRes [HErr] HCount
subsetArom C ([], 2)      = Right 1
subsetArom C ([], 3)      = Right 0
subsetArom C ([Sngl], 2)  = Right 0
subsetArom C ([Dbl], 2)   = Right 0
subsetArom C (l, n)       = Left $ inject $ ImplHErr C 4 True (length l + n)
subsetArom N ([], 3)      = Right 0
subsetArom N ([], 2)      = Right 0
subsetArom N ([Sngl], 2)  = Right 0
subsetArom N (l, n)       = Left $ inject $ ImplHErr N 3 True (length l + n)
subsetArom O ([], 2)      = Right 0
subsetArom O (l, n)       = Left $ inject $ ImplHErr O 2 True (length l + n)
subsetArom B ([], 3)      = Right 0
subsetArom B ([], 2)      = Right 0
subsetArom B ([Sngl], 2)  = Right 0
subsetArom B (l, n)       = Left $ inject $ ImplHErr B 3 True (length l + n)
subsetArom S ([], 2)      = Right 0
subsetArom S (l, n)       = Left $ inject $ ImplHErr S 2 True (length l + n)
subsetArom P ([], 3)      = Right 0
subsetArom P ([], 2)      = Right 0
subsetArom P (l, n)       = Left $ inject $ ImplHErr P 3 True (length l + n)

export
toAtom : Atom -> List Bond -> ChemRes [HErr] (Atom Chirality)
toAtom (SubsetAtom e False) xs = org e <$> subset e (bondTotal xs)
toAtom (SubsetAtom e True) xs  = orgArom e <$> subsetArom e (aromBonds xs)
toAtom (Bracket _ e a _ h c) _ = Right $ MkAtom e a Nothing c None h

export
adjToAtom : Adj Bond Atom -> ChemRes [HErr] (Adj Bond (Atom Chirality))
adjToAtom (MkAdj e ns) = map (`MkAdj` ns) (toAtom e (values ns))


-- TODO: Track 2
-- Define a proper error type for this and return an `Either`
-- in case implicit hydrogen perception did not work.
-- Implement a conversion function to display errors as strings

---------------------------------------------------------------------
-- Main function
---------------------------------------------------------------------
public export
graphWithH : Graph Bond Atom -> ChemRes [HErr] (Graph Bond (Atom Chirality))
graphWithH (MkGraph graph) = map MkGraph (traverse adjToAtom graph)
