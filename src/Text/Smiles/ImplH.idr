module Text.Smiles.ImplH

import Data.Maybe
import Data.List
import Chem
import Chem.Atom
import Text.Smiles.Types
import Data.Graph
import Data.BitMap
import Data.AssocList

%default total

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

toImplH : (val : Nat) -> (bonds : Nat) -> Maybe HCount
toImplH val bonds = refineHCount (cast val - cast bonds)

subset :
     (e : Elem)
  -> {auto 0 prf : ValidSubset e False}
  -> Nat
  -> Maybe HCount
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

subsetArom :
     (e : Elem)
  -> {auto 0 prf : ValidSubset e True}
  -> (List Bond, Nat)
  -> Maybe HCount
subsetArom C ([], 2)      = Just $ 1
subsetArom C ([], 3)      = Just $ 0
subsetArom C ([Sngl], 2)  = Just $ 0
subsetArom C ([Dbl], 2)   = Just $ 0
subsetArom C (_, _)       = Nothing
subsetArom N ([], 3)      = Just $ 0
subsetArom N ([], 2)      = Just $ 0
subsetArom N ([Sngl], 2)  = Just 0
subsetArom N (_, _)       = Nothing
subsetArom O ([], 2)      = Just $ 0
subsetArom O (_, _)       = Nothing
subsetArom B ([], 3)      = Just $ 0
subsetArom B ([], 2)      = Just $ 0
subsetArom B ([Sngl], 2)  = Just $ 0
subsetArom B (_, _)       = Nothing
subsetArom S ([], 2)      = Just $ 0
subsetArom S (_, _)       = Nothing
subsetArom P ([], 3)      = Just $ 0
subsetArom P ([], 2)      = Just $ 0
subsetArom P (_, _)       = Nothing

export
toAtom : Atom -> List Bond -> Maybe (Atom Chirality)
toAtom (SubsetAtom e False) xs = org e <$> subset e (bondTotal xs)
toAtom (SubsetAtom e True) xs  = orgArom e <$> subsetArom e (aromBonds xs)
toAtom (Bracket _ e a _ h c) _ = Just $ MkAtom e a Nothing c None h

export
adjToAtom : Adj Bond Atom -> Maybe (Adj Bond (Atom Chirality))
adjToAtom (MkAdj e ns) = map (`MkAdj` ns) (toAtom e (values ns))

public export
graphWithH : Graph Bond Atom -> Maybe (Graph Bond (Atom Chirality))
graphWithH (MkGraph graph) = map MkGraph (traverse adjToAtom graph)
