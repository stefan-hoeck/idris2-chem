module Text.Smiles.AtomType

import Chem
import Text.Smiles.Types

%default total

||| SMILES atom with perceived atom type and computed
||| implicit hydrogen count
public export
0 SmilesAtomAT : Type
SmilesAtomAT = Atom AromIsotope Charge () () HCount AtomType Chirality ()

||| SMILES molecule with perceived atom type and computed
||| implicit hydrogen count
public export
0 SmilesGraphAT : Type
SmilesGraphAT = Graph SmilesBond SmilesAtomAT

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

toBonds : SmilesBond -> Bonds
toBonds Sngl = BS 1 0 0
toBonds Arom = BS 0 0 0
toBonds Dbl  = BS 0 1 0
toBonds Trpl = BS 0 0 1
toBonds Quad = BS 0 0 0 -- TODO: Should we even support this?
toBonds FW   = BS 0 1 0
toBonds BW   = BS 0 1 0

-- Adjust number of bonds for nitrogen-like elements (N, P, As) with
-- two aromatic bonds. If these have no additional single bonds, they are
-- pyridine-like and one of the aromtic bonds should be treated as a double
-- bond. Otherwise, they are pyrrole-like and both aromatic bonds should
-- be counted as single bonds.
adjNitrogen2 : Bonds -> Bonds
adjNitrogen2 bs =
  if bs.single > 0
     then {single $= (+ 2)} bs
     else {single := 1, double $= S} bs

-- add aromatic bonds to the list of bonds connected to an atom
addAromaticBonds : Elem -> Nat -> Bonds -> Bonds
addAromaticBonds _ 0 bs = bs
addAromaticBonds C 2 bs =
  if bs.double > 0
     then {single $= (+ 2)} bs
     else {single $= S, double $= S} bs
addAromaticBonds C  3 bs = {single $= (+2), double $= S} bs
addAromaticBonds N  2 bs = adjNitrogen2 bs
addAromaticBonds P  2 bs = adjNitrogen2 bs
addAromaticBonds As 2 bs = adjNitrogen2 bs
addAromaticBonds _  n bs = {single $= (+n)} bs

-- compute the atom type and implicit hydrogen count from
-- a SMILES atom and the list of bonds connected to it
calcAT : Fin k -> Adj k SmilesBond SmilesAtom -> SmilesAtomAT
calcAT n (A at@(SubsetAtom e a) ns) =
  let iso     := MkAI e Nothing a
      arom    := count (Arom ==) ns
      bonds   := addAromaticBonds e arom $ foldMap toBonds ns
      (h,tpe) := atomTypeAndHydrogens e NoRadical 0 bonds
   in MkAtom iso 0 () () h tpe None ()

calcAT n (A (Bracket x) ns) =
  let e    := cast {to = Elem} x.elem
      arom := count (Arom ==) ns
      bs   :=
          addAromaticBonds e arom               -- add aromatic bonds
        . {single $= (+ cast x.hydrogen.value)} -- add bonds to implicit Hs
        $ foldMap toBonds ns                    -- compute non-aromatic bonds
   in {type := exactAtomType e NoRadical x.charge bs} x

export %inline
perceiveSmilesAtomTypes : SmilesGraph -> SmilesGraphAT
perceiveSmilesAtomTypes (G o g) = G o $ mapWithCtxt calcAT g
