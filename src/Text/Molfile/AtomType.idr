module Text.Molfile.AtomType

import Chem
import Text.Molfile.Types

%default total

||| .mol-file atom with perceived atom type and computed
||| implicit hydrogen count
public export
0 MolAtomAT : Type
MolAtomAT =
  Atom Isotope Charge (Vect 3 Coordinate) Radical HCount AtomType () ()

||| .mol-file graph with perceived atom types and computed
||| implicit hydrogen counts
public export
0 MolGraphAT : Type
MolGraphAT = Graph MolBond MolAtomAT

toBonds : BondType -> Bonds
toBonds Single = BS 1 0 0
toBonds Dbl    = BS 0 1 0
toBonds Triple = BS 0 0 1

calcAT : Fin k -> Adj k MolBond MolAtom -> MolAtomAT
calcAT n (A l ns) =
  let bs      := foldMap (toBonds . type) ns
      (hy,at) := atomTypeAndHydrogens (cast l.elem) l.radical l.charge bs
   in {type := at, hydrogen := hy} l

||| Perceive atom types and implicit hydrogens for a .mol-file graph
export %inline
perceiveMolAtomTypes : MolGraph -> MolGraphAT
perceiveMolAtomTypes (G o g) = G o $ mapWithCtxt calcAT g
