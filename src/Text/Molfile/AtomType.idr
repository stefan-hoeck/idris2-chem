module Text.Molfile.AtomType

import Chem
import Text.Molfile.Types

%default total

||| Compute the atom type and implicit hydrogen count
||| of an atom with charge and information about
||| racicals set, that is bound to its neighbours by `MolBond`s.
export
calcMolAtomType :
     {auto fld : Foldable f}
  -> f MolBond
  -> Atom Isotope Charge p Radical h t c l
  -> Atom Isotope Charge p Radical HCount AtomType c l
calcMolAtomType ns a =
  let bs      := foldMap (toBonds . type) ns
      (hy,at) := atomTypeAndHydrogens (cast a.elem) a.radical a.charge bs
   in {type := at, hydrogen := hy} a

||| Perceive atom types and implicit hydrogens for a .mol-file graph
export %inline
perceiveMolAtomTypes : MolGraph -> MolGraphAT
perceiveMolAtomTypes (G o g) =
  G o $ mapWithCtxt (\_,(A a ns) => calcMolAtomType ns a) g
