module Text.Smiles.Position.UnsolvedHole

import Chem
import Text.Smiles
import Geom

%default total

-------------------------------------------------------------------------------
--    createNextBond => Types needed
-------------------------------------------------------------------------------

Smiles : AffineTransformation

-- at this state, no rings or bridging atoms are included
record GenLabel where
  constructor GL
  -- normal atom fields
  atom             : AromIsotope
  chargeL          : Charge
  hCount           : HCount
  atomType         : AtomType
  chiral           : Chirality
  position         : Maybe (Point Smiles)

  angle            : Maybe Angle

  -- flag if checked (at the beginning, check if chirality
  -- has to be adjusted, line 2262 - 2281)
  dblConfigChecked : Bool

  -- flag if the atom has allready coordinates, -> easier
  -- to check if there is a Just (Point _) or a Nothing
  drawn            : Bool

  -- node of atom that was positioned before, don't
  -- know if ´Fin n´ is the right type
  -- previousAngle can be extracted from the graph
  prevAtom     : Maybe $ Fin n

  -- nextAtomAngle can be extracted from the graph
  nextAtom         : Maybe $ Fin n

0 SmilesGraphToPos : Type
SmilesGraphToPos = Graph SmilesBond GenLabel

toGenLabels : Fin k -> Adj k SmilesBond SmilesAtomAT -> GenLabel
toGenLabels _ (A lbl neigh) =
  GL { atom             = lbl.elem
     , chargeL          = lbl.charge
     , hCount           = lbl.hydrogen
     , atomType         = lbl.type
     , chiral           = lbl.chirality
     , position         = Nothing
     , angle            = Nothing
     , dblConfigChecked = False
     , drawn            = False
     , prevAtom         = Nothing
     , nextAtom         = Nothing
   }

-- convert graph without positions to a graph with the `GenLabel`
-- (better name needed!)
convertToLabel : SmilesGraphAT -> SmilesGraphToPos
convertToLabel (G o g) =
  G o $ mapWithCtxt toGenLabels g
