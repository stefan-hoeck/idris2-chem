module Text.Smiles.Position.Types

import Chem
import Text.Smiles
import Geom

%default total

-------------------------------------------------------------------------------
--    createNextBond => Types needed
-------------------------------------------------------------------------------

Smiles : AffineTransformation

record SmilesSettings where
  constructor S
  bondLength : Double

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

0 SmilesGraphPos : Type
SmilesGraphPos = Graph SmilesBond GenLabel

toGenLabels : Fin k -> Adj k SmilesBond SmilesAtomAT -> GenLabel

-- convert graph without positions to a graph with the `GenLabel`
-- (better name needed!)
convertToLabel : SmilesGraphAT -> SmilesGraphPos
convertToLabel (G o g) =
  G o $ mapWithCtxt toGenLabels g

-- set the next and previous atoms of each node
-- algorithm which detects branches
-- SmilesDrawer: done when init the graph from the spanning tree
initPrevNext : SmilesGraphPos -> SmilesGraphPos

-- rings and double bonds are not included yet
-- TODO: linear embedding for the `SmilesGraphPos`
createNextPosition : SmilesSettings => GenLabel -> SmilesGraphPos -> GenLabel

-- If no previous node is present do this:

-- if (!previousVertex) {
--   // Add a (dummy) previous position if there is no previous vertex defined
--   // Since the first vertex is at (0, 0), create a vector at (bondLength, 0)
--   // and rotate it by 90°
--
--   let dummy = new Vector2(this.opts.bondLength, 0);
--   dummy.rotate(MathHelper.toRad(-60));
--
--   vertex.previousPosition = dummy;
--   vertex.setPosition(this.opts.bondLength, 0);
--   vertex.angle = MathHelper.toRad(-60);
--
--   // Do not position the vertex if it belongs to a bridged ring that is positioned using a layout algorithm.
--   if (vertex.value.bridgedRing === null) {
--     vertex.positioned = true;
--   }

-- If a previous node is present, do this:

-- // If the previous vertex was not part of a ring, draw a bond based
-- // on the global angle of the previous bond
-- let v = new Vector2(this.opts.bondLength, 0);
--
-- v.rotate(angle);
-- v.add(previousVertex.position);
--
-- vertex.setPositionFromVector(v);
-- vertex.previousPosition = previousVertex.position;
-- vertex.positioned = true;
