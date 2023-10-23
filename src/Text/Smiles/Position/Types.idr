module Text.Smiles.Position.Types

import Chem
import Text.Smiles
import Geom

%default total

-------------------------------------------------------------------------------
--    createNextBond => Types needed
-------------------------------------------------------------------------------

Smiles : AffineTransformation

record GenLabel where
  constructor GL
  -- normal atom fields
  atom             : AromIsotope
  charge           : Charge
  hCount           : HCount
  atomType         : AtomType
  chirality        : Chirality
  position         : Maybe (Point Smiles)

  angle            : Maybe Angle

  -- flag if checked (at the beginning, check if chirality
  -- has to be adjusted, line 2262 - 2281)
  dblConfigChecked : Bool

  -- flag if the atom has allready coordinates, -> easier
  -- to check if there is a Just (Point _) or a Nothing
  drawn            : Bool

  -- node of atom that was drawn before, don't
  -- know if ´Fin n´ is the right type
  previousAtom     : Maybe $ Fin n

  nextVertex       : Maybe $ Fin n
  nextVertexAngle  : Maybe $ Angle

  previousAngle    : Maybe $ Angle
