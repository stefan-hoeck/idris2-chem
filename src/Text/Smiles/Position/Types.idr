module Text.Smiles.Position.Types

import Chem
import Text.Smiles
import Geom
import Data.Vect

%default total

--------------------------------------------------------------------------------
--      State
--------------------------------------------------------------------------------

public export
record Info k where
  constructor I
  parent  : Maybe $ Fin k
  coord   : Point Mol
  angle   : Angle

-- if Just ..., then visisted
public export
0 State : Nat -> Type
State k = Vect k $ Maybe (Info k)
