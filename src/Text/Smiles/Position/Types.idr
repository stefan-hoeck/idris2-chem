module Text.Smiles.Position.Types

import Chem
import Text.Smiles
import Geom
import Data.Vect
import Monocle
import Derive.Lens

%language ElabReflection
%default total

--------------------------------------------------------------------------------
--      State
--------------------------------------------------------------------------------

public export
Smiles : AffineTransformation

public export
record Info k where
  constructor I
  drawn   : Bool
  visited : Bool
  parent  : Maybe $ Fin k
  next    : Maybe $ List (Fin k)
  coord   : Maybe $ Point Smiles
  angle   : Maybe Angle

%runElab derive "Info" [Lenses]

public export
0 State : Nat -> Type
State k = Vect k (Info k)
