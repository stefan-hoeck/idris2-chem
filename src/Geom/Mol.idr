||| The geometry of molecules
module Geom.Mol

import Text.Molfile

import Geom.Angle
import Geom.Bounds
import Geom.Point
import Geom.Scale
import Geom.Vector

%default total

||| Desired bond length in a .mol file in Angstrom
public export
BondLengthInAngstrom : Scale
BondLengthInAngstrom = 1.25

||| Desired bond length in the UI
public export
BondLengthInPixels : Scale
BondLengthInPixels = 20

||| Scaling factor when drawing molecules.
|||
||| Note: This must not be applied as part of the overall transformations of
|||       the canvas when drawing the molecule, because this would also scale
|||       the bond thickness and font sizes.
|||
|||       The points corresponding to the atoms in a molecule are therefore
|||       indexed by the inverse of this scaling factor. That way, when we
|||       convert a molecule to a canvas `Scene` - where we will always
|||       require `Point Id`s for the positions - the correct scaling happens
|||       automatically.
public export
ScalingFactor : Scale
ScalingFactor = BondLengthInPixels / BondLengthInAngstrom

||| Describes the affine space a molecule loaded from a molfile
||| (and after normalization, see `normalizeMol`) lives in.
|||
||| See also @ScalingFactor for some more details.
export
Mol : AffineTransformation
Mol = AT (scaling $ inverse ScalingFactor) vzero

--------------------------------------------------------------------------------
--          Atom Position
--------------------------------------------------------------------------------

toCoord : Double -> Maybe Coordinate
toCoord d = refineCoordinate (cast $ d * cast Precision)

||| Adjust the 3-D coordinates of an atom by setting the x- and y-
||| coordinate from the given `Point Mol`.
export
toCoords : Point Mol -> Vect 3 Coordinate -> Vect 3 Coordinate
toCoords (P x y) cs@[_,_,z] =
  let Just cx := toCoord x          | Nothing => cs
      Just cy := toCoord (negate y) | Nothing => cs
   in [cx,cy,z]

export
GetPoint (Vect 3 Coordinate) Mol where
  point [x,y,_] = P (cast x) (negate $ cast y)

export
ModPoint (Vect 3 Coordinate) Mol where
  modPoint f cs = toCoords (f $ point cs) cs

export %inline
GetPoint MolAtom Mol where
  point = point . position

export %inline
ModPoint MolAtom Mol where
  modPoint f = {position $= modPoint f}

export %inline
GetPoint MolAtomAT Mol where
  point = point . position

export %inline
ModPoint MolAtomAT Mol where
  modPoint f = {position $= modPoint f}

export %inline
ModPoint a t => ModPoint (Graph b a) t where modPoint = map . modPoint

export %inline
{k : _} -> ModPoint a t => ModPoint (IGraph k b a) t where
  modPoint = map . modPoint

--------------------------------------------------------------------------------
--          Bond Lengths and Normalization
--------------------------------------------------------------------------------

||| Calculate the length of an edge in a molecule
export
bondLength : GetPoint a t => {k : _} -> IGraph k b a -> Edge k b -> Double
bondLength g (E x y _) = distance (point $ lab g x) (point $ lab g y)

||| Calculate the average length of bonds in a molecule.
export
averageBondLength : GetPoint a t => {k : _} -> IGraph k b a -> Maybe Double
averageBondLength g = case edges g of
  [] => Nothing
  es => Just $ sum (bondLength g <$> es) / cast (length es)

||| Normalize a molecule to an average bond length of 1.25 Angstrom.
export
normalizeMol :
     {auto mod : ModPoint a Mol}
  -> {auto get : GetPoint a Mol}
  -> {k : _}
  -> IGraph k b a
  -> IGraph k b a
normalizeMol g = case averageBondLength g of
  Nothing => g
  Just v  => scale {t = Mol} (BondLengthInAngstrom / scale v) g
