module Text.Smiles.Position.Position

import Text.Smiles.Position.Types
import Text.Smiles.Types
import Chem
import Geom
import Data.Vect
import Monocle


%default total

--------------------------------------------------------------------------------
--      Settings
--------------------------------------------------------------------------------

record DrawerSettings where
  constructor DS
  bondLength : Double

--------------------------------------------------------------------------------
--      Util
--------------------------------------------------------------------------------

-- get the parent node if it exists
%inline
parent : Fin k -> State k -> Maybe (Fin k)
parent n = maybe Nothing parent . index n

%inline
getCoord : Fin k -> State k -> Maybe (Point Mol)
getCoord n = maybe Nothing (Just . coord) . index n

%inline
getAngle : Fin k -> State k -> Maybe (Angle)
getAngle n = maybe Nothing (Just . angle) . index n

-- draw the very first node with no parent node
drawNodeOrigin : Fin k -> State k -> State k
drawNodeOrigin n =
  updateAt n (map { coord := origin
                  , angle := (1.0 / 6.0) * pi
                  })
--    setL (ix n .> coordL) (origin)
--  . setL (ix n .> angleL) ((1.0 / 6.0) * pi)

drawChildNode : (current,parent : Fin k) -> State k -> Maybe (Point Mol)
drawChildNode n p s =
  let Just prntPnt := getCoord p s | Nothing => Nothing
      Just curAngl := getAngle n s | Nothing => Nothing
      vect         := polar BondLengthInAngstrom curAngl
   in Just $ translate vect prntPnt

updateCoord : Fin k -> Point Mol -> State k -> State k
updateCoord n p = ?foo6 --updateAt n ({coord := p})

---- computes the preferred angle for a new bond based on the bond type
---- angles to already existing bonds.
--bondAngle : (hasTriple : Bool) -> List Angle -> Angle
--bondAngle _     []  = (negate 1.0 / 6.0) * pi
--bondAngle True  [x] = x + pi
--bondAngle False [x] =
--  if (x >= zero && x <= halfPi) || (x >= pi && x <= threeHalfPi)
--     then x + twoThirdPi
--     else x - twoThirdPi
--bondAngle _     xs  = largestBisector xs
--
---- ideal position for a new atom bound to an existing one based on the
---- largest bisector of angles between existing bonds
--bestPos : IGraph k OBond OAtom -> SmilesBond -> Fin k -> Point Id -> Point Id
--bestPos g b n p =
--  let neigh    := values (lneighbours g n)
--      bonds    := b :: map (snd . fst) neigh
--      lVect    := map (\z => pointId z - p) (snd <$> neigh)
--      ws       := mapMaybe angle lVect
--      newAngle := bondAngle (any ((Trpl ==) . type) bonds) ws
--      transV   := polar BondLengthInPixels newAngle
--   in translate transV p

--------------------------------------------------------------------------------
--      Depth first traversal
--------------------------------------------------------------------------------

parameters {0 k : _}
           (g : IGraph k SmilesBond SmilesAtom)
           {se : DrawerSettings}

  partial
  draw : List (Fin k) -> State k -> State k
  draw []        s = s
  draw (n :: ns) s =
    -- set coord
    case parent n s of
      Nothing => drawNodeOrigin n s
      Just p  =>
        let Just newCoord := drawChildNode n p s | Nothing => s  -- break from algorithm
            placeCurNode  := updateCoord n newCoord s
         -- set angles for neighbours
         in ?determineNeighAngles


--------------------------------------------------------------------------------
--      Test
--------------------------------------------------------------------------------

-- yet only showing concept

SmilesPAtom : Type
SmilesPAtom =
  Atom AromIsotope Charge (Point Mol) () HCount AtomType Chirality ()

giveCoord :
     IGraph k SmilesBond SmilesAtom
  -> Info k
  -> IGraph k SmilesBond SmilesPAtom
giveCoord g i = ?giveCoord_rhs

toPosition : IGraph k SmilesBond SmilesAtom -> IGraph k SmilesBond SmilesPAtom
