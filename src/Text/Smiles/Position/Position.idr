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
  updateAt n (map { coord := origin , angle := (1.0 / 6.0) * pi })
-- Do I need Optionals here?
--    setL (ix n .> coordL) (origin)
--  . setL (ix n .> angleL) ((1.0 / 6.0) * pi)

drawChildNode : (current,parent : Fin k) -> State k -> Maybe (Point Mol)
drawChildNode n p s =
  let Just prntPnt := getCoord p s | Nothing => Nothing
      Just curAngl := getAngle n s | Nothing => Nothing
      vect         := polar BondLengthInAngstrom curAngl
   in Just $ translate vect prntPnt

updateNode : Fin k -> Point Mol -> Angle -> State k -> State k
updateNode n p a =
  updateAt n (map { coord := p , angle := a })

-- Needed to update the different branch states
-- Are there modification possible of another indice than the first of the
-- update list?
updateState : State k -> State k -> State k
updateState xs ys = ?updateState_rhs

(++) : State k -> State k -> State k
(++) = updateState

head : List (Fin n) -> Fin n

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
      -- get all neighbours that needs to be checked for drawing
    let allNeigh := map fst (pairs (neighbours g n))
        parent   := parent n s
        toDrawN  := maybe allNeigh (\p => dropWhile (== p) allNeigh) parent
        -- TODO: Proove that this list gets smaller
        -- TODO: Sort `toDrawN` for deciding, which branch should be drawn first
        drawList := toDrawN ++ ns
        nCount   := length drawList
    -- set coords for the neighours
     in case getCoord n s of
       -- Starting Node: Repeat drawing of this node with its start coord and
       -- angle
       Nothing => draw (n :: ns) $ updateNode n origin ((1.0 / 6.0) * pi) s
       _       =>
         case nCount of
           0 => ?nothing
           1 => ?oneN
           2 => ?twoN
           3 => ?threeN
           4 => ?fourN
           _ => ?starFormation


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
