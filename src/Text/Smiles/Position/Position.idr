module Text.Smiles.Position.Position

import Text.Smiles.Position.Types
import Text.Smiles.AtomType
import Text.Smiles.Types
import Text.Smiles.Parser
import Chem
import Geom
import Data.Vect
import Monocle
import Data.Fin


%default total

--------------------------------------------------------------------------------
--      Util
--------------------------------------------------------------------------------

-- list of all neighbours of a node
%inline
lNeigh : IGraph k e n -> Fin k -> List (Fin k)
lNeigh g n = map fst (pairs $ neighbours g n)

-- total count (also drawn ones) of neighbours
%inline
getCountNeigh : Fin k -> IGraph k e n -> Nat
getCountNeigh n g = length $ lNeigh g n

-- TODO: sort out already drawn nodes
-- Neighbours without parent node
lNeigh' : IGraph k e n -> (cur,parent : Fin k) -> List (Fin k)
lNeigh' g n p = delete p $ lNeigh g n

-- get the parent node if it exists
%inline
getParent : Fin k -> State k -> Maybe (Fin k)
getParent n = maybe Nothing parent . index n

%inline
getCoord : Fin k -> State k -> Maybe (Point Mol)
getCoord n = maybe Nothing (Just . coord) . index n

%inline
getAngle : Fin k -> State k -> Maybe (Angle)
getAngle n = maybe Nothing (Just . angle) . index n

getCoordAndAngle : Fin k -> State k -> Maybe (Point Mol, Angle)
getCoordAndAngle n s =
  let Just coord := getCoord n s | Nothing => Nothing
      Just angle := getAngle n s | Nothing => Nothing
   in Just (coord,angle)

initAngle : Angle
initAngle = negate 1.0 / 6.0 * pi

-- TODO: should be more general
calcAngle : (neededAngles : Nat) -> Angle -> List Angle
calcAngle 0 a = []
calcAngle 1 a =
  if (a >= zero && a <= halfPi) || (a >= pi && a <= threeHalfPi)
    then [a + twoThirdPi]
    else [a - twoThirdPi]
calcAngle 2 a = [a + twoThirdPi, a - twoThirdPi]
calcAngle 3 a = ?calcThreeAngle
calcAngle c a = ?calcStarAngles

-- TODO: should be more general
oneAngle : Angle -> Angle
oneAngle x =
  if (x >= zero && x <= halfPi) || (x >= pi && x <= threeHalfPi)
    then x + twoThirdPi
    else x - twoThirdPi

updateNode :
     Fin k
  -> (parent : Maybe (Fin k))
  -> Point Mol
  -> Angle
  -> State k
  -> State k
updateNode n par pt a s = replaceAt n (Just (I par pt a)) s

molOrigin : Point Mol
molOrigin = P 0.0 0.0

translate : Point Mol -> Angle -> Point Mol
translate p a = Point.translate (polar BondLengthInAngstrom a) p

toListDI : State k -> Fin k -> List (DrawInfo k) -> List (DrawInfo k)
toListDI s n l =
  let Just parent := getParent n s | Nothing => l
      Just coord  := getCoord n s  | Nothing => l
      Just angle  := getAngle n s  | Nothing => l
   in DI n parent coord angle :: l


--------------------------------------------------------------------------------
--      Depth first traversal
--------------------------------------------------------------------------------

parameters {0 k : _}
           (g : IGraph k SmilesBond SmilesAtomAT)

  -- calc angles and coordinates for neighbours of a node
  placeNeighbours : DrawInfo k -> List (Fin k) -> State k -> State k
  placeNeighbours di xs s = ?drawNeighbours_rhs

  -- gets a list of the last drawn nodes, whose neighbours had to be drawn next
  covering
  placeNext : List (DrawInfo k) -> State k -> State k
  placeNext []               s = s
  placeNext (t@(DI n p c a) :: xs) s =
        -- list of neighbours without parent
    let lNeigh   := lNeigh' g n p
        newS     := placeNeighbours t lNeigh s
        infoList := foldr (toListDI newS) [] lNeigh
     in placeNext (infoList ++ xs) newS

  -- should place the start node and (if present) one neighbour. Respectivly,
  -- one node is the parent node of the other and vice versa.
  covering
  placeInit : Fin k -> State k -> State k
  placeInit n s = case lNeigh g n of
    -- no neighbours, isolated atom
    []        => updateNode n Nothing molOrigin initAngle s
    (x :: xs) =>
      case getCoordAndAngle n s of
        Nothing =>
          -- place the first neighbour
          let initState  := updateNode n (Just x) molOrigin initAngle s
                            -- TODO: use more general function
              aFirstN    := oneAngle initAngle
              pFirstN    := translate molOrigin aFirstN
              secState   := updateNode x (Just n) pFirstN aFirstN initState
              drawInfos  := [DI n x origin initAngle, DI x n pFirstN aFirstN]
           -- call `placeNext` with the two placed nodes
           in placeNext drawInfos secState
        Just (c,a) =>
          let aFirstN   := oneAngle a
              pFirstN   := translate c aFirstN
              secState  := updateNode x (Just n) pFirstN aFirstN s
              drawInfos := [DI n x c a, DI x n  pFirstN aFirstN]
           in placeNext drawInfos secState


--------------------------------------------------------------------------------
--      Test
--------------------------------------------------------------------------------

--stateToAtom : State k -> Fin k -> Adj k SmilesBond SmilesAtomAT -> SmilesAtomP
--stateToAtom xs n a = { position := maybe origin coord $ index n xs } a.label
--
--parameters {k : _}
--           (g : IGraph k SmilesBond SmilesAtomAT)
--  initState : State k
--  initState = replicate k Nothing
--
--  infoTransfer : State k -> Graph SmilesBond SmilesAtomP
--  infoTransfer xs = G _ $ mapWithCtxt (stateToAtom xs) g
--
--covering
--toPosition : Graph SmilesBond SmilesAtomAT -> Graph SmilesBond SmilesAtomP
--toPosition (G 0 ig) = G 0 empty
--toPosition (G (S k) ig) = infoTransfer ig (draw ig [0] (initState ig))
--
--covering
--drawSmilesMol' : String -> Either String (Graph SmilesBond SmilesAtomP)
--drawSmilesMol' s =
--  case readSmiles' s of
--    Left x  => Left x
--    Right x => Right $ toPosition $ perceiveSmilesAtomTypes x
--
---- for drawing tool
--covering
--public export
--drawSmilesMol : String -> Graph SmilesBond SmilesAtomP
--drawSmilesMol smiles =
--  case drawSmilesMol' smiles of
--   Left _  => G 0 empty
--   Right m => m
--
--covering
--main : IO ()
--main =
--  case drawSmilesMol' "C(C)(C)" of
--    Left x  => putStrLn x
--    Right x => putStrLn $ pretty show show x.graph
--
--
