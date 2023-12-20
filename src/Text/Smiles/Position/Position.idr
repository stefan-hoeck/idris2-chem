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

-- TODO: sort out already drawn nodes
-- Neighbours without parent node
lNeigh' : IGraph k e n -> (cur,parent : Fin k) -> List (Fin k)
lNeigh' g n p = delete p $ lNeigh g n

-- total count (also drawn ones) of neighbours
%inline
getCountNeigh : Fin k -> IGraph k e n -> Nat
getCountNeigh n g = length $ lNeigh g n

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
initAngle = (negate 1.0 / 6.0) * pi

molOrigin : Point Mol
molOrigin = P 0.0 0.0

updateNode :
     Fin k
  -> (parent : Maybe (Fin k))
  -> Point Mol
  -> Angle
  -> State k
  -> State k
updateNode n par pt a s = replaceAt n (Just (I par pt a)) s

translate : Point Mol -> Angle -> Point Mol
translate p a = Point.translate (polar BondLengthInAngstrom a) p

toListDI : State k -> Fin k -> List (DrawInfo k) -> List (DrawInfo k)
toListDI s n l =
  let Just parent := getParent n s | Nothing => l
      Just coord  := getCoord n s  | Nothing => l
      Just angle  := getAngle n s  | Nothing => l
   in DI n parent coord angle :: l

-- calculates the first angle
firstAngle : Angle -> Angle
firstAngle x =
  if (x >= zero && x <= halfPi) || (x >= pi && x <= threeHalfPi)
    then x - piThird
    else x + piThird

-- places the first neighbour
firstPosition :
     Fin k
  -> (parent : DrawInfo k)
  -> State k
  -> (State k, Angle)
firstPosition n (DI i _ c a) s =
  let newA :=
      if (a >= zero && a <= halfPi) || (a >= pi && a <= threeHalfPi)
        then a - piThird
        else a + piThird
      newP := translate c newA
   in (updateNode n (Just i) newP newA s, newA)

-- calc angles and coordinates for neighbours of a node and add to state
placeNeighbours : List (Fin k) -> (parent : DrawInfo k) -> State k -> State k
placeNeighbours []      di s = s
placeNeighbours [x]     di s = fst $ firstPosition x di s
placeNeighbours [x,y]   di s =
  let (firstState,fstA) := firstPosition x di s
      secAngle         := largestBisector [di.angle-pi,fstA]
      secPos           := translate di.coord secAngle
   in updateNode y (Just di.index) secPos secAngle firstState
placeNeighbours [x,y,z] di s =
  let (firstState,fstA) := firstPosition x di s
      bisectorAngle     := largestBisector [di.angle-pi,fstA]
      small1            := bisectorAngle - fromDegree 30.0
      small2            := bisectorAngle + fromDegree 30.0
      pos1              := translate di.coord small1
      pos2              := translate di.coord small2
      secondState       := updateNode y (Just di.index) pos1 small1 firstState
   in updateNode z (Just di.index) pos2 small2 secondState
placeNeighbours xs      di s = ?drawNeighbours_rhs5


--------------------------------------------------------------------------------
--      Depth first traversal
--------------------------------------------------------------------------------

parameters {0 k : _}
           (g : IGraph k SmilesBond SmilesAtomAT)

  -- gets a list of the last drawn nodes, whose neighbours had to be drawn next
  covering
  placeNext : List (DrawInfo k) -> State k -> State k
  placeNext []               s = s
  placeNext (di@(DI n p c a) :: xs) s =
        -- list of neighbours without parent
    let lNeigh   := lNeigh' g n p
        newS     := placeNeighbours lNeigh di s
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
              aFirstN    := firstAngle initAngle
              pFirstN    := translate molOrigin aFirstN
              secState   := updateNode x (Just n) pFirstN aFirstN initState
              drawInfos  := [DI n x origin initAngle, DI x n pFirstN aFirstN]
           -- call `placeNext` with the two placed nodes
           in placeNext drawInfos secState
        Just (c,a) =>
              -- assign parent node to stat node
          let initState := updateNode n (Just x) c a s
              aFirstN   := firstAngle a
              pFirstN   := translate c aFirstN
              secState  := updateNode x (Just n) pFirstN aFirstN initState
              drawInfos := [DI n x c a, DI x n  pFirstN aFirstN]
           in placeNext drawInfos secState


--------------------------------------------------------------------------------
--      Test
--------------------------------------------------------------------------------

stateToAtom : State k -> Fin k -> Adj k SmilesBond SmilesAtomAT -> SmilesAtomP
stateToAtom xs n a = { position := maybe origin coord $ index n xs } a.label

parameters {k : _}
           (g : IGraph k SmilesBond SmilesAtomAT)
  initState : State k
  initState = replicate k Nothing

  infoTransfer : State k -> Graph SmilesBond SmilesAtomP
  infoTransfer xs = G _ $ mapWithCtxt (stateToAtom xs) g

covering
toPosition : Graph SmilesBond SmilesAtomAT -> Graph SmilesBond SmilesAtomP
toPosition (G 0 ig) = G 0 empty
toPosition (G (S k) ig) = infoTransfer ig (placeInit ig 0 (initState ig))

covering
drawSmilesMol' : String -> Either String (Graph SmilesBond SmilesAtomP)
drawSmilesMol' s =
  case readSmiles' s of
    Left x  => Left x
    Right x => Right $ toPosition $ perceiveSmilesAtomTypes x

-- for drawing tool
covering
public export
drawSmilesMol : String -> Graph SmilesBond SmilesAtomP
drawSmilesMol smiles =
  case drawSmilesMol' smiles of
   Left _  => G 0 empty
   Right m => m

covering
main : IO ()
main =
  case drawSmilesMol' "C(C)(C)" of
    Left x  => putStrLn x
    Right x => putStrLn $ pretty show show x.graph


