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

-- TODO: sort out already drawn nodes
-- Neighbours without parent node
lNeigh : IGraph k e n -> (cur,parent : Fin k) -> List (Fin k)
lNeigh g n p = delete p $ map fst (pairs $ neighbours g n)

initAngle : Angle
initAngle = negate 1.0 / 6.0 * pi

calcAngle : (neededAngles : Nat) -> Angle -> List Angle
calcAngle 0 a = []
calcAngle 1 a =
  if (a >= zero && a <= halfPi) || (a >= pi && a <= threeHalfPi)
    then [a + twoThirdPi]
    else [a - twoThirdPi]
calcAngle 2 a = [a + twoThirdPi, a - twoThirdPi]
calcAngle 3 a = ?calcThreeAngle
calcAngle c a = ?calcStarAngles

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

needStartPlaced : Fin k -> State k -> Bool
needStartPlaced x = isNothing . index x

molOrigin : Point Mol
molOrigin = P 0.0 0.0

translate : Point Mol -> Angle -> Point Mol
translate p a = Point.translate (polar BondLengthInAngstrom a) p

concatToDI : State k -> Fin k -> List (DrawInfo k) -> List (DrawInfo k)
concatToDI s n l =
  let Just parent := getParent n s | Nothing => l
      Just coord  := getCoord n s  | Nothing => l
      Just angle  := getAngle n s  | Nothing => l
   in DI n parent coord angle :: l


--------------------------------------------------------------------------------
--      Depth first traversal
--------------------------------------------------------------------------------

parameters {0 k : _}
           (g : IGraph k SmilesBond SmilesAtomAT)

  -- gets a list of the last drawn nodes, whose neighbours had to be drawn next
  covering
  placeNext : List (DrawInfo k) -> State k -> State k
  placeNext []               s = s
  placeNext (DI n p c a :: xs) s =
        -- list of neighbours without parent
    let lNeigh   := lNeigh g n p
        newS     := ?drawAndUpdate
        infoList := foldr (concatToDI newS) [] lNeigh
     in placeNext (infoList ++ xs) newS

  -- should place the start node and (if present) one neighbour. Respectivly,
  -- one node is the parent node of the other and vice versa.
  covering
  placeInit : Fin k -> State k -> State k
  placeInit n s = case map fst (pairs $ neighbours g n) of
    -- no neighbours, isolated atom
    []        => replaceAt n (Just (I Nothing origin initAngle)) s
    (x :: xs) =>
      -- place the first neighbour
      let initState  := replaceAt n (Just (I Nothing molOrigin initAngle)) s
          aFirstN    := oneAngle initAngle
          pFirstN    := translate molOrigin aFirstN
          secState   := replaceAt x (Just (I (Just n) pFirstN aFirstN)) initState
          drawInfos  := [DI n x origin initAngle, DI x n pFirstN aFirstN]
       -- call `placeNext` with the two placed nodes
       in placeNext drawInfos secState

-- draws only coherent chains!
  covering
  draw : (start : Fin k) -> State k -> State k
  draw n s =
    case needStartPlaced n s of
      True  => placeInit n s
      False =>
        let listInfos := ?listDrawInfo
         in placeNext listInfos s


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
