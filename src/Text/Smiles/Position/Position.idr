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

updateNode :
     Fin k
  -> (parent : Maybe (Fin k))
  -> Point Mol
  -> Angle
  -> State k
  -> State k
updateNode n par pt a s =
  case index n s of
    Nothing => replaceAt n (Just (I par pt a)) s
    _       => updateAt n (map {parent := par , coord := pt , angle := a }) s

childAngle : (current : Angle) -> (count,place : Nat) -> Angle
childAngle cur n p =
  case n of
   0 => zero  -- this case should not occur
   1 => if (cur >= zero && cur <= halfPi) || (cur >= pi && cur <= threeHalfPi)
           then cur - piThird
           else cur + piThird
   2 => if (cur >= zero && cur <= halfPi) || (cur >= pi && cur <= threeHalfPi)
           then if (p == 1) then cur - piThird else cur + piThird
           else if (p == 1) then cur + piThird else cur - piThird
   3 => if p == 1 then cur + halfPi
        else if p == 2 then cur
        else if p == 3 then cur - halfPi
        else zero  -- should not occur
   _ => zero  -- should not occur

drawChildNode :
     (current,child : Fin k)
  -> (neigh,place : Nat)
  -> State k
  -> Maybe (State k)
drawChildNode cur ch nc p s =
  let Just curP := getCoord cur s | Nothing => Nothing
      Just curA := getAngle cur s | Nothing => Nothing
      vect      := polar BondLengthInAngstrom curA
      newP      := translate vect curP
      newA      := childAngle curA nc p
   in pure $ updateNode ch (Just cur) newP newA s

-- TODO: do not forget to update the neighbour nodes
drawChildStar : (current : Fin k) -> List (Fin k) -> State k -> State k
drawChildStar cur xs s = ?drawChildStar_rhs

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
           (g : IGraph k SmilesBond SmilesAtomAT)
--           {auto se : DrawerSettings}

-- TODO: There are (at this time) 5 `assert_total` functions here!!!!!!!!!!!!!
--  covering
  draw : List (Fin k) -> State k -> State k
  draw []        s = s
  draw (n :: ns) s =
    -- get all neighbours that needs to be checked for drawing
    let allNeigh := map fst (pairs (neighbours g n))
        parent   := parent n s
        toDrawN  := maybe allNeigh (\p => delete p allNeigh) parent
        -- TODO: Prove that this list gets smaller
        -- TODO: Sort `toDrawN` for deciding, which branch should be drawn first
        drawList := toDrawN ++ ns
    -- set coords for the neighbours
     in case getCoord n s of
       -- Starting Node: Repeat drawing of this node with its start coord and
       -- angle
       Nothing =>
         assert_total $ draw (n :: ns) $ updateNode n Nothing origin ((1.0 / 6.0) * pi) s
       _       =>
         case toDrawN of
           -- draw other branch if exists
           []            => draw ns s
           [x]           =>
             let Just s1 := drawChildNode n x 1 1 s | Nothing => s
              in assert_total $ draw drawList s1
           [x1,x2]       =>
             let Just s1 := drawChildNode n x1 2 1 s  | Nothing => s
                 Just s2 := drawChildNode n x2 2 2 s1 | Nothing => s
              in assert_total $ draw drawList s2
           [x1,x2,x3]    =>
             let Just s1 := drawChildNode n x1 3 1 s  | Nothing => s
                 Just s2 := drawChildNode n x2 3 2 s1 | Nothing => s
                 Just s3 := drawChildNode n x2 3 3 s2 | Nothing => s
              in assert_total $ draw drawList s3
           xs            => assert_total $ draw drawList s -- TODO: add 'drawChildStar n xs s'


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

--covering
toPosition : Graph SmilesBond SmilesAtomAT -> Graph SmilesBond SmilesAtomP
toPosition (G 0 ig) = G 0 empty
toPosition (G (S k) ig) = infoTransfer ig (draw ig [0] (initState ig))

--covering
drawSmilesMol: String -> Either String (Graph SmilesBond SmilesAtomP)
drawSmilesMol s =
  case readSmiles' s of
    Left x  => Left x
    Right x => Right $ toPosition $ perceiveSmilesAtomTypes x

-- for drawing tool
--covering
public export
drawSmilesMol' : String -> Graph SmilesBond SmilesAtomP
drawSmilesMol' smiles =
  case drawSmilesMol smiles of
   Left _  => G 0 empty
   Right m => m

--covering
main : IO ()
main =
  case drawSmilesMol "C(C)(C)" of
    Left x  => putStrLn x
    Right x => putStrLn $ pretty show show x.graph


