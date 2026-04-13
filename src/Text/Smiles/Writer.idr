module Text.Smiles.Writer

import Text.Smiles.Types
import Text.Smiles.Parser
import Text.Molfile.Types
import Data.Tree
import Data.Array.Core
import Data.Graph.Indexed.Query.DFS
import Control.Monad.State
import Derive.Prelude

%default total
%language ElabReflection

------------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------------
record RingData k where
  constructor RD
  edge : Edge k SmilesBond
  ring : Ring

%runElab deriveIndexed "RingData" [Eq]

record Node k where
  constructor MkNode
  label : SmilesAtom
  parentEdge : Maybe SmilesBond
  rings : List (RingData k)

record NodeState k where
  constructor NS
  parent : Maybe (Fin k)
  openRings : List (RingData k)

%runElab deriveIndexed "NodeState" [Eq]
------------------------------------------------------------------------------
-- SMILES Rendering
------------------------------------------------------------------------------
ringNr : RingData k -> RingNr
ringNr (RD _ (R nr _)) = nr

renderRingNr : List (RingData k) -> String
renderRingNr =
  fastConcat . map (interpolate . ringNr) . sortBy (compare `on` ringNr)

renderBond : Node k -> String
renderBond c@(MkNode _ pE _) = case pE of
                         Nothing   => ""
                         Just Sngl => ""
                         Just Arom => ""
                         Just bo   => interpolate bo

renderTree : Tree (Node k) -> String
renderTree (T c@(MkNode v _ rings) cs) =
  let rNr := renderRingNr rings
   in "\{v}\{rNr}\{children cs}"

public export
renderForest : Forest (Node k) -> String
renderForest = fastConcat . intersperse "." . map renderTree
-------------------------------------------------------------------------------
-- Rings
-------------------------------------------------------------------------------
findClosableOpenRing :
     Fin k -- neighbour
  -> Fin k -- current
  -> List (RingData k)
  -> Maybe (RingData k)
findClosableOpenRing n c =
  find (\rd =>
    let e = edge rd in
    (node1 e == c && node2 e == n) ||
    (node1 e == n && node2 e == c))

allocateRingNr : List (RingData k) -> RingNr
allocateRingNr ors =
   fromMaybe 0 $
     find (\x => not (elem x (map ringNr ors)))
          (mapMaybe refineRingNr [1..99])

-------------------------------------------------------------------------------
-- Traversal Helpers
-------------------------------------------------------------------------------

parameters (g : IGraph k SmilesBond SmilesAtom)

  parentE : Maybe (Fin k) -> Fin k -> Maybe SmilesBond
  parentE (Just p) v = elab g p v
  parentE Nothing  _ = Nothing

  -- rings = neighbours - parent - children
  computeNodeContext :
       Fin k
    -> Maybe (Fin k)
    -> Tree (Fin k)
    -> List (RingData k)
    -> List (RingData k)
  computeNodeContext c p (T _ ts) openR =
    foldl step openR filtered
    where
      children : List (Fin k)
      children = map (\(T c _) => c) ts

      filtered : List (Fin k, SmilesBond)
      filtered =
        filter
          (\(n, _) => not (elem n children) && not (Just n == p))
          (neighboursAsPairs g c)

      -- close an existing ring or open a new one
      step : List (RingData k) -> (Fin k, SmilesBond) -> List (RingData k)
      step ors (n, e) =
        case findClosableOpenRing n c ors of
          Just rd => filter (\r => ringNr r /= ringNr rd) ors
          Nothing              =>
            case mkEdge c n e of
              Just edge => RD edge (R (allocateRingNr ors) Nothing) :: ors
              Nothing   => ors

  zipL : Forest (Fin k) -> State (NodeState k) (Forest (Node k))

  buildNodeTree : Tree (Fin k) -> State (NodeState k) (Tree (Node k))
  buildNodeTree t@(T v ts) = do
    pNS@(NS p openR) <- get
    -- get info for current node
    let openR'  = computeNodeContext v p t openR
        ringChanges =
          filter (\x => not (elem x openR)) openR' ++
          filter (\x => not (elem x openR')) openR

    put (NS (Just v) openR') -- set current node as parent
    ts2 <- zipL ts -- process children
    put pNS -- restore old parent

    pure (T (MkNode (lab g v) (parentE p v) ringChanges) ts2)

  zipL []      = pure []
  zipL (t::ts) = [| buildNodeTree t :: zipL ts |]

  public export
  buildNodeForest : Forest (Fin k) -> Forest (Node k)
  buildNodeForest ts = evalState (NS Nothing []) (zipL ts)

export
graphToSmiles : {k : _} -> IGraph k SmilesBond SmilesAtom -> String
graphToSmiles g = renderForest $ buildNodeForest g $ dff' g

export
smilesRoundtrip : String -> String
smilesRoundtrip s =
  case readSmiles' s of
    Left _        => "Parse error."
    Right (G _ g) => graphToSmiles g

smilesRoundtripIO : String -> IO ()
smilesRoundtripIO = putStrLn . smilesRoundtrip


------------------------------------------------------------------------------
-- [TODO] Rewrite smilesIdxLabelTree3 with something like:
record RingInfo k where
  constructor RI
  neighbour : Fin k
  edge : SmilesBond
  ringId : Nat

record Node k where
  constructor MkNode
  node : Fin k -- could be removed later
  --label : SmilesAtom
  --parentNode : Maybe (Fin k) -- could be removed later
  --parentEdge : Maybe SmilesBond
  -- rings : List (RingInfo k)

insertBond2 : IGraph k SmilesBond n -> Node k -> Node k -> String
insertBond2 g p@(MkNode pm) c@(MkNode m) = case elab g pm m of
                         Nothing   => ""
                         Just Sngl => ""
                         Just bo   => interpolate bo

treeString4 :
     Interpolation n
  => IGraph k SmilesBond n
  -> Tree (Node k)
  -> String
treeString4 g (T c@(MkNode m) cs) =
  "\{lab g m}\{children g c cs}"
  where
    children : IGraph k SmilesBond n -> Node k -> Forest (Node k) -> String
    children g _ []               = ""
    children g p [h@(T c _)] = insertBond2 g p c ++ treeString4 g h
    children g p@(MkNode pm) (h@(T c@(MkNode m) _) :: t) =
      "(\{insertBond2 g p c}\{treeString4 g h})\{children g p t}"


forestString3 :
  Interpolation n
  => IGraph k SmilesBond n
  -> Forest (Node k)
  -> String
forestString3 g []       = ""
forestString3 g [h]      = treeString4 g h
forestString3 g (h :: t) = "\{treeString4 g h}.\{forestString3 g t}"

smilesIdxLabelTree4 : String -> IO ()
smilesIdxLabelTree4 s =
  case readSmiles' s of
       Left e   => putStrLn "An error occured"
       Right (G _ g) =>
        putStrLn $ forestString3 g $ dffWith' g MkNode

-- String -> IGraph k e n -> Forest (Fin k) -> Tree ("Data I need") -> String
-- record Node k
-- label : SmilesAtom, rings : List RingInfo, parent : Maybe SmilesBond,
-- (node : Fin k), (parentNode : Maybe (Fin k))



-- [TODO] Square brackets
-- [TODO] Rings: easy but not the best approach:
--               [];[1];[1,2];[1,2,3];[1,3];[3];[]
-- [TODO] Aromaticity ("c1ccccc1" should give "c1cccccc1, not in c:c:c:c:c:c")
-- ([TODO] Bonustask: Refactor using State Monad)
-- ([TODO] Bonustask: Refactor using linear types)

