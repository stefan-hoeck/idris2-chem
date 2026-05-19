module Text.Smiles.Writer

import Text.Smiles.Types
import Text.Molfile.Types
import Data.Tree
import Text.Smiles.Parser
import Data.Graph.Indexed.Query.DFS
import Data.Array.Core
import Control.Monad.State

-- import Derive.Prelude
-- import Derive.Finite
-- import Derive.Refined


%default total
%language ElabReflection

------------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------------
-- This will be moved to Types.idr eventually
record RingData k where
  constructor RD
  edge : Edge k SmilesBond
  ring : Ring -- contains RingNr and Maybe SmilesBond

-- %runElab derive "RingData" [Eq]

record Node k where
  constructor MkNode
  label : SmilesAtom
  parentEdge : Maybe SmilesBond
  rings : List (RingData k)

record NodeState k where
  constructor NS
  parent : Maybe (Fin k)
  openRings : List (RingData k)

-- %runElab derive "NodeState" [Eq]

Eq (RingData k) where
  RD e1 r1 == RD e2 r2 = e1 == e2 && r1 == r2
------------------------------------------------------------------------------
-- SMILES Rendering
------------------------------------------------------------------------------
renderRingNr : Node k -> String
renderRingNr (MkNode _ _ rings) =
  fastConcat $
    map (\(RD _ (R nr _)) => interpolate nr) $
      sortBy (compare `on` (\(RD _ (R nr _ )) => nr)) rings

renderBond : Node k -> String
renderBond c@(MkNode _ pE _) = case pE of
                         Nothing   => ""
                         Just Sngl => ""
                         Just Arom => ""
                         Just bo   => interpolate bo

renderTree : Tree (Node k) -> String
renderTree (T c@(MkNode v _ _) cs) =
  let rNr := renderRingNr c
   in "\{v}\{rNr}\{children cs}"
  where
    children : Forest (Node k) -> String
    children []               = ""
    children [h@(T c _)]      = renderBond c ++ renderTree h
    children (h@(T c _) :: t) =
      "(\{renderBond c}\{renderTree h})\{children t}"

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

closeRing : RingNr -> List (RingData k) -> List (RingData k)
closeRing nr = filter $ \(RD _ (R rn _)) => rn /= nr

allocateRingNr : List (RingData k) -> RingNr
allocateRingNr ors =
  let used = map (\(RD _ (R nr _ )) => nr) ors
   in fromMaybe 0 $
        find (\x => not (elem x used))
             (mapMaybe refineRingNr [1..99])

-------------------------------------------------------------------------------
-- Traversal Helpers
-------------------------------------------------------------------------------
parentEdge :
     IGraph k SmilesBond SmilesAtom
  -> Maybe (Fin k)
  -> Fin k
  -> Maybe SmilesBond
parentEdge g (Just p) v = elab g p v
parentEdge _ Nothing  _ = Nothing

-- rings = neighbours - parent - children
computeNodeContext :
     IGraph k SmilesBond SmilesAtom
  -> Fin k
  -> Maybe (Fin k)
  -> Tree (Fin k)
  -> List (RingData k)
  -> List (RingData k)
computeNodeContext g c p (T _ ts) openR =
  foldl step openR filtered
  where
    children : List (Fin k)
    children = map (\(T c _) => c) ts

    filtered : List (Fin k, SmilesBond)
    filtered =
      filter
        (\(n, _) => not (elem n children) && not (Just n == p))
        (neighboursAsPairs g c)

    step : List (RingData k) -> (Fin k, SmilesBond) -> List (RingData k)
    step ors (n, e) =
      case findClosableOpenRing n c ors of
        Just (RD _ (R nr _)) => closeRing nr ors
        Nothing              =>
          case mkEdge c n e of
            Just edge => RD edge (R (allocateRingNr ors) Nothing) :: ors
            Nothing   => ors

zipL :
     IGraph k SmilesBond SmilesAtom
  -> Forest (Fin k)
  -> State (NodeState k) (Forest (Node k))

buildNodeTree :
     IGraph k SmilesBond SmilesAtom
  -> Tree (Fin k)
  -> State (NodeState k) (Tree (Node k))
buildNodeTree g t@(T v ts) = do
  pNS@(NS p openR) <- get
  -- get info for current node
  let openR'  = computeNodeContext g v p t openR
      ringChanges =
        filter (\x => not (elem x openR)) openR' ++
        filter (\x => not (elem x openR')) openR

  put (NS (Just v) openR') -- set current node as parent
  ts2 <- zipL g ts -- process children
  put pNS -- restore old parent

  pure (T (MkNode (lab g v) (parentEdge g p v) ringChanges) ts2)

zipL g []      = pure []
zipL g (t::ts) = [| buildNodeTree g t :: zipL g ts |]

buildNodeForest :
     IGraph k SmilesBond SmilesAtom
  -> Forest (Fin k)
  -> Forest (Node k)
buildNodeForest g ts = evalState (NS Nothing []) (zipL g ts)

export
smilesRoundtrip : String -> String
smilesRoundtrip s =
  case readSmiles' s of
       Left e   => "An error occured"
       Right (G _ g) => renderForest $ buildNodeForest g $ dff' g

smilesRoundtripIO : String -> IO ()
smilesRoundtripIO = putStrLn . smilesRoundtrip

