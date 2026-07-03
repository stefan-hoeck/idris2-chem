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
  parentArom : Bool
  rings : List (RingData k)

record NodeState k where
  constructor NS
  parent : Maybe (Fin k)
  openRings : List (RingData k)

%runElab deriveIndexed "NodeState" [Eq]

------------------------------------------------------------------------------
-- SMILES Rendering
------------------------------------------------------------------------------

parameters (g : IGraph k SmilesBond SmilesAtom)

  ringNr : RingData k -> RingNr
  ringNr (RD _ (R nr _)) = nr

  -- refactor?
  renderRingNr : List (RingData k) -> String
  renderRingNr =
    fastConcat . map render . sortBy (compare `on` ringNr)
    where
      render : RingData k -> String
      render rd@(RD e _) =
        let bo        = label e
            bothArom  = isArom (lab g (node1 e)) && isArom (lab g (node2 e))
            isDefault = if bothArom then bo == Arom else bo == Sngl
            sym       = if isDefault then "" else interpolate bo
         in sym ++ interpolate (ringNr rd)

  -- refactor?
  renderBond : Node k -> String
  renderBond (MkNode v pE bothArom _) =
    case pE of
      Nothing => ""
      Just bo =>
        let isDefault = if bothArom then bo == Arom else bo == Sngl
         in if isDefault then "" else interpolate bo

  renderTree : Tree (Node k) -> String
  renderTree (T c@(MkNode v _ _ rings) cs) =
    let rNr := renderRingNr rings
     in "\{v}\{rNr}\{children cs}"
    where
      children : Forest (Node k) -> String
      children []               = ""
      children [h@(T c _)]      = renderBond c ++ renderTree h
      children (h@(T c _) :: t) =
        "(\{renderBond c}\{renderTree h})\{children t}"

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
  -- is this needed? maybe use directly?
  parentE : Maybe (Fin k) -> Fin k -> Maybe SmilesBond
  parentE Nothing  _ = Nothing
  parentE (Just p) v = elab g p v

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

      -- format?
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

  -- refactor?
  buildNodeTree : Tree (Fin k) -> State (NodeState k) (Tree (Node k))
  buildNodeTree t@(T v ts) = do
    pNS@(NS p openR) <- get
    -- get info for current node
    let openR'  = computeNodeContext v p t openR
        ringChanges =
          filter (\x => not (elem x openR')) openR ++
          filter (\x => not (elem x openR )) openR'

    put (NS (Just v) openR') -- set current node as parent
    ts2 <- zipL ts -- process children
    put pNS -- restore old parent

    let pe        = parentE p v
        bothArom  = maybe False (\pn => isArom (lab g pn) && isArom (lab g v)) p

    pure (T (MkNode (lab g v) pe bothArom ringChanges) ts2)

  zipL []      = pure []
  zipL (t::ts) = [| buildNodeTree t :: zipL ts |]

  public export
  buildNodeForest : Forest (Fin k) -> Forest (Node k)
  buildNodeForest ts = evalState (NS Nothing []) (zipL ts)

export
graphToSmiles : {k : _} -> IGraph k SmilesBond SmilesAtom -> String
graphToSmiles g = renderForest g $ buildNodeForest g $ dff' g

export
smilesRoundtrip : String -> String
smilesRoundtrip s =
  case readSmiles' s of
    Left _        => "Parse error."
    Right (G _ g) => graphToSmiles g

smilesRoundtripIO : String -> IO ()
smilesRoundtripIO = putStrLn . smilesRoundtrip

