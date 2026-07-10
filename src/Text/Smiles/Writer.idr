||| Writes a molecular graph (IGraph k SmilesBond SmilesAtom) out as a
||| SMILES string.
|||
||| Limitation: Currently only stereochemistry that is already explicitly
||| encoded in the graph is written into a SMILES string.
||| No stereochemistry is derived from atom coordinates.

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
  bothArom : Bool
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

  -- hock: for testability, this should not be under the parameters block,
  -- as it makes no use of `g` internally.
  bondSymbol : Bool -> SmilesBond -> String
  bondSymbol bothArom bo =
    if bo == (if bothArom then Arom else Sngl)
       then ""
       else interpolate bo

  bothAromatic : Fin k -> Fin k -> Bool
  bothAromatic a b = isArom (lab g a) && isArom (lab g b)

  -- hock: for testability, this should not be under the parameters block,
  -- as it makes no use of `g` internally.
  ringNr : RingData k -> RingNr
  ringNr (RD _ (R nr _)) = nr

  renderRingNr : List (RingData k) -> String
  renderRingNr =
    fastConcat . map render . sortBy (compare `on` ringNr)
    where
      render : RingData k -> String
      render rd@(RD e _) =
        let bothArom = bothAromatic (node1 e) (node2 e)
         in bondSymbol bothArom (label e) ++ interpolate (ringNr rd)

  -- hock: for testability, this should not be under the parameters block,
  -- as it makes no use of `g` internally.
  renderBond : Node k -> String
  renderBond (MkNode _ pE bothArom _) = maybe "" (bondSymbol bothArom) pE

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

  -- hock: for testability, this should not be under the parameters block,
  -- as it makes no use of `g` internally.
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

  -- hock: for testability, this should not be under the parameters block,
  -- as it makes no use of `g` internally.
  allocateRingNr : List (RingData k) -> RingNr
  allocateRingNr ors =
     fromMaybe 0 $
       find (\x => not (elem x (map ringNr ors)))
            (mapMaybe refineRingNr [1..99])

-------------------------------------------------------------------------------
-- Traversal Helpers
-------------------------------------------------------------------------------

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
      -- hock: better:
      -- children = map value ts
      -- note also, that - for performance reasons - this should be bound
      -- to a variable in a `let` expression, otherwise it gets recomputed
      -- everytime it is needed in `filtered`

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
          Nothing =>
            maybe ors
                  (\edge => RD edge (R (allocateRingNr ors) Nothing) :: ors)
                  (mkEdge c n e)

  zipL : Forest (Fin k) -> State (NodeState k) (Forest (Node k))

  -- Rings that were opened or closed at this node.
  ringDelta : List (RingData k) -> List (RingData k) -> List (RingData k)
  ringDelta openR openR' =
    filter (\x => not (elem x openR')) openR ++
    filter (\x => not (elem x openR )) openR'

    -- hock: avoid lambdas for readability
    -- filter (not . flip elem openR') openR ++
    -- filter (not . flip elem openR ) openR'

  -- bond to parent (if any) and whether both atoms are aromatic
  parentInfo : Maybe (Fin k) -> Fin k -> (Maybe SmilesBond, Bool)
  parentInfo p v =
    ( maybe Nothing (\pn => elab g pn v) p
    , maybe False   (\pn => bothAromatic pn v) p
    )
    -- hock: use currying, if possible
    --       `maybe Nothing foo bar` is just monadic bind, so `foo >>= bar`
    -- (p >>= elab g v, maybe False (bothAromatic v) p)

  buildNodeTree : Tree (Fin k) -> State (NodeState k) (Tree (Node k))
  buildNodeTree t@(T v ts) = do
    pNS@(NS p openR) <- get

    -- get info for current node
    let openR'      = computeNodeContext v p t openR
        ringChanges = ringDelta openR openR'

    put (NS (Just v) openR') -- set current node as parent
    ts2 <- zipL ts           -- process children
    put pNS                  -- restore old parent

    let (pe, bothArom) = parentInfo p v

    pure (T (MkNode (lab g v) pe bothArom ringChanges) ts2)

  zipL []      = pure []
  zipL (t::ts) = [| buildNodeTree t :: zipL ts |]

  -- hock: Only use `public export` when stuff needs to reduce
  --       during unification. If you don't know what this means,
  --       you probably don't need `public export` for functions.
  public export
  buildNodeForest : Forest (Fin k) -> Forest (Node k)
  buildNodeForest ts = evalState (NS Nothing []) (zipL ts)

export
graphToSmiles : {k : _} -> IGraph k SmilesBond SmilesAtom -> String
graphToSmiles g = renderForest g . buildNodeForest g $ dff' g

-- hock: this should not be exported as it seems to not be very useful
-- (or well typed)
export
smilesRoundtrip : String -> String
smilesRoundtrip s =
  case readSmiles' s of
    Left _        => "Parse error."
    Right (G _ g) => graphToSmiles g

smilesRoundtripIO : String -> IO ()
smilesRoundtripIO = putStrLn . smilesRoundtrip

