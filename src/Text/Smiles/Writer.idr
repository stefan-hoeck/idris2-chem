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
  label : SmilesAtom
  -- parentNode : Maybe (Fin k) -- could be removed later
  -- parentEdge : Maybe SmilesBond
  -- rings : List (RingInfo k)

insertBond2 : IGraph k SmilesBond n -> Node k -> Node k -> String
insertBond2 g p@(MkNode pm _) c@(MkNode m _) = case elab g pm m of
                         Nothing   => ""
                         Just Sngl => ""
                         Just bo   => interpolate bo

treeString4 :
     IGraph k SmilesBond SmilesAtom
  -> Tree (Node k)
  -> String
treeString4 g (T c@(MkNode m v) cs) =
  "\{v}\{children g c cs}"
  where
    children :
         IGraph k SmilesBond SmilesAtom
      -> Node k
      -> Forest (Node k)
      -> String
    children g _ []               = ""
    children g p [h@(T c _)] = insertBond2 g p c ++ treeString4 g h
    children g p@(MkNode pm _ ) (h@(T c@(MkNode m _) _) :: t) =
      "(\{insertBond2 g p c}\{treeString4 g h})\{children g p t}"

forestString3 :
     IGraph k SmilesBond SmilesAtom
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
        putStrLn $ forestString3 g $ dffWith' g (\v => MkNode v (lab g v))

--------------------------------------------------------------------------------
---- State Monad Version
--------------------------------------------------------------------------------
--record State s a where
--  constructor S
--  run : s -> (s,a)
--
--Functor (State s) where
--  map f (S run) = S $ \st => let (st2,v) := run st in (st2,f v)
--
--Applicative (State s) where
--  pure v = S $ \st => (st,v)
--  S run1 <*> S run2 =
--    S $ \st =>
--      let (st2, fun) := run1 st
--          (st3, val) := run2 st2
--       in (st3, fun val)
--
--Monad (State s) where
--  S run1 >>= f =
--    S $ \st =>
--      let (st2,val) := run1 st
--       in run (f val) st2
--
----------------------------------------------------------------------------------
---- Utilities
----------------------------------------------------------------------------------
--
--eval : s -> State s a -> a
--eval ini (S run) = snd $ run ini
--
--get : State s s
--get = S $ \st => (st,st)
--
--put : s -> State s ()
--put st = S $ \_ => (st,())
--
--mod : (s -> s) -> State s ()
--mod f = get >>= put . f

------------------------------------------------------------------------------
--covering
--zipWithParent2 : Tree a -> State (Maybe a) (Tree (Maybe a, a))
--zipWithParent2 (T v ts) = do
--  p <- get -- read parent
--  put (Just v) -- set current as new parent
--  ts2 <- traverse zipWithParent2 ts
--  put p -- restore old parent
--  pure (T (p,v) ts2)
--
--covering
--buildNodeTree :
--     IGraph k SmilesBond SmilesAtom
--  -> Tree (Fin k)
--  -> State (Maybe (Fin k)) (Tree (Node k))
--buildNodeTree g (T v ts) = do
--  p <- get
--  put (Just v)
--  ts2 <- traverse (buildNodeTree g) ts
--  put p
--  pure (T (MkNode v (lab g v)) ts2)
--
----  pure (T (MkNode v (lab g v) (parentEdge g p v)) ts2)
--covering
--buildNodeForest :
--     IGraph k SmilesBond SmilesAtom
--  -> Forest (Fin k)
--  -> Forest (Node k)
--buildNodeForest g forest = eval Nothing (traverse (buildNodeTree g) forest)
--
--covering
--smilesIdxLabelTree5 : String -> IO ()
--smilesIdxLabelTree5 s =
--  case readSmiles' s of
--       Left e   => putStrLn "An error occured"
--       Right (G _ g) =>
--        let forest = dff' g
--            nodes = buildNodeForest g forest
--        in putStrLn $ forestString3 g nodes



-- [TODO] Square brackets
-- [TODO] Rings: easy but not the best approach:
--               [];[1];[1,2];[1,2,3];[1,3];[3];[]
-- [TODO] Aromaticity ("c1ccccc1" should give "c1cccccc1, not in c:c:c:c:c:c")
-- -> Just Arom => ""?
-- ([TODO] Bonustask: Refactor using State Monad)
-- ([TODO] Bonustask: Refactor using linear types)

