module Text.Smiles.Writer

import Text.Smiles.Types
import Text.Molfile.Types
import Data.Tree
import Text.Smiles.Parser
import Data.Graph.Indexed.Query.DFS
import Data.Array.Core

%default total

-- Printing Trees -------------------------------------------------------------
-- Smiles String to Tree with index and label
idxLabelTree : Interpolation n => IGraph k e n -> Tree (Fin k) -> IO ()
idxLabelTree g = putStrLn . prettyTree False . map pretty
  where
    pretty : Fin k -> String
    pretty x = "\{show x}: \{lab g x}"

smilesIdxLabelTree : String -> IO ()
smilesIdxLabelTree s =
  case readSmiles' s of
       Left e   => putStrLn "An error occured"
       Right (G _ g) => traverse_ (idxLabelTree g) $ dff' g

-- Smiles to label, with brackets and bonds
insertBond : IGraph k SmilesBond n -> Fin k -> Fin k -> String
insertBond g p c = case elab g p c of
                         Nothing   => ""
                         Just Sngl => ""
                         Just bo   => interpolate bo

treeString3 :
     Interpolation n
  => IGraph k SmilesBond n
  -> Tree (Fin k)
  -> String
treeString3 g (T c cs) =
  "\{lab g c}\{children g c cs}"
  where
    children : IGraph k SmilesBond n -> Fin k -> Forest (Fin k) -> String
    children g _ []               = ""
    children g p [h@(T c _)]      = insertBond g p c ++ treeString3 g h
    children g p (h@(T c _) :: t) =
      "(\{insertBond g p c}\{treeString3 g h})\{children g p t}"

forestString2 :
     Interpolation n
  => IGraph k SmilesBond n
  -> Forest (Fin k)
  -> String
forestString2 g []       = ""
forestString2 g [h]      = treeString3 g h
forestString2 g (h :: t) = "\{treeString3 g h}.\{forestString2 g t}"

smilesIdxLabelTree3 : String -> IO ()
smilesIdxLabelTree3 s =
  case readSmiles' s of
       Left e   => putStrLn "An error occured"
       Right (G _ g) => putStrLn $ forestString2 g $ dff' g

------------------------------------------------------------------------------
-- es gibt einen bestehenden type chem-lib (smiles parser, types)?
record RingInfo k where
  constructor RI
  neighbour : Fin k
  edge : SmilesBond
  ringId : Nat

record Node k where
  constructor MkNode
  label : SmilesAtom
  parentEdge : Maybe SmilesBond
  -- rings : RingInfo k
  --

insertBond2 : Node k -> String
insertBond2 c@(MkNode _ pE) = case pE of
                         Nothing   => ""
                         Just Sngl => ""
                         Just Arom => "" -- skipping arom for now
                         Just bo   => interpolate bo

treeString4 : Tree (Node k) -> String
treeString4 (T c@(MkNode v _) cs) =
  "\{v}\{children cs}"
  where
    children : Forest (Node k) -> String
    children []               = ""
    children [h@(T c _)] = insertBond2 c ++ treeString4 h
    children (h@(T c _) :: t) =
      "(\{insertBond2 c}\{treeString4 h})\{children t}"

-- könnte eine zeile sein (fastConcat, intersperse, map) ( in dieser Reihenfolge )
forestString3 : Forest (Node k) -> String
forestString3 []       = ""
forestString3 [h]      = treeString4 h
forestString3 (h :: t) = "\{treeString4 h}.\{forestString3 t}"

------------------------------------------------------------------------------
-- State Monad Version
------------------------------------------------------------------------------
record State s a where
  constructor S
  run : s -> (s,a)

Functor (State s) where
  map f (S run) = S $ \st => let (st2,v) := run st in (st2,f v)

Applicative (State s) where
  pure v = S $ \st => (st,v)
  S run1 <*> S run2 =
    S $ \st =>
      let (st2, fun) := run1 st
          (st3, val) := run2 st2
       in (st3, fun val)

Monad (State s) where
  S run1 >>= f =
    S $ \st =>
      let (st2,val) := run1 st
       in run (f val) st2

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

eval : s -> State s a -> a
eval ini (S run) = snd $ run ini

get : State s s
get = S $ \st => (st,st)

put : s -> State s ()
put st = S $ \_ => (st,())

mod : (s -> s) -> State s ()
mod f = get >>= put . f

----------------------------------------------------------------------------
parentEdge :
     IGraph k SmilesBond SmilesAtom
  -> Maybe (Fin k)
  -> Fin k
  -> Maybe SmilesBond
parentEdge _ Nothing  _ = Nothing
parentEdge g (Just p) v = elab g p v

covering
buildNodeTree :
     IGraph k SmilesBond SmilesAtom
  -> Tree (Fin k)
  -- eher ein record type nehmen: fields sind Dinge über die wir Buch führen
  -- rings, parent, etc
  -> State (Maybe (Fin k)) (Tree (Node k))
buildNodeTree g (T v ts) = do
  p <- get                             -- read curent parent
  put (Just v)                         -- set yourself as parent
  ts2 <- traverse (buildNodeTree g) ts -- process children
  put p                                -- restore old parend
  pure (T (MkNode (lab g v) (parentEdge g p v)) ts2) -- return built node

covering
buildNodeForest :
     IGraph k SmilesBond SmilesAtom
  -> Forest (Fin k)
  -> Forest (Node k)
buildNodeForest g ts = eval Nothing (traverse (buildNodeTree g) ts)

covering
smilesIdxLabelTree5 : String -> IO ()
smilesIdxLabelTree5 s =
  case readSmiles' s of
       Left e   => putStrLn "An error occured"
       Right (G _ g) =>
        putStrLn $ forestString3 $ buildNodeForest g $ dff' g



-- issues github:
-- -> PR machen, im PR Kommentare schreiben.
-- -> Es git Syntax für Todo lists in PR
-- in chem lib gibt es ein Beispiel in einem geschlossenen PR
-- PR #89 in chem-lib
-- issues eher für main und kommentare für feature branches -> PR

-- [TODO] Rings: easy but not the best approach:
--               [];[1];[1,2];[1,2,3];[1,3];[3];[]
-- (braucht mehr Info; welche Edges?, Fin k -> wo sind Öffnungen etc.
-- aktuelle Node -> Liste von neighbours mit children vergleichen
-- bereits registrierter Ringschluss?
-- 1. Node k anpassen
-- 2.

-- ([TODO] Bonustask: Refactor using linear types)

