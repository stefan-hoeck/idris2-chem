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
record RingInfo k where
  constructor RI
  neighbour : Fin k
  ring : Ring

record Node k where
  constructor MkNode
  label : SmilesAtom
  parentEdge : Maybe SmilesBond
  rings : List (RingInfo k)

record NodeState k where
  constructor NS
  parent : Maybe (Fin k)
  rings : List (RingInfo k)
  nextRingNr : RingNr
  openRings : List ((Fin k, Fin k), RingNr)

showRingNr : List (RingInfo k) -> String
showRingNr []                     = ""
showRingNr [ri@(RI _ r@(R rNr@(MkRingNr nr _) _))]    = show nr
showRingNr (ri@(RI _ r@(R rNr@(MkRingNr nr _) _)::t)) = show nr ++ showRingNr t


insertRingNr : Node k -> String
insertRingNr n@(MkNode _ _ [])                         = ""
insertRingNr n@(MkNode _ _ [ri@(RI _ r@(R rNr@(MkRingNr nr _) _))])    = show nr
insertRingNr n@(MkNode _ _ (ri@(RI _ r@(R rNr@(MkRingNr nr _) _))::t)) =
  show nr ++ showRingNr t

insertBond2 : Node k -> String
insertBond2 c@(MkNode _ pE _) = case pE of
                         Nothing   => ""
                         Just Sngl => ""
                         Just Arom => ""
                         Just bo   => interpolate bo

treeString4 : Tree (Node k) -> String
treeString4 (T c@(MkNode v _ _) cs) =
  let rNr := insertRingNr c
   in "\{v}\{rNr}\{children cs}"
  where
    children : Forest (Node k) -> String
    children []               = ""
    children [h@(T c _)]      = insertBond2 c ++ treeString4 h
    children (h@(T c _) :: t) =
      "(\{insertBond2 c}\{treeString4 h})\{children t}"

forestString3 : Forest (Node k) -> String
forestString3 = fastConcat . intersperse "." . map treeString4
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

getDirectChildren : Tree (Fin k) -> List (Fin k)
getDirectChildren (T _ ts) = map (\(T c _) => c) ts

-- rings = neighbours - parent - children
dropChildren :
     List (Fin k)
  -> List (Fin k, e)
  -> Maybe (Fin k)
  -> List (Fin k, e)
dropChildren children neighbours Nothing =
  filter (\(n,_) => not (elem n children)) neighbours
dropChildren children neighbours p =
  filter (\(n,_) => not (elem n children) && not (Just n == p)) neighbours

compVisN :
     IGraph k SmilesBond SmilesAtom
  -> Fin k -- current
  -> Maybe (Fin k) -- parent
  -> Tree (Fin k)
  -> NodeState k
  -> List (RingInfo k)
compVisN g c p t pNS@(NS _ _ nNr _) =
  let nPairs := neighboursAsPairs g c
      children := getDirectChildren t
      filtered := dropChildren children nPairs p
      -- kleinste nicht benutzte ringnr verwenden statt 0 wenn möglich
      -- ringnr idealerweise wiederverwenden
   in map (\(n,e) => RI n (R nNr (Just e))) filtered

covering
buildNodeTree :
     IGraph k SmilesBond SmilesAtom
  -> Tree (Fin k)
  -> State (NodeState k) (Tree (Node k))
buildNodeTree g t@(T v ts) = do
  pNS@(NS p ri ringNr@(MkRingNr nr _ ) openR) <- get    -- read curent parent

  let nextRingNr = case refineRingNr (nr + 1) of
                         Just nextRingNr => nextRingNr
                         Nothing         => 0
  put (NS (Just v) ri nextRingNr openR)    -- set yourself as parent
  ts2 <- traverse (buildNodeTree g) ts -- process children
  put pNS                              -- restore old parend
  pure (T (MkNode (lab g v) (parentEdge g p v) (compVisN g v p t pNS)) ts2)

covering
buildNodeForest :
     IGraph k SmilesBond SmilesAtom
  -> Forest (Fin k)
  -> Forest (Node k)
  -- dummy values
buildNodeForest g ts = eval (NS Nothing [] 0 []) (traverse (buildNodeTree g) ts)

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

