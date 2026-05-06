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
-- This is an aid for debugging and will be removed later
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
-- Types
------------------------------------------------------------------------------
-- This will be moved to Types.idr eventually
record RingInfo k where
  constructor RI
  neighbour : Fin k
  ring : Ring

record Node k where
  constructor MkNode
  label : SmilesAtom
  parentEdge : Maybe SmilesBond
  rings : List (RingInfo k)

record OpenRings k where
  constructor OR
  openRings: List ((Fin k, Fin k), RingNr)

record NodeState k where
  constructor NS
  parent : Maybe (Fin k)
  rings : List (RingInfo k)
  openRings : OpenRings k

------------------------------------------------------------------------------
-- SMILES Rendering
------------------------------------------------------------------------------
showRingNr : RingInfo k -> String
showRingNr (RI _ (R (MkRingNr n _) _)) = show n

renderRingNr : Node k -> String
renderRingNr (MkNode _ _ ris) = fastConcat $ map showRingNr ris

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


-------------------------------------------------------------------------------
-- Rings
-------------------------------------------------------------------------------
findOpenRing :
     Fin k
  -> OpenRings k
  -> Maybe RingNr
findOpenRing c (OR ors) =
  case find (\((a,b),_) => a == c || b == c) ors of
  Just (_, ringNr) => Just ringNr
  Nothing => Nothing

closeRing : RingNr -> OpenRings k -> OpenRings k
closeRing nr (OR ors) =
  OR (filter (\(_, ringNr) => ringNr /= nr) ors)

allocateRingNr : OpenRings k -> RingNr
allocateRingNr (OR ors) =
  let used = map snd ors
   in fromMaybe 0 $
        find (\x => not (elem x used)) (mapMaybe refineRingNr [1..99])

openRing :
     (Fin k, Fin k)
  -> RingNr
  -> OpenRings k
  -> OpenRings k
openRing edge nr (OR ors) = OR ((edge, nr) :: ors)

-------------------------------------------------------------------------------
-- Traversal Helpers
-------------------------------------------------------------------------------
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

computeNodeContext :
     IGraph k SmilesBond SmilesAtom
  -> Fin k
  -> Maybe (Fin k)
  -> Tree (Fin k)
  -> OpenRings k
  -> (List (RingInfo k), OpenRings k)
computeNodeContext g c p t openR =
  let nPairs   := neighboursAsPairs g c
      children := getDirectChildren t
      filtered := dropChildren children nPairs p
   in case filtered of
        [] => ([], openR)

        (n, e) :: _ =>
          let (nr, openR') :=
                case findOpenRing c openR of
                  Just openNr =>
                    (openNr, closeRing openNr openR)

                  Nothing =>
                    let freshNr := allocateRingNr openR
                        newOpenR := openRing (c, n) freshNr openR
                     in (freshNr, newOpenR)

              listRI := map (\(n, e) => RI n (R nr (Just e))) filtered
           in (listRI, openR')

covering
buildNodeTree :
     IGraph k SmilesBond SmilesAtom
  -> Tree (Fin k)
  -> State (NodeState k) (Tree (Node k))
buildNodeTree g t@(T v ts) = do
  pNS@(NS p ri openR) <- get    -- read curent parent

  -- get info for current node
  let (listRI, openR') := computeNodeContext g v p t openR

  put (NS (Just v) listRI openR') -- set current node as parent
  ts2 <- traverse (buildNodeTree g) ts  -- process children
  put pNS                               -- restore old parent

  pure (T (MkNode (lab g v) (parentEdge g p v) listRI) ts2)

covering
buildNodeForest :
     IGraph k SmilesBond SmilesAtom
  -> Forest (Fin k)
  -> Forest (Node k)
buildNodeForest g ts =
  eval (NS Nothing [] (OR [])) (traverse (buildNodeTree g) ts)

-- currently still breaks for: "C12C34C56C78C91C2C3C4C5C6C7C8C9"
covering
smilesRoundtrip : String -> IO ()
smilesRoundtrip s =
  case readSmiles' s of
       Left e   => putStrLn "An error occured"
       Right (G _ g) =>
        putStrLn $ renderForest $ buildNodeForest g $ dff' g

