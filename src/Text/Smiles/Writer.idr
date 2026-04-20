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


-- [TODO] Square brackets
-- [TODO] Rings: easy but not the best approach:
--               [];[1];[1,2];[1,2,3];[1,3];[3];[]
-- [TODO] Aromaticity ("c1ccccc1" should give "c1cccccc1, not in c:c:c:c:c:c")
-- -> Just Arom => ""?
-- ([TODO] Bonustask: Refactor using State Monad)
-- ([TODO] Bonustask: Refactor using linear types)

