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

-- Tree to Smiles String ------------------------------------------------------
-- Index Tree
treeString : Tree (Fin k) -> String
treeString (T v cs) = show v ++ children cs
  where
    children : List (Tree (Fin k)) -> String
    children []     = ""
    children [h]    = treeString h
    children (h::t) = "(\{treeString h})\{children t}"

treeSmiles1 : Tree (Fin n) -> IO ()
treeSmiles1 = putStrLn . treeString

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

-- [TODO] Rewrite smilesIdxLabelTree3 with something like:
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

