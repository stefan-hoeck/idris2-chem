module Text.Smiles.Writer

import Text.Smiles.Types
import Text.Molfile.Types
import Data.Tree
import Text.Smiles.Parser
import Data.Graph.Indexed.Query.DFS

%default total

-- Printing Trees -------------------------------------------------------------
-- String Tree
firstTree : Forest String -> Maybe (Tree String)
firstTree []      = Nothing
firstTree (h ::t) = Just h

printTree : Forest String -> IO ()
printTree f = case firstTree f of
                   Just t => putStrLn (prettyTree False t)
                   _      => putStrLn "No Tree found"

testTree1 : Forest String
testTree1 = [T "C" [T "C" [], T "O" []]]

-- Label Tree
testTree2 : Tree SmilesAtom
testTree2 =
  T (SubsetAtom C False)
    [ T (SubsetAtom C False) []
    , T (SubsetAtom O False) []
    ]

labelTree : Tree SmilesAtom -> String
labelTree t = prettyTree False (map saToString t)
  where saToString : SmilesAtom -> String
        saToString (SubsetAtom e _ ) = show e
        saToString (Bracket a)       = show a -- does this make sense?

printSmilesAtom : Tree SmilesAtom -> IO ()
printSmilesAtom = putStrLn . labelTree

-- Index Tree
indexTree : Tree (Fin n) -> String
indexTree = prettyTree False . map show

printIndexTree : Tree (Fin n) -> IO ()
printIndexTree = putStrLn . indexTree

testTree3: Tree (Fin 4)
testTree3 =
  T (FZ)
    [ T (FS FZ)
      [ T (FS (FS FZ)) [], T (FS(FS(FS FZ))) []
    ]]

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
treeString : Tree (Fin n) -> String
treeString (T v cs) = show v ++ children cs
  where
    children : List (Tree (Fin n)) -> String
    children []     = ""
    children [h]    = treeString h
    children (h::t) = "(\{treeString h})\{children t}"

treeSmiles1 : Tree (Fin n) -> IO ()
treeSmiles1 = putStrLn . treeString

-- Index and Label Tree
treeSmiles2 : Tree (Fin n) -> IO ()




