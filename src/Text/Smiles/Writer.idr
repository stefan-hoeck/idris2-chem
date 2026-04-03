module Text.Smiles.Writer

import Text.Smiles.Types
import Text.Molfile.Types
import Data.Tree
import Text.Smiles.Parser
import Data.Graph.Indexed.Query.DFS
import Data.Array.Core

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
treeString : Tree (Fin k) -> String
treeString (T v cs) = show v ++ children cs
  where
    children : List (Tree (Fin k)) -> String
    children []     = ""
    children [h]    = treeString h
    children (h::t) = "(\{treeString h})\{children t}"

treeSmiles1 : Tree (Fin n) -> IO ()
treeSmiles1 = putStrLn . treeString

-- Smiles to label, with brackets, without bonds
treeString2 : Interpolation n => IGraph k e n -> Tree (Fin k) -> String
treeString2 g (T v cs) =
  "\{lab g v}\{children g cs}"
  where
    children : IGraph k e n -> List (Tree (Fin k)) -> String
    children g []       = ""
    children g [h]      = treeString2 g h
    children g (h :: t) = "(\{treeString2 g h})\{children g t}"

forestString : Interpolation n => IGraph k e n -> List (Tree (Fin k)) -> String
forestString g []       = ""
forestString g [h]      = treeString2 g h
forestString g (h :: t) = "\{treeString2 g h}.\{forestString g t}"

smilesIdxLabelTree2 : String -> IO ()
smilesIdxLabelTree2 s =
  case readSmiles' s of
       Left e   => putStrLn "An error occured"
       Right (G _ g) => putStrLn $ forestString g $ dff' g

-- Smiles to label, with brackets and bonds
-- [TODO] Include bonds
--        a) find adj list
--        b) find bond order and connection node
--        c) place bond accordingly in string
--           -If (double/triple) bond from current node to parent node exists,
--            we can add this bond e.g. "=" before the current node label.
--            I think this should work regardless of branch or no branch.
-- [TODO] Square brackets
-- [TODO] Rings
-- [TODO] Refactor

insertBond : IGraph k SmilesBond n -> Fin k -> Fin k -> String
insertBond g p c = case elab g p c of
                         Nothing   => ""
                         Just Sngl => ""
                         Just bo   => interpolate bo


treeString3 : Interpolation n => IGraph k SmilesBond n -> Tree (Fin k) -> String
treeString3 g (T c cs) =
  "\{lab g c}\{children g c cs}"
  where
    children : IGraph k SmilesBond n -> Fin k -> List (Tree (Fin k)) -> String
    children g _ []               = ""
    children g p [h@(T c _)]      = insertBond g p c ++ treeString3 g h
    children g p (h@(T c _) :: t) =
      "(\{insertBond g p c}\{treeString3 g h})\{children g p t}"

forestString2 : Interpolation n => IGraph k SmilesBond n -> List (Tree (Fin k)) -> String
forestString2 g []       = ""
forestString2 g [h]      = treeString3 g h
forestString2 g (h :: t) = "\{treeString3 g h}.\{forestString2 g t}"

smilesIdxLabelTree3 : String -> IO ()
smilesIdxLabelTree3 s =
  case readSmiles' s of
       Left e   => putStrLn "An error occured"
       Right (G _ g) => putStrLn $ forestString2 g $ dff' g

