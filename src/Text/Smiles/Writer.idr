module Text.Smiles.Writer

import Text.Smiles.Types
import Text.Molfile.Types
import Data.Tree

%default total
-- String Tree ----------------------------------------------------------------
firstTree : Forest String -> Maybe (Tree String)
firstTree []      = Nothing
firstTree (h ::t) = Just h

printTree : Forest String -> IO ()
printTree f = case firstTree f of
                   Just t => putStrLn (prettyTree False t)
                   _      => putStrLn "No Tree found"

testTree1 : Forest String
testTree1 = [T "C" [T "C" [], T "O" []]]

-- Label Tree ------------------------------------------------------------
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

-- Index Tree ----------------------------------------------------------------
indexTree : Tree (Fin n) -> String
indexTree = prettyTree False . map show

printIndexTree : Tree (Fin n) -> IO ()
printIndexTree = putStrLn . indexTree

testTree3: Tree (Fin 3)
testTree3 =
  T (FZ)
    [ T (FS FZ)      []
    , T (FS (FS FZ)) []
    ]


