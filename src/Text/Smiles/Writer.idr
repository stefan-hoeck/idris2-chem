module Text.Smiles.Writer

import Text.Smiles.Types
import Text.Molfile.Types
import Data.Tree

%default total
writeSmiles : SmilesGraph -> String

-- Tree SmilesAtom ------------------------------------------------------------
testTree1 : Tree SmilesAtom
testTree1 =
  T (SubsetAtom C False)
    [ T (SubsetAtom C False) []
    , T (SubsetAtom O False) []
    ]

treeToSmiles : Tree SmilesAtom -> String
treeToSmiles t = prettyTree False (map show t)

printSmilesAtom : Tree SmilesAtom -> IO ()
printSmilesAtom = putStrLn . treeToSmiles

-- Tree String ----------------------------------------------------------------
firstTree : Forest String -> Maybe (Tree String)
firstTree []      = Nothing
firstTree (h ::t) = Just h

printTree : Forest String -> IO ()
printTree f = case firstTree f of
                   Just t => putStrLn (prettyTree False t)
                   _      => putStrLn "No Tree found"

testTree2 : Forest String
testTree2 = [T "C" [T "C" [], T "O" []]]
