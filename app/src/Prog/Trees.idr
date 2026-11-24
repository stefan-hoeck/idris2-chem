module Prog.Trees

import Data.Tree
import Prog.Pretty
import Prog.Util
import Data.Graph.Indexed.Query.DFS

%default total

printTree : Interpolation n => (g : Graph e n) -> Tree (Node g) -> Prog ()
printTree g = putStrLn . prettyTree False . map pretty
  where
    pretty : Node g -> String
    pretty x = "\{show x}: \{lab x}"

act : SmilesGraph -> Prog ()
act g = traverse_ (printTree g) $ dff' g

export
trees : List String -> Prog ()
trees [s] = fromSmiles s >>= act
trees _   = invalid
