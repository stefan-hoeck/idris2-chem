module Prog.Trees

import Data.Tree
import Prog.Pretty
import Prog.Util
import Data.Graph.Indexed.Query.DFS

%default total

printTree : Interpolation n => IGraph k e n -> Tree (Fin k) -> Prog ()
printTree g = putStrLn . prettyTree False . map pretty
  where
    pretty : Fin k -> String
    pretty x = "\{show x}: \{lab g x}"

act : SmilesGraph -> Prog ()
act (G _ g) = traverse_ (printTree g) $ dff' g

export
trees : List String -> Prog ()
trees [s] = fromSmiles s >>= act
trees _   = invalid
