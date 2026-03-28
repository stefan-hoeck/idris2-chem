module Prog.Cycles

import Prog.Pretty
import Prog.Util
import Data.Graph.Indexed.Ring.Relevant
import Data.Graph.Indexed.Ring.Relevant.Types

%default total

printCycle : Cycle k -> Prog ()
printCycle (C n _ _) = prntLn n

act : SmilesGraph -> Prog ()
act (G _ g) = traverse_ printCycle $ mcb (computeCrAndMCB g)

export
cycles : List String -> Prog ()
cycles [s] = fromSmiles s >>= act
cycles _   = invalid
