module Prog.Pretty

import Prog.Util

%default total

act : List String -> SmilesGraph -> Prog ()
act [] (G _ g) = stdoutLn (pretty interpolate interpolate g)
act _ _        = invalid

export
fromSmiles : String -> Prog SmilesGraph
fromSmiles = fromResult . readSmiles

export
prettySmiles : List String -> Prog ()
prettySmiles (s::t) = fromSmiles s >>= act t
prettySmiles []     = invalid
