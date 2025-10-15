module Geom.Gen2D.Debug

import Chem
import Data.String
import Geom.Gen2D.Types
import Text.Smiles

%default total

attachPoint : AttachPoint n -> String
attachPoint None         = ""
attachPoint (Attach a n) = " (\{show a} -> \{show n})"

export
showComponent : Component k e n -> String
showComponent (C a xs r _) =
 let pre := the String $ if r then "Ring" else "Chain"
  in "\{pre}: \{show xs}\{attachPoint a}"

export
printComponents : Graph e n -> IO ()
printComponents (G _ g) = traverse_ (putStrLn . showComponent) (components g)

export
test : String -> IO ()
test s =
  case readSmiles' s of
    Left x  => putStrLn "\{x}"
    Right x => printComponents x
