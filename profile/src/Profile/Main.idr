module Profile.Main

import Data.List1
import Data.String
import Profile
import Profile.Text.Lex.Element
import Profile.Text.Smiles
import System

fromArgs : List String -> String -> Bool
fromArgs [_,p] = case split ('=' ==) p of
  "--only" ::: [s] => isInfixOf s
  _                => const False
fromArgs _ = const True

main : IO ()
main = do
  select <- fromArgs <$> getArgs
  runDefault select Table show $ Group "all"
    [ Element.bench
    , Smiles.bench
    ]
