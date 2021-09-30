module Profile.Text.Zinc

import Data.List
import Data.String
import Data.Vect
import System.File
import Text.Smiles

parseLines : Nat -> File -> IO (Either FileError ())
parseLines n f = do
  False <- fEOF f | True => pure $ Right ()
  Right str <- fGetLine f   | Left err => pure $ Left err
  End _ <- pure (parse $ trim str) 
    | st => putStrLn #"Line \#{show n}: \#{show st}. (\#{str})"# >> parseLines (n+1) f
  parseLines (n+1) f

export
profile : IO ()
profile = do
  Right _ <- withFile "resources/zinc.txt" Read pure (parseLines 1)
    | Left err => printLn err
  pure ()
