module Profile.Text.Smiles

import Chem
import Data.List.Quantifiers.Extra
import Data.String
import Profile
import System.File
import Text.Smiles

export
mol : String
mol = "C[C@@H]1CCCN(C1)C(=O)[C@@H](C)Oc2ccccc2"

export
strychnine : String
strychnine = "O=C7N2c1ccccc1[C@@]64[C@@H]2[C@@H]3[C@@H](OC/C=C5\[C@@H]3C[C@@H]6N(CC4)C5)C7"

parse' : String -> ChemRes [SmilesParseErr] Mol
parse' s = parse s

parseLines : Integer -> File -> IO (Either FileError ())
parseLines n f = Prelude.do
  False <- fEOF f | True => pure $ Right ()
  Right str <- fGetLine f   | Left err => pure $ Left err
  Right _ <- pure (parse' $ trim str)
    | Left (Here st) => putStrLn "Line \{show n}: \{st}" >> parseLines (n+1) f
  parseLines (n+1) f

profile : IO ()
profile = do
  Right _ <- withFile "resources/zinc.txt" Read pure (parseLines 1)
    | Left err => printLn err
  pure ()

export
bench : Benchmark Void
bench = Group "Text.Smiles.Parse" [
    Single "mol1" (basic parse' mol)
  , Single "strychnine" (basic parse' strychnine)
  , Single "zinc" (singleIO profile)
  ]
