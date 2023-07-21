module Profile.Chem.AtomType

import Chem
import Chem.AtomType
import Data.List.Quantifiers.Extra
import Data.Maybe
import Data.String
import Profile
import Profile.Text.Smiles
import System.File
import Text.Smiles

0 Errs : List Type
Errs = [HErr, ATErr, SmilesParseErr]

calcAtomTypes : String -> Maybe (Graph Bond (Atom (Chirality,AtomType)))
calcAtomTypes str =
  either (const Nothing) Just $ smilesToAtomType {es = Errs} str

parseLines : Integer -> File -> IO (Either FileError ())
parseLines n f = do
  False <- fEOF f | True => pure $ Right ()
  Right str <- fGetLine f   | Left err => pure $ Left err
  Just _ <- pure (calcAtomTypes $ trim str)
    | st => parseLines (n+1) f
  parseLines (n+1) f

profile : IO ()
profile = do
  Right _ <- withFile "resources/zinc.txt" Read pure (parseLines 1)
    | Left err => printLn err
  pure ()

export
bench : Benchmark Void
bench = Group "Chem.AtomTypes" [
    Single "mol" (basic calcAtomTypes mol)
  , Single "strychnine" (basic calcAtomTypes strychnine)
  , Single "zinc" (singleIO profile)
  ]
