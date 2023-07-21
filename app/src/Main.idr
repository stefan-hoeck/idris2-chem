module Main

import Control.RIO.App
import Control.RIO.Console
import Control.RIO.Logging

import Data.String
import Text.Smiles
import Chem.AtomType

0 ErrTypes : List Type
ErrTypes = [HErr, ATErr, SmilesParseErr]

handlers : Console => All (Handler ()) ErrTypes
handlers =
  [ \x => cputStrLn "\{x}\n"
  , \x => cputStrLn "\{x}\n"
  , \x => cputStrLn "\{x}\n"
  ]

printAtom : Atom (Chirality,AtomType) -> String
printAtom (MkAtom e _ _ _ l _) = "\{show e} (\{show $ snd l})"

app : Console => RIO Void ()
app = do
  cputStr "Please enter a SMILES string (q to quit): "
  s <- map trim cgetLine
  case s of
    "q" => cputStr "Goodbye!"
    _   => do
      handleAll @{handlers} $ do
        G _ graph <- liftEither $ smilesToAtomType s
        cputStrLn (pretty interpolate printAtom graph)
        cputStrLn ""
      app


main : IO ()
main = run $ app @{stdIO}
