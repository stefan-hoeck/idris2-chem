module Main

import Control.RIO.App
import Control.RIO.Console
import Control.RIO.Logging

import Data.String
import Data.Vect
import Text.Molfile
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

mol : ChemRes [MolParseErr] MolFile
mol =
  readMol
    Virtual
    """

      Mrv2219 08252310162D

      8  8  0  0  0  0            999 V2000
      -11.3170    4.0393    0.0000 C   0  0  0  0  0  0  0  0  0  0  0  0
      -12.0314    3.6268    0.0000 C   0  0  0  0  0  0  0  0  0  0  0  0
      -12.0314    2.8018    0.0000 C   0  0  0  0  0  0  0  0  0  0  0  0
      -11.3170    2.3893    0.0000 C   0  0  0  0  0  0  0  0  0  0  0  0
      -10.6025    2.8018    0.0000 C   0  0  0  0  0  0  0  0  0  0  0  0
      -10.6025    3.6268    0.0000 C   0  0  0  0  0  0  0  0  0  0  0  0
      -11.3170    4.8643    0.0000 O   0  0  0  0  0  0  0  0  0  0  0  0
       -9.8880    2.3893    0.0000 Cl  0  0  0  0  0  0  0  0  0  0  0  0
      1  2  1  0  0  0  0
      2  3  2  0  0  0  0
      3  4  1  0  0  0  0
      4  5  2  0  0  0  0
      5  6  1  0  0  0  0
      1  6  2  0  0  0  0
      1  7  1  0  0  0  0
      5  8  1  0  0  0  0
    M  END
    """
