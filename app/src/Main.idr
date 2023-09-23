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
ErrTypes = [SmilesParseErr]

handlers : Console => All (Handler ()) ErrTypes
handlers = [ \x => cputStrLn "\{x}\n" ]

aromElem : Elem -> Bool -> String
aromElem e False = show e
aromElem e True  = toLower $ show e

printIso : AromIsotope -> String
printIso (MkAI e Nothing a)  = aromElem e a
printIso (MkAI e (Just n) a) = "\{show n}\{aromElem e a}"

printCharge : Charge -> String
printCharge 0    = ""
printCharge 1    = "+"
printCharge (-1) = "-"
printCharge c    = if c.value > 0 then "+\{show c.value}" else show c.value

printH : HCount -> String
printH 0 = ""
printH 1 = "; H"
printH n = "; H\{show n.value}"

printAtom : SmilesAtomAT -> String
printAtom (MkAtom e c () () h t _ _) =
  "\{printIso e}\{printCharge c} (\{t.name}\{printH h})"

app : Console => RIO Void ()
app = do
  cputStr "Please enter a SMILES string (q to quit): "
  s <- map trim cgetLine
  case s of
    "q" => cputStr "Goodbye!"
    _   => do
      handleAll @{handlers} $ do
        G _ graph <- liftEither . map perceiveSmilesAtomTypes $ readSmiles s
        cputStrLn (pretty interpolate printAtom graph)
        cputStrLn ""
      app

main : IO ()
main = run $ app @{stdIO}
