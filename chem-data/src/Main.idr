module Main

import Chem.Data.Elem
import System
import System.File

%default total

elemTxt, datSrc : String
elemTxt = "build/elem.txt"
datSrc  = "src/Chem/Data.idr"

covering
main : IO ()
main = do
  Right dat <- readFile elemTxt                        | Left e => die (show e)
  Right src <- readFile datSrc                         | Left e => die (show e)
  Right ()  <- writeFile datSrc (adjustSource dat src) | Left e => die (show e)
  pure ()

