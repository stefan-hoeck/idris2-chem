module Main

import Chem.Data.Elem
import Chem.Data.Isotope
import Data.List
import Data.String
import System
import System.File

%default total

elemTxt, isoTxt, datSrc : String
elemTxt = "build/elem.txt"
isoTxt  = "build/isotopes.txt"
datSrc  = "src/Chem/Data.idr"

genStr : String
genStr = "-- Generated Data"

||| Extracts data from the `dat` string, generates Idris code from it, and
||| attaches it to `src` after the `-- Generated Data` line.
export
adjustSource : (s_elem, s_iso, src : String) -> String
adjustSource s_elem s_iso src =
  let elems       := Elem.generateLines s_elem
      isos        := Isotope.generateLines s_iso
      (pre, _::t) := break (genStr ==) (lines src) | _ => src
   in unlines $ pre ++ [genStr, "", elems, "", isos]

covering
main : IO ()
main = do
  Right s_elem <- readFile elemTxt | Left e => die (show e)
  Right s_iso  <- readFile isoTxt  | Left e => die (show e)
  Right src    <- readFile datSrc  | Left e => die (show e)
  Right ()  <- writeFile datSrc (adjustSource s_elem s_iso src)
    | Left e => die (show e)
  pure ()

