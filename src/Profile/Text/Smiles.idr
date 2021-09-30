module Profile.Text.Smiles

import Data.List1
import Data.Nat
import Data.String
import Profile.Profiler
import Text.Smiles

mol : String
mol = "C[C@@H]1CCCN(C1)C(=O)[C@@H](C)Oc2ccccc2"

isRes : Parser.Result -> Bool
isRes (End _) = True
isRes _       = False

testParser : () -> Bool
testParser () = isRes $ parse mol

export
profile : IO ()
profile = do
  profileAndReport $
    MkTask "parse smiles" testParser 300000 ItIsSucc

  case parse mol of
    End g      => putStrLn "Parsing successfull" >>
                  putStrLn (pretty bond atom g)
    Stuck r cs => putStrLn #"Parsing stopped at \#{pack cs}"# >>
                  printLn r
