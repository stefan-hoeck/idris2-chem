module Main

import Data.String
import Text.FC
import Text.Smiles.Lexer
import Text.Smiles.Parser

main : IO ()
main = do
  putStr "Please enter a SMILES string (q to quit): "
  s <- map trim getLine
  case s of
    "q" => putStrLn "Goodbye!"
    _   => case parse s of
      Left (fc,e) => putStrLn (printParseError s fc e) >> main
      Right x     => putStrLn (pretty interpolate interpolate x) >> main
