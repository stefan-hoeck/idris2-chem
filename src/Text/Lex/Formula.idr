module Text.Lex.Formula

import Chem
import Data.List.Quantifiers.Extra
import Derive.Prelude
import Text.Bounds
import Text.FC
import Text.Lex.Elem
import Text.Lex.Manual

%language ElabReflection
%default total

public export
record FormulaErr where
  constructor FE
  formula : String
  context : FileContext
  error   : ParseError Void Void

%runElab derive "FormulaErr" [Eq,Show]

export
Interpolation FormulaErr where
  interpolate (FE s c e) = printParseError s c e

lexNat : Elem -> SafeTok Formula
lexNat e []        = Succ (singleton e 1) []
lexNat e (x :: xs) =
  if isDigit x
     then singleton e <$> dec1 (digit x) xs
     else Succ (singleton e 1) (x::xs)

lexPair : StrictTok e Formula
lexPair cs = case lexElement {orig} cs of
  Succ val xs => lexNat val xs
  Fail x y z  => Fail x y z

export
readFormula : Has FormulaErr es => String -> ChemRes es Formula
readFormula s = go begin neutral (unpack s) suffixAcc
  where
    go :
         Position
      -> Formula
      -> (ts : List Char)
      -> (0 acc : SuffixAcc ts)
      -> ChemRes es Formula
    go p1 f [] _      = Right f
    go p1 f cs (SA r) = case lexPair cs of
      Succ v xs2 @{p}     =>
        let p2 := endPos p1 p
         in go p2 (f <+> v) xs2 r
      Fail x e r =>
        let B v bs := boundedErr p1 x e r
         in Left . inject $ FE s (FC Virtual bs) v
