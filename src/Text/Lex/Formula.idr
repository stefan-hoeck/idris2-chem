module Text.Lex.Formula

import Chem
import Data.Finite
import Derive.Prelude
import Text.ILex
import Text.ILex.String.DStack

%default total
%language ElabReflection

data FState : SnocList Type -> Type where
  FIni : FState [<Formula]
  FEl  : FState [<Formula,Elem]

%runElab deriveIndexed "FState" [Show,ConIndex]

FSz : Bits32
FSz = 1 + cast (conIndexFState $ FEl)

inBoundsFState : (s : FState ts) -> (cast (conIndexFState s) < FSz) === True

export %inline
Cast (FState ts) (Index FSz) where
  cast v = I (cast $ conIndexFState v) @{mkLT $ inBoundsFState v}

0 SK : Type -> Type
SK = DStack FState Void

parameters {auto sk : SK q}

  %inline
  onelem : Elem -> StateAct q FState FSz
  onelem el FIni sx         = dput FEl $ sx:<el
  onelem el FEl  (sx:<f:<e) = dput FEl $ sx:<insertElem e f:<el

  onnat : Integer -> StateAct q FState FSz
  onnat n FEl (sx:<f:<e) = dput FIni $ sx :< insert e (cast n) f
  onnat n p   sx         = dput p sx

el : Steps q FSz SK
el = vals symbol (\el,_ => dact (onelem el)) values

formulaTrans : Lex1 q FSz SK
formulaTrans =
  lex1
    [ entry FIni $ dfa el
    , entry FEl  $ dfa (conv decimal (dact . onnat . decimal) :: el)
    ]

formulaErr : Arr32 FSz (SK q -> F1 q (BoundedErr Void))
formulaErr = errs []

formulaEOI : Index FSz -> SK q -> F1 q (Either (BoundedErr Void) Formula)
formulaEOI v sk t =
  case read1 sk.stack_ t of
    (_:<f:>FIni)   # t => Right f # t
    (_:<f:<e:>FEl) # t => Right (insertElem e f) # t

public export
formula : P1 q (BoundedErr Void) Formula
formula =
  P (cast FIni) (init $ [<neutral]:>FIni) formulaTrans
    (\_ => (Nothing #)) formulaErr formulaEOI

inBoundsFState FIni = Refl
inBoundsFState FEl  = Refl

export %inline
parseFormula : String -> Either (ParseError Void) Formula
parseFormula = parseString formula Virtual

testFormula : String -> IO ()
testFormula s =
  case parseFormula s of
    Left x  => putStrLn "\{x}"
    Right f => printLn f
