module Text.Lex.Formula

import Chem
import Data.Finite
import Derive.Prelude
import Text.ILex
import Text.ILex.DStack

%default total
%language ElabReflection

public export
data FState : List Type -> Type where
  FIni : FState [Formula]
  FEl  : FState [Elem,Formula]

%runElab deriveIndexed "FState" [Show,ConIndex]

FSz : Bits32
FSz = 1 + cast (conIndexFState $ FEl)

inBoundsFState : (s : FState ts) -> (cast (conIndexFState s) < FSz) === True

export %inline
Cast (FState ts) (Index FSz) where
  cast v = I (cast $ conIndexFState v) @{mkLT $ inBoundsFState v}

public export
0 SK : Type -> Type
SK = DStack FState Void

parameters {auto sk : SK q}

  %inline
  onelem : Elem -> StateAct q FState FSz
  onelem el FIni t         = dput FEl $ el::t
  onelem el FEl  (e::f::t) = dput FEl $ el::insertElem e f::t

  onnat : Integer -> StateAct q FState FSz
  onnat n FEl (e::f::t) = dput FIni $ insert e (cast n) f::t
  onnat n p t           = dput p t

el : Steps q FSz SK
el = vals symbol (\el => \(sk # t) => dact (onelem el) t) values

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
    (FIni:>(f::_))   # t => Right f # t
    (FEl:>(e::f::_)) # t => Right (insertElem e f) # t

export
formula : P1 q (BoundedErr Void) FSz SK Formula
formula =
  P (cast FIni) (init $ FIni:>[neutral]) formulaTrans
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
