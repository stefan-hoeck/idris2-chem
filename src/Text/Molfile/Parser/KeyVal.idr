module Text.Molfile.Parser.KeyVal

import Derive.Prelude
import Syntax.T1
import Text.ILex
import Text.ILex.Derive
import Text.Molfile.Parser.Util

%default total
%language ElabReflection

public export
data Prim : Type where
  PS : String  -> Prim
  PI : Integer -> Prim

%runElab derive "Prim" [Show,Eq]

public export
data Val : Type where
  V : Prim -> Val
  L : List Prim -> Val

%runElab derive "Val" [Show,Eq]

public export
0 KeyVal : Type
KeyVal = Either Val (String,Val)

--------------------------------------------------------------------------------
--          Parser State
--------------------------------------------------------------------------------

%runElab deriveParserState "KSz" "KST"
  ["KIni","KVal","InStr","LStart","LVal","LEnd"]

data Part : Type where
  VS : SnocList KeyVal -> Part
  VK : SnocList KeyVal -> String -> Part
  VO : SnocList KeyVal -> Nat -> SnocList Prim -> Part
  VL : SnocList KeyVal -> String -> Nat -> SnocList Prim -> Part

public export
0 SK : Type -> Type
SK = Stack Void Part KSz

--------------------------------------------------------------------------------
-- Transformations
--------------------------------------------------------------------------------

parameters {auto sk : SK q}
  part : Prim -> Part -> F1 q KST
  part p (VS sx)          = putStackAs (VS $ sx:<Left (V p)) KIni
  part p (VK sx str)      = putStackAs (VS $ sx:<Right (str,V p)) KIni
  part p (VO sx k sp)     =
    case pred k of
      0 => putStackAs (VS $ sx:<Left (L $ sp<>>[p])) LEnd
      x => putStackAs (VO sx x (sp:<p)) LVal
  part p (VL sx str k sp) =
    case pred k of
      0 => putStackAs (VS $ sx:<Right (str,L $ sp<>>[p])) LEnd
      x => putStackAs (VL sx str x (sp:<p)) LVal

  key : String -> Part -> F1 q KST
  key s (VS sx) = putStackAs (VK sx s) KVal
  key s _       = pure KIni -- impossible

  %inline
  onPrim : Prim -> F1 q KST
  onPrim v = getStack >>= part v

  %inline
  onKey : ByteString -> F1 q KST
  onKey v = getStack >>= key (toString $ dropEnd 1 v)

  startList : Integer -> F1 q KST
  startList n =
    getStack >>= \case
      VS sx   => putStackAs (VO sx   (cast n) [<]) LVal
      VK sx s => putStackAs (VL sx s (cast n) [<]) LVal
      _       => pure KIni -- impossible

--------------------------------------------------------------------------------
-- Lexers
--------------------------------------------------------------------------------

size : RExp True
size = posdigit >> star digit

-- according to the spec (sic):
--   >> Strings that contain blank spaces or start
--   >> with left parenthesis or double quote, must be surrounded by
--   >> double quotes
--
-- to distinguish a string from a key, an unquoted string must not contain
-- an equals sign.
unquoted : RExp True
unquoted = start >> star uqc
  where
    uqc, start : RExp True
    uqc   = dot && not ' ' && not ')' && not '='
    start = uqc && not '"' && not '('

spaced : KST -> Steps q KSz SK -> DFA q KSz SK
spaced x ss =
  dfa $
    [ conv' (plus ' ') x
    , linecol' 1 6 ('-' >> newline >> "M  V30") x
    ] ++ ss

val : KST -> Steps q KSz SK -> DFA q KSz SK
val x ss =
  spaced x $
    [ conv integer (onPrim . PI . decimal)
    , read unquoted (onPrim . PS)
    , copen' '"' InStr
    ] ++ ss

toplevel : KST -> DFA q KSz SK
toplevel x =
  val KIni
    [ conv (plus alphaNum >> '=') onKey
    , copen' '(' LStart
    ]

str : DFA q KSz SK
str =
  dfa
    [ read (plus $ dot && not '"' && not '-') (pushStr InStr)
    , cexpr "\"\"" (pushStr InStr "\"")
    , cexpr '-'    (pushStr InStr "-")
    , linecol' 1 7 ('-' >> newline >> "M  V30 ") InStr
    , linecol' 1 6 ('-' >> newline >> "M  V30")  InStr
    , ccloseStr '"' (onPrim . PS)
    ]

--------------------------------------------------------------------------------
-- Parser
--------------------------------------------------------------------------------

kvTrans : Lex1 q KSz SK
kvTrans =
  lex1
    [ E KIni   $ toplevel KIni
    , E KVal   $ toplevel KVal
    , E LVal   $ val LVal []
    , E LStart $ spaced LStart [conv size (startList . decimal)]
    , E LEnd   $ spaced LEnd [cclose ')' (pure KIni)]
    , E InStr    str
    ]

kvErr : Arr32 KSz (SK q -> F1 q (BoundedErr Void))
kvErr =
  arr32 KSz (unexpected [])
    [ E InStr  $ unclosedIfEOI "\"" []
    , E LStart $ unclosedIfEOI "(" []
    , E LVal   $ unclosedIfEOI "(" []
    , E LEnd   $ unclosedIfEOI "(" [")"]
    ]

kvEOI : KST -> SK q -> F1 q (Either (BoundedErr Void) (List KeyVal))
kvEOI sk s t =
  case sk == KIni of
    False => arrFail SK kvErr sk s t
    True  => case getStack t of
      VS vs # t => Right (vs <>> []) # t
      _     # t => Right [] # t -- impossible

kv : P1 q (BoundedErr Void) KSz SK (List KeyVal)
kv = P KIni (init (VS [<])) kvTrans noChunk kvErr kvEOI

||| Parses V3000 key-value pairs from a (possibly multiline) bytestring.
export %inline
parseKeyVals : ByteString -> Either (ParseError Void) (List KeyVal)
parseKeyVals = parseBytes kv Virtual

test : String -> IO ()
test =
  either (putStrLn . interpolate) (traverse_ printLn) . parseKeyVals . cast

ml : String
ml =
  """
  FOO=12 BAR="quux" BAZ="this is a -
  M  V30 test" AND=(7 1 2 3 4 5   -
  M  V30 6 7) IM="not yet done"
  """
