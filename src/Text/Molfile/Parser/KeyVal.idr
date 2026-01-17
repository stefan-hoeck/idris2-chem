module Text.Molfile.Parser.KeyVal

import Derive.Prelude
import Syntax.T1
import Text.ILex
import Text.ILex.Derive
import Text.Molfile.Parser.Util
import Text.Molfile.Types

%default total
%language ElabReflection

public export
data KV : Nat -> Type where
  S : String  -> KV n
  I : Integer -> KV n
  L : List (KV 0) -> KV (S n)
  P : String -> KV 1 -> KV 2

%runElab deriveIndexed "KV" [Show]

w1 : KV n -> KV 2
w1 (S s)   = S s
w1 (I i)   = I i
w1 (L xs)  = L xs
w1 (P s x) = P s x

w0 : KV 0 -> KV 1
w0 (S s) = S s
w0 (I i) = I i

public export
0 KeyVal : Type
KeyVal = KV 2

export
toString : KV n -> Maybe String
toString (S s) = Just s
toString _     = Nothing

export
toNat : KV n -> Maybe Nat
toNat (I i) = if i >= 0 then Just (cast i) else Nothing
toNat _     = Nothing

export
toNats : KV n -> Maybe (List Nat)
toNats (L xs) = traverse toNat xs
toNats _      = Nothing

export
lookupVal : String -> List KeyVal -> Maybe (KV 1)
lookupVal s []            = Nothing
lookupVal s (P k v :: xs) = if s == k then Just v else lookupVal s xs
lookupVal s (_     :: xs) = lookupVal s xs

--------------------------------------------------------------------------------
--          Parser State
--------------------------------------------------------------------------------

%runElab deriveParserState "KSz" "KST"
  ["KIni","Entry","KVal","InStr","LStart","LVal","LEnd","KErr","KDone"]

data Part : Type where
  VS : SnocList KeyVal -> Part
  VK : SnocList KeyVal -> String -> Part
  VO : SnocList KeyVal -> Nat -> SnocList (KV 0) -> Part
  VL : SnocList KeyVal -> String -> Nat -> SnocList (KV 0) -> Part

public export
0 SK : Type -> Type
SK = Stack MolErr Part KSz

--------------------------------------------------------------------------------
-- Transformations
--------------------------------------------------------------------------------

parameters {auto sk : SK q}
  part : KV 0 -> Part -> F1 q KST
  part p (VS sx)      = putStackAs (VS $ sx:<w1 p) Entry
  part p (VK sx s)    = putStackAs (VS $ sx:<P s (w0 p)) Entry
  part p (VO sx k sp) =
    case pred k of
      0 => putStackAs (VS $ sx:<(L $ sp<>>[p])) LEnd
      x => putStackAs (VO sx x (sp:<p)) LVal
  part p (VL sx s k sp) =
    case pred k of
      0 => putStackAs (VS $ sx:<P s (L $ sp<>>[p])) LEnd
      x => putStackAs (VL sx s x (sp:<p)) LVal

  key : String -> Part -> F1 q KST
  key s (VS sx) = putStackAs (VK sx s) KVal
  key s _       = pure KErr -- impossible

  %inline
  onPrim : KV 0 -> F1 q KST
  onPrim v = getStack >>= part v

  %inline
  onKey : ByteString -> F1 q KST
  onKey v = getStack >>= key (toUpper $ toString $ dropEnd 1 v)

  startList : ByteString -> F1 q KST
  startList bs =
   let n := cast {to = Nat} $ decimal bs
    in getStack >>= \case
         VS sx   => putStackAs (VO sx   n [<]) LVal
         VK sx s => putStackAs (VL sx s n [<]) LVal
         _       => pure KErr -- impossible

--------------------------------------------------------------------------------
-- Lexers
--------------------------------------------------------------------------------

||| the "M  V30" line prefix
public export
mv30 : RExp True
mv30 = like "M  V30"

||| Remainder of a (possibly mutli-line) entry of values and key-value pairs.
export
keyValRest : RExp True
keyValRest = dots >> star ('-' >> newline >> mv30 >> dots) >> newline

||| Recognizes some tokens, dropping any optional white space around them.
export %inline
spaced : HasBytes s => HasPosition s => Index r -> Steps q r s -> DFA q r s
spaced x ss = dfa $ conv' (plus ' ') x :: ss

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

splitted : KST -> Steps q KSz SK -> DFA q KSz SK
splitted x ss =
  spaced x $
    [ linecol' 1 6 ('-' >> newline >> mv30) x
    , newline' newline KDone
    ] ++ ss

val : KST -> Steps q KSz SK -> DFA q KSz SK
val x ss =
  splitted x $
    [ conv integer (onPrim . I . decimal)
    , read unquoted (onPrim . S)
    , copen' '"' InStr
    ] ++ ss

toplevel : KST -> DFA q KSz SK
toplevel x =
  val x
    [ conv (plus alphaNum >> '=') onKey
    , copen' '(' LStart
    ]

str : DFA q KSz SK
str =
  dfa
    [ read (plus $ dot && not '"' && not '-') (pushStr InStr)
    , cexpr "\"\"" (pushStr InStr "\"")
    , cexpr '-'    (pushStr InStr "-")
    , linecol' 1 7 ('-' >> newline >> mv30 >> ' ') InStr
    , linecol' 1 6 ('-' >> newline >> mv30)  InStr
    , ccloseStr '"' (onPrim . S)
    ]

--------------------------------------------------------------------------------
-- Parser
--------------------------------------------------------------------------------

kvTrans : Lex1 q KSz SK
kvTrans =
  lex1
    [ E KIni   $ dfa [cexpr' mv30 KeyVal.Entry]
    , E Entry     $ toplevel Entry
    , E KVal   $ toplevel KVal
    , E LVal   $ val LVal []
    , E LStart $ splitted LStart [conv size startList]
    , E LEnd   $ splitted LEnd [cclose ')' (pure Entry)]
    , E InStr    str
    ]

kvErr : Arr32 KSz (SK q -> F1 q (BoundedErr MolErr))
kvErr =
  arr32 KSz (unexpected [])
    [ E InStr  $ unclosedIfEOI "\"" []
    , E LStart $ unclosedIfEOI "(" []
    , E LVal   $ unclosedIfEOI "(" []
    , E LEnd   $ unclosedIfEOI "(" [")"]
    ]

kvEOI : KST -> SK q -> F1 q (Either (BoundedErr MolErr) (List KeyVal))
kvEOI sk s t =
  case sk == KDone || sk == Entry of
    False => arrFail SK kvErr sk s t
    True  => case getStack t of
      VS vs # t => Right (vs <>> []) # t
      _     # t => Right [] # t -- impossible

kv : P1 q (BoundedErr MolErr) KSz SK (List KeyVal)
kv = P KIni (init (VS [<])) kvTrans noChunk kvErr kvEOI

||| Parses V3000 key-value pairs from a (possibly multiline) bytestring.
export %inline
keyVals : ByteString -> Either (BoundedErr MolErr) (List KeyVal)
keyVals = runBytes kv

test : String -> IO ()
test s =
  either
    (putStrLn . interpolate)
    (traverse_ printLn)
    (parseString kv Virtual s)

ml : String
ml =
  """
  M  V30 FOO=12 BAR="quux" BAZ="this is a -
  M  V30 test" AND=(7 1 2 3 4 5   -
  M  V30 six "se=ven") im="not yet done"
  """

sup : String
sup =
  """
  M  V30 1 SUP 0 LABEL=a0 ATOMS=(1 1)\n
  """
