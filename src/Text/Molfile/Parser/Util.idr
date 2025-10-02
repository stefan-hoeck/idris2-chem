module Text.Molfile.Parser.Util

import Data.SortedMap as SM
import Data.Array.Mutable
import Data.Finite
import Syntax.T1
import Text.Molfile.Parser.Stack

%default total

||| Isotopes recognized directly by the parser.
|||
||| In addition to the regular element symbols, this includes "D" and "T"
||| for deuterium and tritium.
export
isos : List Isotope
isos = MkI H (Just 2) :: MkI H (Just 3) :: map (`MkI` Nothing) values

||| Isotope pretty printer.
export
dispIso : Isotope -> String
dispIso (MkI H (Just 2)) = "D"
dispIso (MkI H (Just 3)) = "T"
dispIso (MkI e _)        = symbol e

||| Converts the given byte string to a string, removing any trailing
||| end of line characters (`'\n'` and `'\r'`).
export
stringTillEOL : ByteString -> String
stringTillEOL = toString . dropWhileEnd isNL

--------------------------------------------------------------------------------
-- Expressions
--------------------------------------------------------------------------------

||| From a given string, generates a list of string by badding
||| it in all possible ways with spaces, so that each of them is
||| exactly `n` characters long.
|||
||| For instance, `fill 3 "C"` will return `["  C", " C ", "C  "]`.
export
fill : Nat -> String -> List String
fill n s = go [<] (n `minus` length s) 0
  where
    go : SnocList String -> Nat -> Nat -> List String
    go ss 0     j = ss <>> [s ++ replicate j ' ']
    go ss (S k) j =
      go (ss:< (replicate (S k) ' ' ++ s ++ replicate j ' ')) k (S j)

||| Expressions we recognize as line breaks.
export
newline : RExp True
newline = '\r' <|> '\n' <|> "\r\n"

||| A space or a decimal digit.
export
sdigit : RExp True
sdigit = ' ' <|> digit

||| An arbitrary number of spaces and zeroes, followed by a linebreak.
|||
||| If we find this, it typically means we can stop interpreting a
||| line of data and fill in default values (for instance, with V2000
||| atom and bond definitions).
export
zeroes : RExp True
zeroes = star (' ' <|> '0') >> newline

--------------------------------------------------------------------------------
-- State Transitions
--------------------------------------------------------------------------------

parameters {auto sk : CSTCK q}

  ||| Writes a custom error with proper bounds based on the given
  ||| `ByteString`.
  |||
  ||| The bounds are computed from the current position and the size
  ||| and offset of the bytestring, which is supposed to be a substring
  ||| of the one stored in the `bytes_` filed.
  export
  fail : ErrPair -> F1' q
  fail (BS l $ BV _ o2 _, x) = T1.do
    BS _ (BV _ o1 _) <- read1 (bytes sk)
    p                <- getPosition
    let ps := addCol (o2 `minus` o1) p
        pe := addCol l ps
    write1 sk.error_ (Just $ B (Custom x) $ BS ps pe)

  ||| Convenience alias for `fail p >> pure CErr`.
  export
  failErr : ErrPair -> F1 q CST
  failErr p = fail p >> pure CErr

  export %inline
  h1,h2,h3 : ByteString -> F1 q CST
  h1 bs = writeAs sk.h1 (cast bs) H2
  h2 bs = writeAs sk.h2 (cast bs) H3
  h3 bs = writeAs sk.h3 (cast bs) Counts

  ||| Modifies the current atom in the mol graph
  export
  modAtom : (MolAtom -> MolAtom) -> F1' q
  modAtom f = T1.do
    mg <- read1 sk.mgraph
    x  <- read1 mg.atom
    modify mg.graph x {label $= f}

  ||| Returns the current position in the bytestring
  ||| and increases it by the given number of bytes.
  export %inline
  inc : Nat -> F1 q Nat
  inc k = read1 sk.pos >>= \n => writeAs sk.pos (k+n) n

  ||| Converts the next `len` bytes of the recognized byte string
  ||| using the given convertion function.
  export
  read : (ByteString -> a) -> (len : Nat) -> F1 q a
  read f len = T1.do
    bs <- read1 sk.bytes_
    p  <- inc len
    pure (f $ substring p len bs)

  ||| Converts the remainder of the recognized byte string to a `String`,
  ||| trimming any newline characters from its end.
  export
  remString : F1 q String
  remString = T1.do
    p  <- read1 sk.pos
    bs <- read1 sk.bytes_
    pure (stringTillEOL $ drop p bs)

  ||| Finalizes the current molecule
  export
  end : F1 q CST
  end = T1.do
    h1   <- replace1 sk.h1 ""
    h2   <- replace1 sk.h2 ""
    h3   <- replace1 sk.h3 ""
    sds  <- getList sk.sdvals
    mg   <- read1 sk.mgraph
    grps <- replace1 sk.groups SM.empty
    lupdNodes mg.graph $ {label $= map (groupLbl grps)}
    g  <- Array.Core.unsafeFreeze mg.graph
    push1 sk.stack_ (MkMolfile h1 h2 h3 (G _ $ IG g) sds)
    pure H1

  sdheader : ByteString -> F1 q CST
  sdheader bs = writeAs sk.sdhead (readHeader bs) SDValue

  endSDValue : F1 q CST
  endSDValue = T1.do
    hd <- read1 sk.sdhead
    v  <- getStr
    push1 sk.sdvals (SD hd $ fromMaybe "" $ refineSDValue v)
    pure SData

||| Sets the isotope of the current atom
export
setIso : CST -> Isotope -> Step1 q CSz CSTCK
setIso x i = \(_ # t) => let _ # t := modAtom {elem := i} t in x # t

--------------------------------------------------------------------------------
-- Structure Data
--------------------------------------------------------------------------------

||| Transition steps for structure data header entries.
export
sdata : Steps q CSz CSTCK
sdata =
  [ newline ("$$$$" >> newline) end
  , cexpr  "$$$$" (ignore1 end >> pure CDone)
  , convline ( '>' >> star dot >> newline) sdheader
  ]

||| Transition steps for structure data value entries.
export
sdvalue : Steps q CSz CSTCK
sdvalue =
  [ newline newline endSDValue
  , convline (dots >> newline) (pushStr SDValue . stringTillEOL)
  ]
