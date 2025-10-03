module Text.Molfile.Parser

import Data.Array.Mutable
import Data.SortedMap as SM
import Data.Finite
import Syntax.T1
import Text.Molfile.Parser.Util
import Text.Molfile.Parser.V2000
import Text.Molfile.Parser.V3000
import Text.Molfile.Writer.Util

import public Text.Molfile.Parser.Stack

%default total

--------------------------------------------------------------------------------
-- Parser
--------------------------------------------------------------------------------

ctabTrans : Lex1 q CSz CSTCK
ctabTrans =
  lex1
    [ E H1       $ dfa [convline (star dot >> newline) h1]
    , E H2       $ dfa [convline (star dot >> newline) h2]
    , E H3       $ dfa [convline (star dot >> newline) h3]
    , E Counts   $ dfa [mv30prefix 2 v3000 CountsV3, convline v2000 countsV2]
    , E SData    $ dfa sdata
    , E SDValue  $ dfa sdvalue
    , E EndMol   $ dfa sdata

    -- V2000
    , E Coords2  $ spaced Coords2 [conv coordinatesV2 coordsV2]
    , E Sym2     $ dfa $ valsN (fill 4 . (" "++) . dispIso) (setIso Chrg2) isos
    , E Chrg2    $ dfa [newline zeroes atomV2, line 2 (sdigits 5) chargeV2]
    , E Bnd2     $ dfa [line 0 (sdigits 6) bond]
    , E Prop2    $ dfa prop2

    -- V3000
    , E CountsV3   $ spaced CountsV3 [cexpr' "COUNTS" ACount]
    , E EmptyV3    $ dfa emptyEnd
    , E ACount     $ spaced ACount [conv (plus digit) newV3]
    , E BCount     $ spaced BCount [conv (plus digit) bondsV3]
    , E CountEnd   $ dfa [newlines' 2 (dots >> newline >> beginV3 "ATOM") Atom3]
    -- Atoms V3000
    , E Atom3      $ dfa [cexpr' mv30 Index3]
    , E Index3     $ spaced Index3 [conv (plus digit) indexV3]
    , E Sym3       $ spaced Sym3 (vals dispIso (setIso Coords3) isos)
    , E Coords3    $ spaced Coords3 [conv coordinatesV3 coordsV3]
    , E AAMap      $ dfa [conv' (plus ' ' >> plus digit) Prop3]
    , E Prop3      $ spaced Prop3 prop3
    , E AtomEnd    $ dfa [newline (endV3 "ATOM") beginBondV3]
    -- Bonds V3000
    , E BondBegin  $ dfa [newline' (beginV3 "BOND") Bnd3]
    , E Bnd3       $ dfa [conv bondExprV3 bondV3]
    , E BndProp3   $ spaced BndProp3 bondProp3
    , E BondEnd    $ dfa [newline' (endV3 "BOND") RestV3]
    , E RestV3     $ dfa rest3
    ]

ctabErr : Arr32 CSz (CSTCK q -> F1 q (BoundedErr MolErr))
ctabErr = arr32 CSz (unexpected []) []

ctabEOI : CST -> CSTCK q -> F1 q (Either (BoundedErr MolErr) (List Molfile))
ctabEOI st sk =
  case st == H1 || st == CDone of
    False => case st == EndMol of
      False => arrFail CSTCK ctabErr st sk
      True  => end >> getList sk.stack_ >>= pure . Right
    True  => getList sk.stack_ >>= pure . Right

||| A parser for CTab file formats. Can read V2000 and V3000 mol
||| and SD files. Suitable for streaming large amounts of data.
export
ctab : P1 q (BoundedErr MolErr) CSz CSTCK (List Molfile)
ctab = P H1 init ctabTrans snocChunk ctabErr ctabEOI

parameters {auto has : Has (ParseError MolErr) es}

  ||| Reads a single `Molfile` entry from a string.
  |||
  ||| The entry can be either in V2000 or V3000 format or a mixture of both.
  |||
  ||| Accepts strings that end with an option SD block
  ||| and optional SD delimiter (`"$$$$"`).
  export
  readMolFrom : Origin -> String -> ChemRes es Molfile
  readMolFrom o s =
    case parseString ctab o s of
      Left x    => Left $ inject x
      Right []  => Right (MkMolfile "" "" "" (G 0 empty) [])
      Right [x] => Right x
      Right _   =>
        Left (inject $ toParseError o s (B (Custom MEntries) NoBounds))

  ||| Convenience alias for `readMolFrom Virtual`.
  export %inline
  readMol : String -> ChemRes es Molfile
  readMol = readMolFrom Virtual

  ||| Reads a list of SD entries from a string.
  |||
  ||| The entries can be either in V2000 or V3000 format or a mixture of both.
  export %inline
  readSDFFrom : Origin -> String -> ChemRes es (List Molfile)
  readSDFFrom o = mapFst inject . parseString ctab o

  ||| Convenience alias for `readSDFFrom Virtual`.
  export %inline
  readSDF : String -> ChemRes es (List Molfile)
  readSDF = readSDFFrom Virtual
