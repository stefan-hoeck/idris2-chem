module Text.Molfile.Parser

import Data.Array.Mutable
import Data.SortedMap as SM
import Data.Finite
import Syntax.T1
import Text.Molfile.Parser.KeyVal
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
    [ E H1       $ dfa [bytes (star dot >> newline) h1]
    , E H2       $ dfa [bytes (star dot >> newline) h2]
    , E H3       $ dfa [bytes (star dot >> newline) h3]
    , E Counts   $ dfa [mv30prefix v3000 CountsV3, bytes v2000 countsV2]
    , E SData    $ dfa sdata
    , E SDValue  $ dfa sdvalue
    , E EndMol   $ dfa sdata

    -- V2000
    , E Coords2  $ spaced [bytes coordinatesV2 coordsV2]
    , E Sym2     $ dfa $ valsN (fill 4 . (" "++) . dispIso) (setIso Chrg2) isos
    , E Chrg2    $ dfa [step zeroes atomV2, line 2 (sdigits 5) chargeV2]
    , E Bnd2     $ dfa [line 0 (sdigits 6) bond]
    , E Prop2    $ dfa prop2

    -- V3000
    , E CountsV3   $ spaced [step' "COUNTS" ACount]
    , E EmptyV3    $ dfa emptyEnd
    , E ACount     $ spaced [bytes (plus digit) newV3]
    , E BCount     $ spaced [bytes (plus digit) bondsV3]
    , E CountEnd   $ dfa [step' (dots >> newline >> beginV3 "ATOM") Atom3]
    -- Atoms V3000
    , E Atom3      $ dfa [step' mv30 Index3]
    , E Index3     $ spaced [bytes (plus digit) indexV3]
    , E Sym3       $ spaced (vals dispIso (setIso Coords3) isos)
    , E Coords3    $ spaced [bytes coordinatesV3 coordsV3]
    , E AAMap      $ dfa [step' (plus ' ' >> plus digit) Prop3]
    , E Prop3      $ spaced prop3
    , E AtomEnd    $ dfa [step (endV3 "ATOM") beginBondV3]
    -- Bonds V3000
    , E BondBegin  $ dfa [step' (beginV3 "BOND") Bnd3]
    , E Bnd3       $ dfa [bytes bondExprV3 bondV3]
    , E BndProp3   $ spaced bondProp3
    , E BondEnd    $ dfa [step' (endV3 "BOND") RestV3]
    , E SGroup     $ dfa sgroup
    , E RestV3     $ dfa rest3
    ]

ctabErr : Arr32 CSz (CSTCK q -> F1 q (BBErr MolErr))
ctabErr = arr32 CSz (unexpected []) []

ctabEOI : CST -> CSTCK q -> F1 q (Either (BBErr MolErr) (List Molfile))
ctabEOI st sk =
  case st == H1 || st == CDone of
    False => case st == EndMol of
      False => arrFail CSTCK ctabErr st sk
      True  => end >> getList sk.stack_ >>= pure . Right
    True  => getList sk.stack_ >>= pure . Right

||| A parser for CTab file formats. Can read V2000 and V3000 mol
||| and SD files. Suitable for streaming large amounts of data.
public export
ctab : P1 q (BBErr MolErr) (List Molfile)
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


test : String -> IO ()
test s =
  case readMol {es = [ParseError MolErr]} s of
    Left (Here x) => putStrLn (interpolate x)
    Right (MkMolfile _ _ _  (G s _) _) => putStrLn "\{show s} atoms parsed"

v3 : String
v3 =
  """



  00000999 V3000
  M  V30 BEGIN CTAB
  M  V30 COUNTS 1 0 1 0 0
  M  V30 BEGIN ATOM
  M  V30 1 H 0 0 0 0
  M  V30 END ATOM
  M  V30 BEGIN BOND
  M  V30 END BOND
  M  V30 BEGIN SGROUP
  M  V30 1 SUP 0 LABEL=a0 ATOMS=(1 1)
  M  V30 END SGROUP
  M  V30 END CTAB
  M  END
  """
