module Text.Molfile.SDF

import Data.Either
import Data.Linear.Traverse1
import Data.Refined.String
import Derive.Prelude
import Derive.Refined
import Text.Lex.Manual.Syntax
import Text.Molfile.Reader
import Text.Molfile.Reader.Types
import Text.Molfile.Reader.Util
import Text.Molfile.Types
import Text.Molfile.Writer

%default total
%language ElabReflection

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

public export
0 IsHeader : String -> Type
IsHeader = Len (<= 70) && Str (All $ AlphaNum || ('_' ===))

||| Header of a SDF data entry. This is put in angles (`<>`) in an SD file.
public export
record SDHeader where
  constructor SDH
  value : String
  {auto 0 prf : IsHeader value}

export %inline
Interpolation SDHeader where
  interpolate = value

namespace SDHeader
  %runElab derive "SDHeader" [Show,Eq,Ord,RefinedString]

||| Encodes a value header by replacing spaces with underscores and
||| dropping some other invalid characters such as angles.
export
encodeHeader : String -> Maybe SDHeader
encodeHeader = refineSDHeader . convert [<] . unpack
  where
    convert : SnocList Char -> List Char -> String
    convert sc [] = pack $ sc <>> []
    convert sc (' '::t) = convert (sc :< '_') t
    convert sc (h::t)   =
      if isAlphaNum h then convert (sc:<h) t else convert sc t

public export
0 IsValue : String -> Type
IsValue = Str (All Printable)

||| Value of an SDF data entry. This follows after the header (see
||| `SDHeader`) and may span across several lines, each of which must not
||| be longer than 200 characters.
public export
record SDValue where
  constructor SDV
  value : String
  {auto 0 prf : IsValue value}

export %inline
Interpolation SDValue where
  interpolate = value

namespace SDValue
  %runElab derive "SDValue" [Show,Eq,Ord,RefinedString]

||| A data entry in an SD file consisting of the data header and value.
public export
record StructureData where
  constructor SD
  header : SDHeader
  value  : SDValue

%runElab derive "StructureData" [Show,Eq]

||| Tries to convert a name-value pair to a piece of
||| SD-data.
|||
||| While the values is refined as it is, we try to encode the
||| header in such a way that it does not contain any invalid
||| characters.
export
encodeStructureData : (name,value : String) -> Maybe StructureData
encodeStructureData n v = [| SD (encodeHeader n) (refineSDValue v) |]

||| A single structure in an SD file consisting of a mol-file entry followed
||| by an arbitrary number of data entries.
public export
record SDFile' (h,t,c : Type) where
  constructor SDF
  mol : Molfile' h t c
  dat : List StructureData

%runElab derive "SDFile'" [Show,Eq]

public export
0 SDFile : Type
SDFile = SDFile' () () ()

public export
0 SDFileAT : Type
SDFileAT = SDFile' HCount AtomType ()

--------------------------------------------------------------------------------
-- Writing SD-files
--------------------------------------------------------------------------------

export %inline
sdfDelimiter : String
sdfDelimiter = "$$$$"

writeV : SDValue -> List String
writeV "" = [""]
writeV v  = (map pack . grouped 200 $ unpack v.value) ++ [""]

writeStructureData : StructureData -> List String
writeStructureData (SD h v) = "> <\{h}>" :: writeV v

writeSDFile : SDFile' h t c -> List String
writeSDFile (SDF (MkMolfile n i c g) ds) =
  molLines n i c g ++ (ds >>= writeStructureData) ++ [sdfDelimiter]

export
writeSDF : List (SDFile' h t c) -> String
writeSDF = unlines . (>>= writeSDFile)

--------------------------------------------------------------------------------
-- Reading SD-files
--------------------------------------------------------------------------------

0 SDParser : Type
SDParser =
     SnocList StructureData
  -> List (Nat,String)
  -> Either MolParseErr (List StructureData)

readH : SnocList Char -> Parser SDHeader
readH sc []       = Left EOI
readH sc ('>'::_) =
  let s := pack (sc <>> [])
   in ([],) <$> maybeToEither (EInvalid s) (refineSDHeader s)
readH sc (c::cs)  = readH (sc :< c) cs

header : Parser SDHeader
header []        = Left EOI
header ('>'::xs) =
  case break ('<' ==) xs of
    (_, '<'::t) => readH [<] t
    _           => Left $ EInvalid $ pack xs
header xs        = Left (EInvalid $ pack xs) 


value : SDHeader -> SnocList String -> SDParser

sdf : SDParser

value hd ss sv []          = Left $ MPE 0 EOI
value hd ss sv ((l,"")::t) =
  let str := fastConcat $ ss <>> []
   in case refineSDValue str of
        Nothing => Left $ MPE l (EInvalid str)
        Just v  => sdf (sv :< SD hd v) t
value hd ss sv (h::t)  = value hd (ss :< snd h) sv t

sdf sd []     = Right (sd <>> [])
sdf sd (h::t) = lineTok header h >>= \hd => value hd [<] sd t

readBlock : List (Nat,String) -> Either MolParseErr (Maybe SDFile)
readBlock [] = Right Nothing
readBlock ls = Prelude.do
  R ls2 mf <- readMolFrom ls
  vs       <- sdf [<] ls2
  pure . Just $ SDF mf vs

||| Reads the SD file entries from a string.
export
readSDF : Has MolParseErr es => String -> ChemRes es (List SDFile)
readSDF s =
  let blocks := forget $ split ((sdfDelimiter ==) . snd) (zipWithIndex $ lines s)
   in bimap inject catMaybes $ traverse readBlock blocks
