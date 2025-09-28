module Text.Molfile.SData

import Data.ByteString
import Derive.Prelude
import Derive.Refined
import public Data.Nat
import public Data.String
import public Data.Refined
import public Data.Refined.Integer
import public Data.Refined.String

%default total
%language ElabReflection

public export
IsHeaderChar : Char -> Bool
IsHeaderChar '>' = False
IsHeaderChar '<' = False
IsHeaderChar c   = not (isControl c)

public export
0 IsHeader : String -> Type
IsHeader = Len (<= 70) && Str (All $ Holds IsHeaderChar)

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

export
readHeader : ByteString -> SDHeader
readHeader bs =
  case break (60 ==) bs of -- '<'
    (_, BS 0 _)      => ""
    (_, BS (S k) bv) =>
      fromMaybe "" $ refineSDHeader (toString . BV.takeWhile (62 /=) $ tail bv)

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
