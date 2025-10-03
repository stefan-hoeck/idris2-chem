module Text.Molfile.Writer.Util

import Data.SortedMap
import Text.Molfile.Types

%default total

||| Isotope pretty printer.
export
dispIso : Isotope -> String
dispIso (MkI H (Just 2)) = "D"
dispIso (MkI H (Just 3)) = "T"
dispIso (MkI e _)        = symbol e

||| Radical pretty printer
export
dispRadical : Radical -> String
dispRadical NoRadical = "0"
dispRadical Singlet   = "1"
dispRadical Doublet   = "2"
dispRadical Triplet   = "3"

export %inline
sdfDelimiter : String
sdfDelimiter = "$$$$"

writeV : SDValue -> List String
writeV "" = [""]
writeV v  = (map pack . grouped 200 $ unpack v.value) ++ [""]

export
writeStructureData : StructureData -> List String
writeStructureData (SD h v) = "> <\{h}>" :: writeV v

public export
0 GroupMap : Nat -> Type
GroupMap k = SortedMap Nat (String, SnocList $ Fin k)

export
appendLbl : Maybe AtomGroup -> Fin k -> GroupMap k -> GroupMap k
appendLbl Nothing  _       m = m
appendLbl (Just $ G n l) x m =
  case lookup n m of
    Just (l,sx) => insert n (l, sx :< x) m
    Nothing     => insert n (l, [<x]) m
