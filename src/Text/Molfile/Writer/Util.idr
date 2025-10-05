module Text.Molfile.Writer.Util

import Data.Linear.Traverse1
import Data.SortedMap
import Syntax.T1
import Data.String.Builder
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

parameters {auto b : Builder q}

  writeV : SDValue -> F1' q
  writeV "" = linebreak
  writeV v  = T1.do
    traverse1_ putCharsLn (grouped 200 $ unpack v.value)
    linebreak

  export
  writeStructureData : StructureData -> F1' q
  writeStructureData (SD h v) = putTextLn "> <\{h}>" >> writeV v

  export %inline
  sdfDelimiter : F1' q
  sdfDelimiter = putTextLn "$$$$"

public export
0 GroupMap : Type
GroupMap = SortedMap Nat (String, SnocList Nat)

export
appendLbl : Fin k -> Maybe AtomGroup -> GroupMap -> GroupMap
appendLbl _ Nothing        m = m
appendLbl x (Just $ G n l) m =
  case lookup n m of
    Just (l,sx) => insert n (l, sx :< S (cast x)) m
    Nothing     => insert n (l, [<S (cast x)]) m
