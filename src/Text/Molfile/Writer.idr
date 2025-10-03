module Text.Molfile.Writer

import Chem
import Data.String
import Text.Molfile.Types
import Text.Molfile.Writer.Util
import Text.Molfile.Writer.V2000
import Text.Molfile.Writer.V3000

%default total

--------------------------------------------------------------------------------
-- Writing SD-files
--------------------------------------------------------------------------------

parameters {default V2000 version : MolVersion}

  export %inline
  molLines : (name, info, comment : MolLine) -> MolGraph' h t c -> List String
  molLines =
    case version of
      V2000 => molLines2000
      V3000 => molLines3000

  export %inline
  writeMolfile : Molfile' h t c -> String
  writeMolfile (MkMolfile n i c g _) = unlines $ molLines n i c g

  export
  writeSDFile : Molfile' h t c -> List String
  writeSDFile (MkMolfile n i c g ds) =
    molLines n i c g ++ (ds >>= writeStructureData) ++ [sdfDelimiter]

  export
  writeSDF : List (Molfile' h t c) -> String
  writeSDF = unlines . (>>= writeSDFile)
