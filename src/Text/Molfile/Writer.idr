module Text.Molfile.Writer

import Chem
import Data.Linear.Traverse1
import Data.String.Builder
import Syntax.T1
import Text.Molfile.Types
import Text.Molfile.Writer.Util
import Text.Molfile.Writer.V2000
import Text.Molfile.Writer.V3000

%default total

--------------------------------------------------------------------------------
-- Writing SD-files
--------------------------------------------------------------------------------

parameters {default V2000 version : MolVersion}

  export
  putMol : Builder q => (n,i,ct : MolLine) -> MolGraph' h t c -> F1' q
  putMol n i c (G 0 _) = pure ()
  putMol n i c g       = T1.do
    putTextLn n.value
    putTextLn i.value
    putTextLn c.value
    if version == V3000 then putMol3000 g else putMol2000 g
    putTextLn "M  END"

  export
  putSDF : Builder q => Molfile' h t c -> F1' q
  putSDF (MkMolfile n i c g ds) = T1.do
    putMol n i c g
    traverse1_ writeStructureData ds
    sdfDelimiter

  export %inline
  writeMolfile : Molfile' h t c -> String
  writeMolfile (MkMolfile n i c g _) = withBuilder $ putMol n i c g

  export %inline
  writeSDFile : Molfile' h t c -> String
  writeSDFile m = withBuilder $ putSDF m

  export %inline
  writeSDF : List (Molfile' h t c) -> String
  writeSDF ms = withBuilder $ traverse1_ putSDF ms
