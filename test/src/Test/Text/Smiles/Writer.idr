module Test.Text.Smiles.Writer

import Text.Smiles.Writer
import Hedgehog


%default total

--------------------------------------------------------------------------------
--          Properties
--------------------------------------------------------------------------------

covering
propSmilesLVL1 : Property
propSmilesLVL1 = property1 $
  smilesRoundtrip "CC" === "CC"

-- propSmilesLVL1' : Property
-- propSmilesLVL1' = property $ smilesRoundtrip "CC" === "CC"

export covering
props : Group
props =
  MkGroup "Text.Smiles.Writer"
    [ ("propSmilesLVL1", propSmilesLVL1)
    ]


-- TODO Bei Roundtrip einmal nach und einmal vor roundtrip substrukturensuche machen und vergleichen
-- TODO substruktursuche -> anzahl nodes/edges vergleichen
-- indexed graph lib: src/data/query/subgraph -> fun query und in tests gibt es ein beispiel
-- wie sie benutzt wird
-- TODO smiles code generieren? siehe chem-generators/src/Test/Data/Graph/Generators.idr
