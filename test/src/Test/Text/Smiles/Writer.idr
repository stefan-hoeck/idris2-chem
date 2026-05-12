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

covering
propSmilesLVL2 : Property
propSmilesLVL2 = property1 $
  smilesRoundtrip "C12CC1C2" === "C12CC1C2"

covering
propSmilesLVL3 : Property
propSmilesLVL3 = property1 $
  smilesRoundtrip "C1C(C2C(C3C(C4C(C5C(C6C(C7C(C8C(C9C(C%10C(CC)C%10C)C9C)C8C)C7C)C6C)C5C)C4C)C3C)C2C)C1" === "C1C(C2C(C3C(C4C(C5C(C6C(C7C(C8C(C9C(C%10C(CC)C%10C)C9C)C8C)C7C)C6C)C5C)C4C)C3C)C2C)C1"

export covering
props : Group
props =
  MkGroup "Text.Smiles.Writer"
    [ ("propSmilesLVL1", propSmilesLVL1),
      ("propSmilesLVL2", propSmilesLVL2),
      ("propSmilesLVL3", propSmilesLVL3)
    ]


