module Profile.Text.Smiles

import Chem.Element
import Profile
import Text.FC
import Text.Smiles.Lexer
import Text.Smiles.Parser

mol : String
mol = "C[C@@H]1CCCN(C1)C(=O)[C@@H](C)Oc2ccccc2"

strychnine : String
strychnine = "O=C7N2c1ccccc1[C@@]64[C@@H]2[C@@H]3[C@@H](OC/C=C5\[C@@H]3C[C@@H]6N(CC4)C5)C7"

export
bench : Benchmark Void
bench = Group "Text.Smiles.Parse" [
    Single "mol1" (basic parse mol)
  , Single "strychnine" (basic parse strychnine)
  ]
