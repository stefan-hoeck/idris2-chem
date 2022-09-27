module Profile.Main

import Profile.Data.Refined
import Profile.Text.Molfile
import Profile.Text.Smiles
import Profile.Text.Zinc

main : IO ()
main = do
  Zinc.profile
  Refined.profile
  Molfile.profile
