module Profile.Main

import Profile.Data.Refined
import Profile.Text.Molfile
import Profile.Text.Smiles
import Profile.Text.Zinc
import Profile.Data.Isomorphism

main : IO ()
main = do
  Zinc.profile
  Refined.profile
  Molfile.profile
  Isomorphism.profile
