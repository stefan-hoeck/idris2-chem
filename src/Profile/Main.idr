module Profile.Main

import Profile.Data.Refined
import Profile.Text.Molfile

main : IO ()
main = do
  Refined.profile
  Molfile.profile
