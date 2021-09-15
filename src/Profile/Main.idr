module Profile.Main

import Profile.Data.IntMap
import Profile.Data.Refined
import Profile.Text.Molfile

main : IO ()
main = do
    IntMap.profile
--  Refined.profile
--  Molfile.profile
