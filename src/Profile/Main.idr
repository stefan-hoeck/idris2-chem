module Profile.Main

import Profile.Data.IntMap
import Profile.Data.Refined
import Profile.Text.Molfile
import Profile.Text.Smiles

main : IO ()
main = do
    Smiles.profile
--  IntMap.profile
--  Refined.profile
--  Molfile.profile
