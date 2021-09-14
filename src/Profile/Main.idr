module Profile.Main

import Data.Nat
import Data.Refined
import Profile.Profiler

allUnpack : (Char -> Bool) -> String -> Bool
allUnpack f s = all f $ unpack s

testAllUnpack : () -> Bool
testAllUnpack () =
  let str = "The quick brown fox and all that bullshit"
   in allUnpack isPrintableLatin str

testAllStrM : () -> Bool
testAllStrM () =
  let str = "The quick brown fox and all that bullshit"
   in all isPrintableLatin str

main : IO ()
main = do
  profileAndReport $
    MkTask "allUnpack" testAllUnpack 5000000 ItIsSucc
  profileAndReport $
    MkTask "all with strM" testAllStrM 5000000 ItIsSucc
