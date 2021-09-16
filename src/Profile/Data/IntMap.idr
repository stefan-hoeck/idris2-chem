module Profile.Data.IntMap

import Data.IntMap as IM
import Data.SortedMap as SM
import Data.Nat
import Profile.Profiler

pairs : List (Bits32,Bits32)
pairs = map dup [0 .. 10000]

nonEmptySM : SortedMap k v -> Bool
nonEmptySM m = not $ null m

testFromList : () -> Bool
testFromList () =
  Just 1000 == lookup 1000 (IM.fromList pairs)

testFromListSM : () -> Bool
testFromListSM () =
  Just 1000 == lookup 1000 (SM.fromList pairs)

testLookup : IntMap Bits32 -> () -> Bool
testLookup m = \_ => Just 1000 == lookup 1000 m

testInsert : IntMap Bits32 -> () -> Bool
testInsert m = \_ => nonEmpty (insert 2000 2000 m)

testLookupSM : SortedMap Bits32 Bits32 -> () -> Bool
testLookupSM m = \_ => Just 1000 == lookup 1000 m

testInsertSM : SortedMap Bits32 Bits32 -> () -> Bool
testInsertSM m = \_ => nonEmptySM (insert 2000 2000 m)

export
profile : IO ()
profile = 
  let im = IM.fromList (map dup [0 .. 1023])
      sm = SM.fromList (map dup [0 .. 1023])
   in do
     profileAndReport $
       MkTask "fromList" testFromList 1000 ItIsSucc
     profileAndReport $
       MkTask "fromListSM" testFromListSM 1000 ItIsSucc
     profileAndReport $
       MkTask "lookup" (testLookup im) 100000 ItIsSucc
     profileAndReport $
       MkTask "lookupSM" (testLookupSM sm) 100000 ItIsSucc
     profileAndReport $
       MkTask "insert" (testInsert im) 100000 ItIsSucc
     profileAndReport $
       MkTask "insertSM" (testInsertSM sm) 100000 ItIsSucc
