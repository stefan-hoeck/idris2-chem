module Profile.Data.IntMap

import Data.IntMap as IM
import Data.SortedMap as SM
import Data.Nat
import Profile.Profiler

pairs : List (Key,Key)
pairs = map dup [0 .. 10000]

nonEmptySM : SortedMap k v -> Bool
nonEmptySM m = not $ null m

testFromList : () -> Bool
testFromList () =
  Just 1000 == lookup 1000 (IM.fromList pairs)

testFromListSM : () -> Bool
testFromListSM () =
  Just 1000 == lookup 1000 (SM.fromList pairs)

testLookup : IntMap Key -> () -> Bool
testLookup m = \_ => Just 1000 == lookup 1000 m

testInsert : IntMap Key -> () -> Bool
testInsert m = \_ => nonEmpty (insert 2000 2000 m)

testDelete : IntMap Key -> () -> Bool
testDelete m = \_ => nonEmpty (delete 1000 m)

testLookupSM : SortedMap Key Key -> () -> Bool
testLookupSM m = \_ => Just 1000 == lookup 1000 m

testInsertSM : SortedMap Key Key -> () -> Bool
testInsertSM m = \_ => nonEmptySM (insert 2000 2000 m)

testDeleteSM : SortedMap Key Key -> () -> Bool
testDeleteSM m = \_ => nonEmptySM (delete 1000 m)

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
     profileAndReport $
       MkTask "delete" (testDelete im) 100000 ItIsSucc
     profileAndReport $
       MkTask "deleteSM" (testDeleteSM sm) 100000 ItIsSucc
