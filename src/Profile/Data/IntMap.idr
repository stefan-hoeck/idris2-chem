module Profile.Data.IntMap

import Data.BitMap as BM
import Data.IntMap as IM
import Data.SortedMap as SM
import Data.Nat
import Profile.Profiler

pairs : List (BM.Key,BM.Key)
pairs = map dup [0 .. 10000]

nonEmptySM : SortedMap k v -> Bool
nonEmptySM m = not $ null m

testFromList : () -> Bool
testFromList () =
  Just 1000 == lookup 1000 (IM.fromList pairs)

testFromListBM : () -> Bool
testFromListBM () =
  Just 1000 == lookup 1000 (BM.fromList pairs)

testFromListSM : () -> Bool
testFromListSM () =
  Just 1000 == lookup 1000 (SM.fromList pairs)

testLookup : IntMap BM.Key -> () -> Bool
testLookup m = \_ => Just 1000 == lookup 1000 m

testLookupBM : BitMap BM.Key -> () -> Bool
testLookupBM m = \_ => Just 1000 == lookup 1000 m

testLookupSM : SortedMap BM.Key BM.Key -> () -> Bool
testLookupSM m = \_ => Just 1000 == lookup 1000 m

testInsert : IntMap BM.Key -> () -> Bool
testInsert m = \_ => nonEmpty (insert 2000 2000 m)

testInsertBM : BitMap BM.Key -> () -> Bool
testInsertBM m = \_ => nonEmpty (insert 2000 2000 m)

testInsertSM : SortedMap BM.Key BM.Key -> () -> Bool
testInsertSM m = \_ => nonEmptySM (insert 2000 2000 m)

testDelete : IntMap BM.Key -> () -> Bool
testDelete m = \_ => nonEmpty (delete 1000 m)

testDeleteBM : BitMap BM.Key -> () -> Bool
testDeleteBM m = \_ => nonEmpty (delete 1000 m)

testDeleteSM : SortedMap BM.Key BM.Key -> () -> Bool
testDeleteSM m = \_ => nonEmptySM (delete 1000 m)

export
profile : IO ()
profile =
  let im = IM.fromList (map dup [0 .. 1023])
      sm = SM.fromList (map dup [0 .. 1023])
      bm = BM.fromList (map dup [0 .. 1023])
   in do
     profileAndReport $
       MkTask "fromList" testFromList 1000 ItIsSucc
     profileAndReport $
       MkTask "fromListBM" testFromListBM 1000 ItIsSucc
     profileAndReport $
       MkTask "fromListSM" testFromListSM 1000 ItIsSucc
     profileAndReport $
       MkTask "lookup" (testLookup im) 100000 ItIsSucc
     profileAndReport $
       MkTask "lookupBM" (testLookupBM bm) 100000 ItIsSucc
     profileAndReport $
       MkTask "lookupSM" (testLookupSM sm) 100000 ItIsSucc
     profileAndReport $
       MkTask "insert" (testInsert im) 100000 ItIsSucc
     profileAndReport $
       MkTask "insertBM" (testInsertBM bm) 100000 ItIsSucc
     profileAndReport $
       MkTask "insertSM" (testInsertSM sm) 100000 ItIsSucc
     profileAndReport $
       MkTask "delete" (testDelete im) 100000 ItIsSucc
     profileAndReport $
       MkTask "deleteBM" (testDeleteBM bm) 100000 ItIsSucc
     profileAndReport $
       MkTask "deleteSM" (testDeleteSM sm) 100000 ItIsSucc
