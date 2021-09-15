module Profile.Data.IntMap

import Data.IntMap as IM
import Data.SortedMap as SM
import Data.Nat
import Profile.Profiler

pairs : List (Bits32,Bits32)
pairs = map dup [0 .. 300]

nonEmpty : IntMap a -> Bool
nonEmpty Empty = False
nonEmpty _     = True

nonEmptySM : SortedMap k v -> Bool
nonEmptySM m = not $ null m

testFromList : () -> Bool
testFromList () =
  Just 127 == lookup 127 (IM.fromList pairs)

testFromListSM : () -> Bool
testFromListSM () =
  Just 127 == lookup 127 (SM.fromList pairs)

testLookup : IntMap Bits32 -> () -> Bool
testLookup m = \_ => Just 127 == lookup 127 m

testInsert : IntMap Bits32 -> () -> Bool
testInsert m = \_ => nonEmpty (insert 200 200 m)

testLookupSM : SortedMap Bits32 Bits32 -> () -> Bool
testLookupSM m = \_ => Just 127 == lookup 127 m

testInsertSM : SortedMap Bits32 Bits32 -> () -> Bool
testInsertSM m = \_ => nonEmptySM (insert 200 200 m)

export
profile : IO ()
profile = 
  let im = IM.fromList (map dup [0 .. 1000])
      sm = SM.fromList (map dup [0 .. 1000])
   in do
     profileAndReport $
       MkTask "fromList" testFromList 1000 ItIsSucc
     profileAndReport $
       MkTask "fromListSM" testFromListSM 1000 ItIsSucc
     profileAndReport $
       MkTask "lookup" (testLookup im) 10000000 ItIsSucc
     profileAndReport $
       MkTask "lookupSM" (testLookupSM sm) 10000000 ItIsSucc
     profileAndReport $
       MkTask "insert" (testInsert im) 10000000 ItIsSucc
     profileAndReport $
       MkTask "insertSM" (testInsertSM sm) 10000000 ItIsSucc
